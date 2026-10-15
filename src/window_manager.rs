//! Native Windows workspace and tiling manager.
//!
//! This module deliberately talks to Win32 directly. It owns workspace membership,
//! reacts to accessibility window events, lays out top-level application windows,
//! and publishes the compact state consumed by the bar.

use super::{
    AppEntry, TilingDirection, WindowManagerCommand, WindowManagerUpdate, WmConfig, WorkspaceEntry,
    WorkspacesState, is_shell_surface_title,
};
#[cfg(target_os = "windows")]
use super::SEARCH_INPUT_ACTIVE;
use eframe::egui::Context;
use std::{
    collections::{BTreeSet, HashMap, HashSet},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc::{self, Receiver, Sender},
        Mutex, OnceLock,
    },
    thread,
    time::{Duration, Instant},
};

#[cfg(target_os = "windows")]
use std::ffi::c_void;

/// Height, in pixels, of the bar's reserved strip at the top of its monitor.
/// Kept as a single constant since both the workspace-area reservation and
/// the bar-overlap/fullscreen detection need to agree on it.
#[cfg(target_os = "windows")]
const BAR_HEIGHT: i32 = 41;

#[cfg(target_os = "windows")]
fn spawn_unelevated_explorer() -> Result<(), String> {
    use windows::{
        Win32::{
            Foundation::CloseHandle,
            System::Threading::{
                CreateProcessW, DeleteProcThreadAttributeList, EXTENDED_STARTUPINFO_PRESENT,
                InitializeProcThreadAttributeList, LPPROC_THREAD_ATTRIBUTE_LIST, OpenProcess,
                PROCESS_CREATE_PROCESS, PROCESS_INFORMATION, STARTUPINFOEXW,
                UpdateProcThreadAttribute,
            },
            UI::WindowsAndMessaging::{GetShellWindow, GetWindowThreadProcessId},
        },
        core::{PCWSTR, PWSTR},
    };
    const PROC_THREAD_ATTRIBUTE_PARENT_PROCESS: usize = 0x0002_0000;

    unsafe {
        let shell = GetShellWindow();
        if shell.is_invalid() {
            return Err("no shell window".into());
        }
        let mut pid = 0_u32;
        GetWindowThreadProcessId(shell, Some(&mut pid));
        if pid == 0 {
            return Err("no shell process".into());
        }
        // A child created with the shell as its parent process inherits the
        // shell's (non-elevated) token, exactly like a taskbar launch.
        let parent = OpenProcess(PROCESS_CREATE_PROCESS, false, pid)
            .map_err(|error| format!("OpenProcess: {error}"))?;

        let mut size = 0_usize;
        let _ = InitializeProcThreadAttributeList(LPPROC_THREAD_ATTRIBUTE_LIST::default(), 1, 0, &mut size);
        let mut buffer = vec![0_u8; size];
        let attributes = LPPROC_THREAD_ATTRIBUTE_LIST(buffer.as_mut_ptr().cast());
        if let Err(error) = InitializeProcThreadAttributeList(attributes, 1, 0, &mut size) {
            let _ = CloseHandle(parent);
            return Err(format!("InitializeProcThreadAttributeList: {error}"));
        }
        let updated = UpdateProcThreadAttribute(
            attributes,
            0,
            PROC_THREAD_ATTRIBUTE_PARENT_PROCESS,
            Some((&parent as *const _) as *const std::ffi::c_void),
            std::mem::size_of_val(&parent),
            None,
            None,
        );
        if let Err(error) = updated {
            DeleteProcThreadAttributeList(attributes);
            let _ = CloseHandle(parent);
            return Err(format!("UpdateProcThreadAttribute: {error}"));
        }

        let windir = std::env::var("WINDIR").unwrap_or_else(|_| "C:\\Windows".into());
        let exe = format!("{windir}\\explorer.exe");
        let application = exe.encode_utf16().chain(std::iter::once(0)).collect::<Vec<u16>>();
        let mut command_line = format!("\"{exe}\"")
            .encode_utf16()
            .chain(std::iter::once(0))
            .collect::<Vec<u16>>();
        let mut startup = STARTUPINFOEXW::default();
        startup.StartupInfo.cb = std::mem::size_of::<STARTUPINFOEXW>() as u32;
        startup.lpAttributeList = attributes;
        let mut information = PROCESS_INFORMATION::default();
        let created = CreateProcessW(
            PCWSTR(application.as_ptr()),
            PWSTR(command_line.as_mut_ptr()),
            None,
            None,
            false,
            EXTENDED_STARTUPINFO_PRESENT,
            None,
            PCWSTR::null(),
            &startup.StartupInfo,
            &mut information,
        );
        DeleteProcThreadAttributeList(attributes);
        let _ = CloseHandle(parent);
        created.map_err(|error| format!("CreateProcessW: {error}"))?;
        let _ = CloseHandle(information.hProcess);
        let _ = CloseHandle(information.hThread);
    }
    Ok(())
}

#[derive(Clone, Debug)]
struct ManagedWindow {
    handle: isize,
    title: String,
    process_name: String,
    #[cfg(target_os = "windows")]
    class_name: String,
    #[cfg(target_os = "windows")]
    owner: Option<isize>,
    #[cfg(target_os = "windows")]
    original_rect: LayoutRect,
    #[cfg(target_os = "windows")]
    transient: bool,
    workspace: usize,
    floating: bool,
    fullscreen_restore: Option<FullscreenRestore>,
    /// Set to the window's original workspace while it is being auto-handled
    /// as a native (OS-level) maximize: moved to its own workspace (or kept in
    /// place if it already had none) while the bar auto-hides. Cleared when
    /// the window is restored.
    maximize_restore: Option<usize>,
    /// Distinguishes a real Win32 maximize from an app-controlled borderless
    /// fullscreen window. Frameless Electron windows can match both shapes,
    /// but their restore button must be governed by `IsZoomed` alone.
    native_maximized: bool,
}

#[cfg(target_os = "windows")]
impl ManagedWindow {
    fn persistence_key(&self) -> String {
        let process = self.process_name.trim().to_ascii_lowercase();
        let class = self.class_name.trim().to_ascii_lowercase();
        if self.owner.is_some() {
            let title = self.title.split_whitespace().collect::<Vec<_>>().join(" ").to_ascii_lowercase();
            format!("{process}|dialog|{class}|{title}")
        } else if self.transient {
            let title = self.title.split_whitespace().collect::<Vec<_>>().join(" ").to_ascii_lowercase();
            format!("{process}|transient|{class}|{title}")
        } else {
            format!("{process}|main|{class}")
        }
    }
}

#[derive(Clone, Debug)]
struct FullscreenRestore {
    rect: (i32, i32, i32, i32),
    style: i32,
}

#[cfg(target_os = "windows")]
#[derive(Clone, Debug)]
enum LayoutNode {
    Leaf(isize),
    Split {
        direction: TilingDirection,
        ratio: f32,
        first: Box<LayoutNode>,
        second: Box<LayoutNode>,
    },
}

#[cfg(target_os = "windows")]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct LayoutRect {
    left: i32,
    top: i32,
    right: i32,
    bottom: i32,
}

#[cfg(target_os = "windows")]
impl LayoutNode {
    fn contains(&self, handle: isize) -> bool {
        match self {
            Self::Leaf(candidate) => *candidate == handle,
            Self::Split { first, second, .. } => {
                first.contains(handle) || second.contains(handle)
            }
        }
    }

    fn leaves(&self, output: &mut Vec<isize>) {
        match self {
            Self::Leaf(handle) => output.push(*handle),
            Self::Split { first, second, .. } => {
                first.leaves(output);
                second.leaves(output);
            }
        }
    }

    fn insert_beside(
        &mut self,
        target: isize,
        handle: isize,
        direction: TilingDirection,
        after: bool,
    ) -> bool {
        match self {
            Self::Leaf(candidate) if *candidate == target => {
                let previous = std::mem::replace(self, Self::Leaf(handle));
                let inserted = Self::Leaf(handle);
                let (first, second) = if after {
                    (previous, inserted)
                } else {
                    (inserted, previous)
                };
                *self = Self::Split {
                    direction,
                    ratio: 0.5,
                    first: Box::new(first),
                    second: Box::new(second),
                };
                true
            }
            Self::Leaf(_) => false,
            Self::Split { first, second, .. } => {
                first.insert_beside(target, handle, direction, after)
                    || second.insert_beside(target, handle, direction, after)
            }
        }
    }

    fn remove(self, handle: isize) -> Option<Self> {
        match self {
            Self::Leaf(candidate) => (candidate != handle).then_some(Self::Leaf(candidate)),
            Self::Split {
                direction,
                ratio,
                first,
                second,
            } => {
                let first = first.remove(handle);
                let second = second.remove(handle);
                match (first, second) {
                    (Some(first), Some(second)) => Some(Self::Split {
                        direction,
                        ratio,
                        first: Box::new(first),
                        second: Box::new(second),
                    }),
                    (Some(remaining), None) | (None, Some(remaining)) => Some(remaining),
                    (None, None) => None,
                }
            }
        }
    }

    fn replace_leaf(&mut self, from: isize, to: isize) -> bool {
        match self {
            Self::Leaf(handle) if *handle == from => {
                *handle = to;
                true
            }
            Self::Leaf(_) => false,
            Self::Split { first, second, .. } => {
                first.replace_leaf(from, to) || second.replace_leaf(from, to)
            }
        }
    }

    fn resize_for(
        &mut self,
        handle: isize,
        direction: TilingDirection,
        delta: f32,
    ) -> bool {
        let Self::Split {
            direction: split_direction,
            ratio,
            first,
            second,
        } = self
        else {
            return false;
        };
        let in_first = first.contains(handle);
        let in_second = second.contains(handle);
        if !in_first && !in_second {
            return false;
        }
        let child_resized = if in_first {
            first.resize_for(handle, direction, delta)
        } else {
            second.resize_for(handle, direction, delta)
        };
        if child_resized {
            return true;
        }
        if *split_direction == direction {
            let previous = *ratio;
            *ratio = (*ratio + if in_first { delta } else { -delta }).clamp(0.1, 0.9);
            (*ratio - previous).abs() > f32::EPSILON
        } else {
            false
        }
    }

    /// Moves the nearest matching split boundary in the requested screen
    /// direction. Unlike `resize_for`, the sign is not inverted for a window
    /// in the second child: Right always moves the divider right and Down
    /// always moves it down, regardless of which side owns focus.
    fn move_boundary_for(
        &mut self,
        handle: isize,
        direction: TilingDirection,
        delta: f32,
    ) -> bool {
        let Self::Split {
            direction: split_direction,
            ratio,
            first,
            second,
        } = self
        else {
            return false;
        };
        let in_first = first.contains(handle);
        let in_second = second.contains(handle);
        if !in_first && !in_second {
            return false;
        }
        let child_resized = if in_first {
            first.move_boundary_for(handle, direction, delta)
        } else {
            second.move_boundary_for(handle, direction, delta)
        };
        if child_resized {
            return true;
        }
        if *split_direction != direction {
            return false;
        }
        let previous = *ratio;
        *ratio = (*ratio + delta).clamp(0.1, 0.9);
        (*ratio - previous).abs() > f32::EPSILON
    }

    fn rects(&self, rect: LayoutRect, gap: i32, output: &mut Vec<(isize, LayoutRect)>) {
        match self {
            Self::Leaf(handle) => output.push((*handle, rect)),
            Self::Split {
                direction,
                ratio,
                first,
                second,
            } => match direction {
                TilingDirection::Horizontal => {
                    let split = rect.left
                        + ((rect.right - rect.left) as f32 * ratio).round() as i32;
                    first.rects(
                        LayoutRect {
                            right: split - gap / 2,
                            ..rect
                        },
                        gap,
                        output,
                    );
                    second.rects(
                        LayoutRect {
                            left: split + (gap + 1) / 2,
                            ..rect
                        },
                        gap,
                        output,
                    );
                }
                TilingDirection::Vertical => {
                    let split = rect.top
                        + ((rect.bottom - rect.top) as f32 * ratio).round() as i32;
                    first.rects(
                        LayoutRect {
                            bottom: split - gap / 2,
                            ..rect
                        },
                        gap,
                        output,
                    );
                    second.rects(
                        LayoutRect {
                            top: split + (gap + 1) / 2,
                            ..rect
                        },
                        gap,
                        output,
                    );
                }
            },
        }
    }
}

#[cfg(target_os = "windows")]
static WINDOW_EVENT_DIRTY: AtomicBool = AtomicBool::new(true);

#[cfg(target_os = "windows")]
static WINDOW_EVENTS: OnceLock<Mutex<Vec<(u32, isize)>>> = OnceLock::new();

#[cfg(target_os = "windows")]
#[derive(Clone, Debug)]
struct SnapTarget {
    target: isize,
    direction: TilingDirection,
    after: bool,
    changes_layout: bool,
    preview: LayoutRect,
    placements: Vec<(isize, LayoutRect)>,
}

pub(super) fn spawn(
    ctx: Context,
    config: WmConfig,
) -> (
    Sender<WindowManagerCommand>,
    Receiver<WindowManagerUpdate>,
    Arc<AtomicBool>,
) {
    let (command_sender, command_receiver) = mpsc::channel();
    let (update_sender, update_receiver) = mpsc::channel();
    let running = Arc::new(AtomicBool::new(true));
    let worker_running = Arc::clone(&running);

    #[cfg(target_os = "windows")]
    let _ = thread::Builder::new()
        .name("overbar-window-manager".into())
        .spawn(move || run_windows_manager(ctx, command_receiver, update_sender, worker_running, config));

    #[cfg(not(target_os = "windows"))]
    {
        let _ = (ctx, command_receiver, update_sender, worker_running);
    }

    (command_sender, update_receiver, running)
}

#[cfg(target_os = "windows")]
struct Manager {
    windows: HashMap<isize, ManagedWindow>,
    active_workspace: usize,
    recent_workspace: usize,
    direction: TilingDirection,
    focused: Option<isize>,
    last_focused: HashMap<usize, isize>,
    last_foreground_event: Option<(isize, Instant)>,
    pending_workspace_focus: Option<(usize, isize, Instant)>,
    last_focus_retry: Instant,
    last_workspace_departure: Option<(usize, Instant)>,
    workspace_switch_guard: Option<(usize, Instant)>,
    last_explorer_relaunch: Instant,
    layouts: HashMap<usize, LayoutNode>,
    workspace_monitors: HashMap<usize, isize>,
    insertion_directions: HashMap<isize, TilingDirection>,
    minimum_sizes: HashMap<isize, (i32, i32)>,
    /// Largest app-enforced outer size seen and consecutive observation count.
    pending_growth: HashMap<isize, (i32, i32, u8)>,
    dragging: Option<isize>,
    snap_target: Option<SnapTarget>,
    parked_rects: HashMap<isize, LayoutRect>,
    paused: bool,
    resize_mode: bool,
    closing: HashSet<isize>,
    taskbar_hidden: HashSet<isize>,
    /// Handles parked (hidden off-screen) by the most recent `focus_workspace`
    /// transition, with the instant each was parked. Windows can emit a
    /// spurious `EVENT_SYSTEM_FOREGROUND` for a window immediately after it is
    /// moved off-screen with `SetWindowPos`, even with `SWP_NOACTIVATE` set.
    /// Without this guard that spurious event reached
    /// `redirect_hidden_app_activation`, which (for Explorer) misread it as a
    /// genuine taskbar click and launched an unwanted new `explorer.exe`.
    recently_parked: HashMap<isize, Instant>,
    last_local_foreground: Option<(isize, Instant)>,
    /// Set when a new Explorer window has been spawned to satisfy a hidden-app
    /// activation, cleared once `refresh()` discovers that window. Without
    /// this, a parked Explorer HWND that keeps re-reporting itself as the OS
    /// foreground window (observed to happen repeatedly, seconds apart, with
    /// no further user click) would otherwise spawn a brand new `explorer.exe`
    /// every time, since the 750ms cooldown alone doesn't survive gaps that
    /// long.
    pending_explorer_relaunch: Option<usize>,
    last_published: Option<WorkspacesState>,
    config: WmConfig,
    bar_hidden: bool,
}

#[cfg(target_os = "windows")]
impl Manager {
    fn new(config: WmConfig) -> Self {
        Self {
            windows: HashMap::new(),
            active_workspace: 1,
            recent_workspace: 1,
            direction: TilingDirection::Horizontal,
            focused: None,
            last_focused: HashMap::new(),
            last_foreground_event: None,
            pending_workspace_focus: None,
            last_focus_retry: Instant::now() - Duration::from_secs(1),
            last_workspace_departure: None,
            workspace_switch_guard: None,
            last_explorer_relaunch: Instant::now() - Duration::from_secs(1),
            layouts: HashMap::new(),
            workspace_monitors: HashMap::new(),
            insertion_directions: HashMap::new(),
            minimum_sizes: HashMap::new(),
            pending_growth: HashMap::new(),
            dragging: None,
            snap_target: None,
            parked_rects: HashMap::new(),
            paused: false,
            resize_mode: false,
            closing: HashSet::new(),
            taskbar_hidden: HashSet::new(),
            recently_parked: HashMap::new(),
            last_local_foreground: None,
            pending_explorer_relaunch: None,
            last_published: None,
            config,
            bar_hidden: false,
        }
    }

    fn refresh(&mut self) -> (bool, bool) {
        use windows::Win32::UI::WindowsAndMessaging::{GetForegroundWindow, IsWindow};

        self.closing.retain(|handle| unsafe { IsWindow(hwnd(*handle)) }.as_bool());
        let discovered = enumerate_manageable_windows()
            .into_iter()
            .collect::<Vec<_>>();
        let discovered_handles = discovered.iter().map(|window| window.handle).collect::<HashSet<_>>();
        // Hidden-to-tray windows keep a valid HWND, but they are no longer a
        // visible managed window and must not keep their workspace alive.
        let removed = self.windows.keys().copied()
            .filter(|handle| {
                !discovered_handles.contains(handle)
                    && !managed_window_still_present(*handle)
            })
            .collect::<Vec<_>>();
        for handle in &removed {
            if let Some(window) = self.windows.remove(handle)
                && window.workspace == self.active_workspace
            {
                self.last_workspace_departure = Some((window.workspace, Instant::now()));
            }
            self.closing.remove(handle);
            if self
                .pending_workspace_focus
                .is_some_and(|(_, pending, _)| pending == *handle)
            {
                self.pending_workspace_focus = None;
            }
            self.parked_rects.remove(handle);
            self.remove_from_layout(*handle);
            self.insertion_directions.remove(handle);
            self.minimum_sizes.remove(handle);
            self.pending_growth.remove(handle);
            self.taskbar_hidden.remove(handle);
            self.last_focused.retain(|_, candidate| candidate != handle);
        }

        let stale_layouts_removed = self.prune_stale_layout_leaves();
        let mut changed = !removed.is_empty() || stale_layouts_removed;
        let mut layout_changed = changed;
        let mut newest_window = None;
        for mut window in discovered {
            if let Some(existing) = self.windows.get_mut(&window.handle) {
                if existing.title != window.title || existing.process_name != window.process_name {
                    existing.title = window.title;
                    existing.process_name = window.process_name;
                    changed = true;
                }
            } else {
                let explorer_spawn_workspace = if window
                    .process_name
                    .trim_end_matches(".exe")
                    .eq_ignore_ascii_case("explorer")
                {
                    self.pending_explorer_relaunch.take()
                } else {
                    None
                };
                window.workspace = self.active_workspace;
                let handle = window.handle;
                let persistence_key = window.persistence_key();
                let persisted_floating = self.config.window_floating_states
                    .get(&persistence_key).copied();
                let should_center = self.config.centered_window_types.contains(&persistence_key);
                window.floating = persisted_floating.unwrap_or(window.floating);
                let floating = window.floating;
                let ignored = self.minimum_size_ignored(&window.process_name);
                self.minimum_sizes.insert(handle, if ignored {
                    (64, 64)
                } else {
                    window_min_track_size(handle).unwrap_or((64, 64))
                });
                // Discord owns its custom maximize/restore chrome. Forcing
                // DWM transitions off on that HWND can leave Electron's
                // caption state out of sync, so let DWM manage it normally.
                let disable_transitions = !window
                    .process_name
                    .trim_end_matches(".exe")
                    .to_ascii_lowercase()
                    .starts_with("discord");
                set_managed_window_transitions(handle, disable_transitions);
                self.windows.insert(handle, window);
                let mut workspace = self.active_workspace;
                if !floating {
                    let original_layout = self.layouts.get(&self.active_workspace).cloned();
                    self.insert_into_layout(self.active_workspace, handle, self.focused, None, true);
                    if !self.constrain_workspace_to_minimum(self.active_workspace) {
                        self.remove_from_layout(handle);
                        let alternate = original_layout.as_ref().and_then(|original| {
                            let area = self.workspace_area(self.active_workspace)?;
                            self.find_fitting_insertion(original, area, handle)
                        });
                        if let Some(alternate) = alternate {
                            self.layouts.insert(self.active_workspace, alternate);
                        } else {
                            if let Some(original) = original_layout {
                                self.layouts.insert(self.active_workspace, original);
                            }
                            // The new window doesn't fit anywhere in the
                            // existing layout even after trying every
                            // insertion point. Rather than always banishing
                            // whichever window happened to be discovered
                            // last (essentially arbitrary - on initial
                            // launch, many pre-existing windows are
                            // enumerated and inserted one after another, so
                            // "last discovered" has nothing to do with which
                            // one is actually oversized), relocate whichever
                            // single window - the new one or an existing
                            // sibling already in this workspace - has the
                            // LARGEST minimum footprint, since that is the
                            // one actually responsible for the overflow.
                            let area_of = |manager: &Self, candidate: isize| {
                                manager.minimum_sizes.get(&candidate)
                                    .map(|(width, height)| (*width as i64) * (*height as i64))
                                    .unwrap_or(64 * 64)
                            };
                            let mut biggest = handle;
                            let mut biggest_area = area_of(self, handle);
                            let mut siblings = Vec::new();
                            if let Some(root) = self.layouts.get(&self.active_workspace) {
                                root.leaves(&mut siblings);
                            }
                            for sibling in siblings {
                                let area = area_of(self, sibling);
                                if area > biggest_area {
                                    biggest_area = area;
                                    biggest = sibling;
                                }
                            }
                            if biggest != handle {
                                // Move the oversized existing window away,
                                // then retry inserting the new (comparatively
                                // smaller) window normally.
                                self.remove_from_layout(biggest);
                                let displaced_workspace = self.next_available_workspace();
                                if let Some(window) = self.windows.get_mut(&biggest) {
                                    window.workspace = displaced_workspace;
                                }
                                self.insert_into_layout(displaced_workspace, biggest, None, None, true);
                                self.insert_into_layout(self.active_workspace, handle, self.focused, None, true);
                                if !self.constrain_workspace_to_minimum(self.active_workspace) {
                                    // Still doesn't fit (e.g. the new window
                                    // is ALSO oversized on its own) - fall
                                    // back to moving the new window itself.
                                    self.remove_from_layout(handle);
                                    workspace = self.next_available_workspace();
                                    if let Some(window) = self.windows.get_mut(&handle) {
                                        window.workspace = workspace;
                                    }
                                    self.insert_into_layout(workspace, handle, None, None, true);
                                }
                            } else {
                                workspace = self.next_available_workspace();
                                if let Some(window) = self.windows.get_mut(&handle) {
                                    window.workspace = workspace;
                                }
                                self.insert_into_layout(workspace, handle, None, None, true);
                            }
                        }
                    }
                } else if should_center {
                    self.center_floating_window(handle);
                }
                let relocate_to = explorer_spawn_workspace.filter(|target| {
                    *target != self.active_workspace && workspace == self.active_workspace
                });
                if let Some(target) = relocate_to {
                    // The user already left the workspace that requested this
                    // Explorer window; keep it there, parked, instead of
                    // dropping it onto whatever workspace is active now.
                    self.relocate_window_to_workspace(handle, target);
                    self.park_window(handle);
                    self.sync_taskbar_visibility();
                } else {
                    newest_window = Some((handle, workspace));
                }
                changed = true;
                layout_changed = true;
            }
        }

        if let Some((handle, workspace)) = newest_window {
            if workspace != self.active_workspace {
                self.focus_workspace(workspace);
            } else {
                focus_native_window(handle);
                self.focused = Some(handle);
                self.last_focused.insert(workspace, handle);
                self.pending_workspace_focus = Some((workspace, handle, Instant::now()));
            }
        }

        let foreground = unsafe { GetForegroundWindow() };
        let foreground_handle = self.last_foreground_event
            .filter(|(_, received)| received.elapsed() < Duration::from_millis(100))
            .map(|(handle, _)| handle)
            .or_else(|| (!foreground.is_invalid()).then_some(foreground.0 as isize));
        // While launcher input is active its HWND is intentionally foreground but
        // is not a managed application. Preserve the last application focus and
        // border instead of interpreting that transient foreground state as "none".
        let mut focused = if SEARCH_INPUT_ACTIVE.load(Ordering::Acquire) {
            self.focused.filter(|handle| self.windows.contains_key(handle))
        } else {
            foreground_handle.filter(|handle| self.windows.contains_key(handle))
        };
        if let Some(handle) = focused
            && self.windows.get(&handle).is_some_and(|window| window.workspace != self.active_workspace)
        {
            // The foreground event for this window may still be queued. Taking
            // focus back here would make it look stale by the time it is
            // handled, so a tray/app-initiated activation could never switch
            // workspaces. Leave it to `apply_foreground_event` to decide.
            use windows::Win32::UI::WindowsAndMessaging::EVENT_SYSTEM_FOREGROUND;
            let event_pending = WINDOW_EVENTS
                .get_or_init(Default::default)
                .lock()
                .map(|events| {
                    events.iter().any(|(event, queued)| {
                        *event == EVENT_SYSTEM_FOREGROUND && *queued == handle
                    })
                })
                .unwrap_or(false);
            if event_pending {
                focused = None;
            } else {
                // A taskbar/Alt-Tab activation must not pull an inactive workspace
                // window back onto the current desktop.
                self.park_window(handle);
                focused = self.last_focused.get(&self.active_workspace).copied()
                    .filter(|candidate| self.windows.contains_key(candidate));
                if let Some(active) = focused {
                    focus_native_window(active);
                    self.pending_workspace_focus = Some((
                        self.active_workspace,
                        active,
                        Instant::now(),
                    ));
                }
            }
        }
        // Keep the "last local foreground" fresh while a local window actually
        // holds focus, so a minimize fallback is recognised even if the window
        // had been focused for longer than the fallback grace period.
        if let Some(handle) = focused
            && self.windows.get(&handle).is_some_and(|window| window.workspace == self.active_workspace)
        {
            self.last_local_foreground = Some((handle, Instant::now()));
        }
        if self.focused != focused {
            self.focused = focused;
            changed = true;
            if let Some(handle) = focused {
                let workspace = self
                    .windows
                    .get(&handle)
                    .map_or(self.active_workspace, |window| window.workspace);
                let direction = self
                    .insertion_directions
                    .get(&handle)
                    .copied()
                    .unwrap_or_else(|| self.automatic_direction(workspace, handle));
                self.direction = direction;
            }
        }
        if let Some(handle) = focused && let Some(window) = self.windows.get(&handle) {
            self.last_focused.insert(window.workspace, handle);
        }

        self.apply_borders();
        (changed, layout_changed)
    }

    fn remove_from_layout(&mut self, handle: isize) {
        let workspaces = self.layouts.keys().copied().collect::<Vec<_>>();
        for workspace in workspaces {
            if let Some(root) = self.layouts.remove(&workspace) {
                if let Some(root) = root.remove(handle) {
                    self.layouts.insert(workspace, root);
                } else {
                    self.workspace_monitors.remove(&workspace);
                }
            }
        }
    }

    fn prune_stale_layout_leaves(&mut self) -> bool {
        let mut stale = Vec::new();
        for (workspace, root) in &self.layouts {
            let mut leaves = Vec::new();
            root.leaves(&mut leaves);
            stale.extend(leaves.into_iter().filter(|handle| {
                !self.windows.get(handle).is_some_and(|window| {
                    window.workspace == *workspace && !window.floating
                })
            }));
        }
        stale.sort_unstable();
        stale.dedup();
        for handle in &stale {
            self.remove_from_layout(*handle);
        }
        !stale.is_empty()
    }

    fn next_available_workspace(&self) -> usize {
        let occupied = self.windows.values().map(|window| window.workspace).collect::<HashSet<_>>();
        (1..=99).find(|workspace| !occupied.contains(workspace)).unwrap_or(99)
    }

    fn minimum_size_ignored(&self, process_name: &str) -> bool {
        let process = process_name.trim().trim_end_matches(".exe").to_ascii_lowercase();
        process == "zen"
            || process == "zen-browser"
            || self.config.ignore_minimum_size_apps.iter().any(|name| {
            let ignored = name.trim().trim_end_matches(".exe").to_ascii_lowercase();
            !ignored.is_empty() && ignored == process
        })
    }

    fn update_config(&mut self, config: WmConfig) {
        self.config = config;
        for window in self.windows.values() {
            let size = if self.minimum_size_ignored(&window.process_name) {
                (64, 64)
            } else {
                window_min_track_size(window.handle).unwrap_or((64, 64))
            };
            self.minimum_sizes.insert(window.handle, size);
        }
        if !self.paused { self.tile_active_workspace(); }
    }

    fn insert_into_layout(
        &mut self,
        workspace: usize,
        handle: isize,
        preferred_target: Option<isize>,
        forced_direction: Option<TilingDirection>,
        after: bool,
    ) {
        use windows::Win32::Graphics::Gdi::{MONITOR_DEFAULTTONEAREST, MonitorFromWindow};
        self.remove_from_layout(handle);
        let monitor = unsafe { MonitorFromWindow(hwnd(handle), MONITOR_DEFAULTTONEAREST) }.0 as isize;
        self.workspace_monitors.entry(workspace).or_insert(monitor);
        if self.layouts.contains_key(&workspace) {
            let mut leaves = Vec::new();
            if let Some(root) = self.layouts.get(&workspace) {
                root.leaves(&mut leaves);
            }
            let target = preferred_target.filter(|candidate| {
                self.layouts
                    .get(&workspace)
                    .is_some_and(|root| root.contains(*candidate))
            })
                .or_else(|| self.last_focused.get(&workspace).copied().filter(|candidate| {
                    self.layouts
                        .get(&workspace)
                        .is_some_and(|root| root.contains(*candidate))
                }))
                .or_else(|| leaves.last().copied());
            if let Some(target) = target {
                let direction = forced_direction
                    .or_else(|| self.insertion_directions.get(&target).copied())
                    .unwrap_or_else(|| self.automatic_direction(workspace, target));
                if let Some(root) = self.layouts.get_mut(&workspace) {
                    let _ = root.insert_beside(target, handle, direction, after);
                }
            }
        } else {
            self.layouts.insert(workspace, LayoutNode::Leaf(handle));
        }
    }

    fn automatic_direction(&self, workspace: usize, target: isize) -> TilingDirection {
        let Some((_, rect)) = self
            .layout_rects(workspace)
            .into_iter()
            .find(|(handle, _)| *handle == target)
        else {
            return TilingDirection::Horizontal;
        };
        let width = (rect.right - rect.left).max(1) as f32;
        let height = (rect.bottom - rect.top).max(1) as f32;
        // Prefer a new column until a tile becomes noticeably taller than it
        // is wide. This produces useful two/three-column layouts on widescreen
        // monitors, then starts rows within those columns instead of building
        // a long vertical stack.
        if width >= height * 0.85 {
            TilingDirection::Horizontal
        } else {
            TilingDirection::Vertical
        }
    }

    fn focus_workspace(&mut self, workspace: usize) {
        let workspace = workspace.clamp(1, 99);
        if workspace == self.active_workspace {
            if let Some(handle) = self.preferred_workspace_window(workspace) {
                focus_native_window(handle);
                self.focused = Some(handle);
                self.pending_workspace_focus = Some((workspace, handle, Instant::now()));
            }
            return;
        }

        self.recent_workspace = self.active_workspace;
        self.active_workspace = workspace;
        self.workspace_switch_guard = Some((workspace, Instant::now()));
        // Park inactive workspace windows off-screen rather than hiding or
        // cloaking them. Hide/cloak makes Chromium windows look as if they were
        // destroyed and recreated; parking preserves their compositor surface.
        let inactive = self.windows.values()
            .filter(|window| window.workspace != workspace)
            .map(|window| window.handle)
            .collect::<Vec<_>>();
        let active = self.windows.values()
            .filter(|window| window.workspace == workspace)
            .map(|window| window.handle)
            .collect::<Vec<_>>();
        for handle in inactive {
            self.park_window(handle);
        }
        for handle in active {
            self.unpark_window(handle);
        }
        self.sync_taskbar_visibility();
        if !self.paused {
            self.tile_active_workspace();
        }
        flush_dwm();
        let target = self.preferred_workspace_window(workspace);
        if let Some(handle) = target {
            focus_native_window(handle);
            self.focused = Some(handle);
            self.last_focused.insert(workspace, handle);
            // Remember it as the local foreground so that minimizing it right
            // away (taskbar click) is recognised and its z-order fallback onto
            // another workspace's parked window is not mistaken for a switch.
            self.last_local_foreground = Some((handle, Instant::now()));
            // Some applications do not accept foreground activation until their
            // compositor surface has returned from its parked position. Retry for
            // a short bounded interval instead of losing the workspace's focus.
            self.pending_workspace_focus = Some((workspace, handle, Instant::now()));
        } else {
            self.pending_workspace_focus = None;
            use windows::Win32::UI::WindowsAndMessaging::{GetShellWindow, SetForegroundWindow};
            self.focused = None;
            let shell = unsafe { GetShellWindow() };
            if !shell.is_invalid() {
                unsafe { let _ = SetForegroundWindow(shell); }
            }
        }
        WINDOW_EVENT_DIRTY.store(true, Ordering::Release);
    }

    fn preferred_workspace_window(&self, workspace: usize) -> Option<isize> {
        self.last_focused
            .get(&workspace)
            .copied()
            .filter(|handle| {
                self.windows
                    .get(handle)
                    .is_some_and(|window| window.workspace == workspace)
            })
            .or_else(|| {
                let mut leaves = Vec::new();
                self.layouts.get(&workspace)?.leaves(&mut leaves);
                leaves.into_iter().rev().find(|handle| self.windows.contains_key(handle))
            })
            .or_else(|| {
                self.windows
                    .values()
                    .find(|window| window.workspace == workspace)
                    .map(|window| window.handle)
            })
    }

    fn enforce_pending_workspace_focus(&mut self) {
        use windows::Win32::UI::WindowsAndMessaging::GetForegroundWindow;
        if SEARCH_INPUT_ACTIVE.load(Ordering::Acquire) {
            self.pending_workspace_focus = None;
            return;
        }
        let Some((workspace, handle, started)) = self.pending_workspace_focus else { return; };
        if started.elapsed() > Duration::from_millis(500)
            || workspace != self.active_workspace
            || !self.windows.get(&handle).is_some_and(|window| window.workspace == workspace)
        {
            self.pending_workspace_focus = None;
            return;
        }
        let foreground = unsafe { GetForegroundWindow() }.0 as isize;
        if foreground == handle {
            self.pending_workspace_focus = None;
            self.focused = Some(handle);
            return;
        }
        // If the target got minimized after the switch (the user clicked its
        // taskbar icon), retrying focus would restore it and undo that.
        if started.elapsed() > Duration::from_millis(200)
            && unsafe { windows::Win32::UI::WindowsAndMessaging::IsIconic(hwnd(handle)) }.as_bool()
        {
            self.pending_workspace_focus = None;
            return;
        }
        // SetForegroundWindow/AttachThreadInput is intentionally invasive.
        // Running it every 8 ms made applications repeatedly reactivate and
        // repaint when Windows rejected focus, which looked like the whole
        // layout was flashing. Workspace switches still get bounded retries,
        // but never more often than eight times per second.
        if self.last_focus_retry.elapsed() < Duration::from_millis(125) {
            return;
        }
        self.last_focus_retry = Instant::now();
        focus_native_window(handle);
        self.focused = Some(handle);
        self.last_focused.insert(workspace, handle);
    }

    fn move_focused_to_workspace(&mut self, workspace: usize) {
        let Some(handle) = self.focused else {
            return;
        };
        let Some(window) = self.windows.get_mut(&handle) else {
            return;
        };
        let old_workspace = window.workspace;
        let new_workspace = workspace.clamp(1, 99);
        window.workspace = new_workspace;
        self.last_focused.insert(new_workspace, handle);
        self.remove_from_layout(handle);
        self.insert_into_layout(new_workspace, handle, self.last_focused.get(&new_workspace).copied(), None, true);
        self.park_window(handle);
        self.sync_taskbar_visibility();
        if !self.paused {
            self.tile_workspace(old_workspace);
        }
        WINDOW_EVENT_DIRTY.store(true, Ordering::Release);
    }

    fn toggle_floating(&mut self) -> bool {
        use windows::Win32::UI::WindowsAndMessaging::{
            SWP_NOACTIVATE, SWP_NOOWNERZORDER, SWP_NOSENDCHANGING, SWP_NOZORDER,
            SetWindowPos,
        };
        let Some(handle) = self.focused else {
            return false;
        };
        // A window the user native-maximized (or that went borderless
        // fullscreen) is still conceptually "tiled" underneath - Alt+T on it
        // should only restore that back to tiled, exactly like clicking the
        // window's own restore button, instead of also kicking it into
        // floating mode (which left it in an inconsistent state: floating
        // but still tagged `maximize_restore`, so it was permanently skipped
        // by `sync_native_maximize`'s candidate filter and could never be
        // untangled again).
        if self.windows.get(&handle).is_some_and(|window| window.maximize_restore.is_some()) {
            let original = self.windows.get_mut(&handle).and_then(|window| {
                window.native_maximized = false;
                window.maximize_restore.take()
            });
            let Some(original) = original else { return false; };
            let current_workspace = self.windows.get(&handle).map(|window| window.workspace);
            if current_workspace != Some(original) {
                self.relocate_window_to_workspace(handle, original);
                self.focus_workspace(original);
            } else if !self.paused {
                self.tile_active_workspace();
            }
            WINDOW_EVENT_DIRTY.store(true, Ordering::Release);
            return true;
        }
        let Some(window) = self.windows.get_mut(&handle) else {
            return false;
        };
        window.floating = !window.floating;
        let floating = window.floating;
        let workspace = window.workspace;
        let persistence_key = window.persistence_key();
        let original_rect = window.original_rect;
        self.config.window_floating_states.insert(persistence_key.clone(), floating);
        if floating {
            self.remove_from_layout(handle);
            unsafe {
                let _ = SetWindowPos(
                    hwnd(handle),
                    None,
                    original_rect.left,
                    original_rect.top,
                    (original_rect.right - original_rect.left).max(64),
                    (original_rect.bottom - original_rect.top).max(64),
                    SWP_NOACTIVATE | SWP_NOOWNERZORDER | SWP_NOSENDCHANGING | SWP_NOZORDER,
                );
            }
            if self.config.centered_window_types.contains(&persistence_key) {
                self.center_floating_window(handle);
            }
        } else {
            self.insert_into_layout(workspace, handle, self.last_focused.get(&workspace).copied(), None, true);
        }
        if !self.paused {
            self.tile_active_workspace();
        }
        WINDOW_EVENT_DIRTY.store(true, Ordering::Release);
        true
    }

    // Unlike `toggle_floating` (which cycles tiled<->floating), this only
    // ever moves the focused window *towards* tiled: a floating window (or
    // one that's native-maximized/fullscreen) gets tiled/restored, and a
    // window that's already tiled just gets retiled in place instead of
    // being left untouched or flipped to floating.
    fn set_tiled(&mut self) -> bool {
        let Some(handle) = self.focused else {
            return false;
        };
        let already_tiled = self.windows.get(&handle).is_some_and(|window| {
            window.maximize_restore.is_none() && !window.floating
        });
        if !already_tiled {
            return self.toggle_floating();
        }
        if !self.paused {
            self.tile_active_workspace();
        }
        WINDOW_EVENT_DIRTY.store(true, Ordering::Release);
        true
    }

    fn center_focused_floating(&mut self) -> bool {
        let Some(handle) = self.focused else { return false; };
        let Some(key) = self.windows.get(&handle).map(ManagedWindow::persistence_key) else {
            return false;
        };
        if !self.center_floating_window(handle) {
            return false;
        }
        self.config.centered_window_types.insert(key);
        true
    }

    fn center_floating_window(&mut self, handle: isize) -> bool {
        use windows::Win32::{
            Foundation::RECT,
            Graphics::Gdi::{
                GetMonitorInfoW, MONITOR_DEFAULTTONEAREST, MONITORINFO, MonitorFromWindow,
            },
            UI::WindowsAndMessaging::{
                GetWindowRect, IsIconic, SWP_NOACTIVATE, SWP_NOOWNERZORDER,
                SWP_NOSENDCHANGING, SWP_NOZORDER, SetWindowPos,
            },
        };
        let valid = self.windows.get(&handle).is_some_and(|window| {
                window.workspace == self.active_workspace
                    && window.floating
                    && window.fullscreen_restore.is_none()
                    && window.maximize_restore.is_none()
            });
        if !valid { return false; }
        if unsafe { IsIconic(hwnd(handle)) }.as_bool() {
            return false;
        }
        let mut window_rect = RECT::default();
        if unsafe { GetWindowRect(hwnd(handle), &mut window_rect) }.is_err() {
            return false;
        }
        let monitor = unsafe { MonitorFromWindow(hwnd(handle), MONITOR_DEFAULTTONEAREST) };
        let mut info = MONITORINFO {
            cbSize: std::mem::size_of::<MONITORINFO>() as u32,
            ..Default::default()
        };
        if !unsafe { GetMonitorInfoW(monitor, &mut info) }.as_bool() {
            return false;
        }
        let mut area = LayoutRect {
            left: info.rcWork.left,
            top: info.rcWork.top,
            right: info.rcWork.right,
            bottom: info.rcWork.bottom,
        };
        if info.dwFlags != 0 {
            area.top = area.top.max(info.rcMonitor.top + BAR_HEIGHT);
        }
        let width = (window_rect.right - window_rect.left).max(64);
        let height = (window_rect.bottom - window_rect.top).max(64);
        let left = area.left + ((area.right - area.left - width).max(0) / 2);
        let top = area.top + ((area.bottom - area.top - height).max(0) / 2);
        unsafe {
            let _ = SetWindowPos(
                hwnd(handle),
                None,
                left,
                top,
                width,
                height,
                SWP_NOACTIVATE | SWP_NOOWNERZORDER | SWP_NOSENDCHANGING | SWP_NOZORDER,
            );
        }
        WINDOW_EVENT_DIRTY.store(true, Ordering::Release);
        true
    }

    fn park_window(&mut self, handle: isize) {
        use windows::Win32::{
            Foundation::RECT,
            UI::WindowsAndMessaging::{
                GetWindowRect, SWP_NOACTIVATE, SWP_NOOWNERZORDER, SWP_NOSENDCHANGING,
                SWP_NOZORDER, SetWindowPos,
            },
        };
        let rect = self.parked_rects.entry(handle).or_insert_with(|| {
            let mut rect = RECT::default();
            if unsafe { GetWindowRect(hwnd(handle), &mut rect) }.is_ok() {
                LayoutRect { left: rect.left, top: rect.top, right: rect.right, bottom: rect.bottom }
            } else {
                LayoutRect { left: 0, top: 0, right: 800, bottom: 600 }
            }
        });
        let target_width = (rect.right - rect.left).max(64);
        let target_height = (rect.bottom - rect.top).max(64);
        // `enforce_workspace_visibility` calls this every ~75ms for every
        // inactive-workspace window, not just once per workspace switch.
        // Skip the redundant SetWindowPos (and, crucially, skip refreshing
        // `recently_parked`) when the window is already sitting at the
        // parked position - otherwise `recently_parked`'s timestamp would
        // never actually expire while a window stays in an inactive
        // workspace, perpetually re-arming `apply_foreground_event`'s
        // spurious-activation suppression/redirect logic for a window that
        // hasn't transitioned in a long time. Still re-applies if an app
        // manages to move itself back on-screen while parked.
        let mut current = RECT::default();
        let already_parked = unsafe { GetWindowRect(hwnd(handle), &mut current) }.is_ok()
            && (current.left - (-32_000)).abs() <= 4
            && (current.top - (-32_000)).abs() <= 4;
        if already_parked {
            return;
        }
        self.recently_parked.insert(handle, Instant::now());
        unsafe {
            let _ = SetWindowPos(
                hwnd(handle),
                None,
                -32_000,
                -32_000,
                target_width,
                target_height,
                SWP_NOACTIVATE | SWP_NOOWNERZORDER | SWP_NOSENDCHANGING | SWP_NOZORDER,
            );
        }
    }

    fn unpark_window(&mut self, handle: isize) {
        use windows::Win32::UI::WindowsAndMessaging::{
            SWP_NOACTIVATE, SWP_NOOWNERZORDER, SWP_NOSENDCHANGING, SWP_NOZORDER, SetWindowPos,
        };
        let Some(rect) = self.parked_rects.remove(&handle) else { return; };
        // Tiled windows are immediately assigned their tree rectangle below;
        // floating windows return to the exact position they had before switching.
        if self.windows.get(&handle).is_some_and(|window| window.floating) {
            unsafe {
                let _ = SetWindowPos(
                    hwnd(handle), None, rect.left, rect.top,
                    (rect.right - rect.left).max(64), (rect.bottom - rect.top).max(64),
                    SWP_NOACTIVATE | SWP_NOOWNERZORDER | SWP_NOSENDCHANGING | SWP_NOZORDER,
                );
            }
        }
    }

    fn enforce_workspace_visibility(&mut self) {
        let inactive = self.windows.values()
            .filter(|window| window.workspace != self.active_workspace)
            .map(|window| window.handle)
            .collect::<Vec<_>>();
        for handle in inactive {
            self.park_window(handle);
        }
        self.sync_taskbar_visibility();
    }

    fn sync_taskbar_visibility(&mut self) {
        let states = self.windows.values()
            .filter(|window| window.owner.is_none())
            .map(|window| (window.handle, window.workspace == self.active_workspace))
            .collect::<Vec<_>>();
        for (handle, visible) in states {
            if visible {
                if self.taskbar_hidden.remove(&handle) {
                    set_native_taskbar_tab_visible(handle, true);
                }
            } else if self.taskbar_hidden.insert(handle) {
                set_native_taskbar_tab_visible(handle, false);
            }
        }
    }

    fn toggle_paused(&mut self) {
        self.paused = !self.paused;
        if !self.paused {
            self.tile_active_workspace();
        }
    }

    fn focus_relative_workspace(&mut self, delta: isize) {
        let active = self
            .windows
            .values()
            .map(|window| window.workspace)
            .chain(std::iter::once(self.active_workspace))
            .collect::<HashSet<_>>();
        let mut active = active.into_iter().collect::<Vec<_>>();
        active.sort_unstable();
        let current = active
            .iter()
            .position(|workspace| *workspace == self.active_workspace)
            .unwrap_or(0);
        let next = (current as isize + delta).rem_euclid(active.len() as isize) as usize;
        self.focus_workspace(active[next]);
    }

    fn toggle_fullscreen(&mut self) {
        use windows::Win32::{
            Foundation::RECT,
            Graphics::Gdi::{MONITOR_DEFAULTTONEAREST, MONITORINFO, GetMonitorInfoW, MonitorFromWindow},
            UI::WindowsAndMessaging::{
                GWL_STYLE, GetWindowLongW, GetWindowRect, SWP_FRAMECHANGED, SWP_NOACTIVATE,
                SWP_NOOWNERZORDER, SWP_NOZORDER, SetWindowLongW, SetWindowPos, WS_CAPTION,
                WS_THICKFRAME,
            },
        };
        let Some(handle) = self.focused.filter(|handle| self.windows.contains_key(handle)) else {
            return;
        };
        let Some(window) = self.windows.get_mut(&handle) else {
            return;
        };
        unsafe {
            if let Some(restore) = window.fullscreen_restore.take() {
                SetWindowLongW(hwnd(handle), GWL_STYLE, restore.style);
                let _ = SetWindowPos(
                    hwnd(handle),
                    None,
                    restore.rect.0,
                    restore.rect.1,
                    restore.rect.2 - restore.rect.0,
                    restore.rect.3 - restore.rect.1,
                    SWP_FRAMECHANGED | SWP_NOACTIVATE | SWP_NOOWNERZORDER | SWP_NOZORDER,
                );
            } else {
                let mut rect = RECT::default();
                if GetWindowRect(hwnd(handle), &mut rect).is_err() {
                    return;
                }
                let style = GetWindowLongW(hwnd(handle), GWL_STYLE);
                window.fullscreen_restore = Some(FullscreenRestore {
                    rect: (rect.left, rect.top, rect.right, rect.bottom),
                    style,
                });
                SetWindowLongW(
                    hwnd(handle),
                    GWL_STYLE,
                    style & !(WS_CAPTION.0 | WS_THICKFRAME.0) as i32,
                );
                let monitor = MonitorFromWindow(hwnd(handle), MONITOR_DEFAULTTONEAREST);
                let mut info = MONITORINFO {
                    cbSize: std::mem::size_of::<MONITORINFO>() as u32,
                    ..Default::default()
                };
                if GetMonitorInfoW(monitor, &mut info).as_bool() {
                    let rect = info.rcMonitor;
                    let _ = SetWindowPos(
                        hwnd(handle),
                        None,
                        rect.left,
                        rect.top,
                        rect.right - rect.left,
                        rect.bottom - rect.top,
                        SWP_FRAMECHANGED | SWP_NOACTIVATE | SWP_NOOWNERZORDER | SWP_NOZORDER,
                    );
                }
            }
        }
        if self
            .windows
            .get(&handle)
            .is_some_and(|window| window.fullscreen_restore.is_none() && !window.floating)
            && !self.paused
        {
            self.tile_active_workspace();
        }
    }

    /// Detect windows that have gone fullscreen - either a native OS maximize
    /// (double-clicked titlebar, Win+Up, maximize button, detected via
    /// `IsZoomed`) or an app-driven borderless fullscreen such as F11 in a
    /// browser (detected by the window's rect covering the entire monitor,
    /// including the area under the taskbar) - or restored, and react: a
    /// freshly fullscreened window is moved to an empty workspace (if it
    /// would otherwise share its workspace with other windows) while the bar
    /// auto-hides; restoring it moves it back to its original workspace and
    /// switches back there. Only genuinely fullscreen windows trigger the
    /// workspace relocation - an ordinary window the user merely dragged over
    /// the bar's strip does not, it only hides the bar (see
    /// `any_window_over_bar_strip`).
    fn sync_native_maximize(&mut self, updates: &Sender<WindowManagerUpdate>) {
        use windows::Win32::{
            Foundation::RECT,
            Graphics::Gdi::{GetMonitorInfoW, MONITOR_DEFAULTTONEAREST, MONITORINFO, MonitorFromWindow},
            UI::WindowsAndMessaging::{GWL_STYLE, GetWindowLongW, GetWindowRect, IsZoomed, WS_CAPTION},
        };

        const COVER_TOLERANCE: i32 = 2;
        fn covers_monitor(handle: isize) -> bool {
            // Only treat "window rect covers the whole monitor" as fullscreen
            // for borderless windows (no title bar / caption) - this is how
            // apps implement F11-style fullscreen (same style bits our own
            // `toggle_fullscreen` strips). Ordinary windows that keep their
            // normal chrome (Discord, FL Studio, ...) rely solely on
            // `IsZoomed` below; without this guard, a brief resize-animation
            // frame that happens to land near-fullscreen could misfire as
            // "became fullscreen", causing spurious workspace relocation.
            if unsafe { GetWindowLongW(hwnd(handle), GWL_STYLE) } as u32 & WS_CAPTION.0 != 0 {
                return false;
            }
            let mut rect = RECT::default();
            if unsafe { GetWindowRect(hwnd(handle), &mut rect) }.is_err() {
                return false;
            }
            let monitor = unsafe { MonitorFromWindow(hwnd(handle), MONITOR_DEFAULTTONEAREST) };
            let mut info = MONITORINFO {
                cbSize: std::mem::size_of::<MONITORINFO>() as u32,
                ..Default::default()
            };
            if !unsafe { GetMonitorInfoW(monitor, &mut info) }.as_bool() {
                return false;
            }
            (rect.left - info.rcMonitor.left).abs() <= COVER_TOLERANCE
                && (rect.top - info.rcMonitor.top).abs() <= COVER_TOLERANCE
                && (rect.right - info.rcMonitor.right).abs() <= COVER_TOLERANCE
                && (rect.bottom - info.rcMonitor.bottom).abs() <= COVER_TOLERANCE
        }

        let candidates = self
            .windows
            .values()
            .filter(|window| !window.floating && window.owner.is_none() && window.fullscreen_restore.is_none())
            .map(|window| (
                window.handle,
                window.workspace,
                window.maximize_restore,
                window.native_maximized,
            ))
            .collect::<Vec<_>>();

        let mut became_fullscreen = Vec::new();
        let mut restored = Vec::new();
        for (handle, workspace, restore, was_native) in candidates {
            let is_zoomed = unsafe { IsZoomed(hwnd(handle)) }.as_bool();
            let is_fullscreen = if restore.is_some() && was_native {
                // Discord and other frameless Electron apps may still cover
                // the monitor for an animation frame after native restore.
                // Their Win32 zoom state is authoritative and changes first.
                is_zoomed
            } else {
                is_zoomed || covers_monitor(handle)
            };
            match (is_fullscreen, restore) {
                (true, None) => became_fullscreen.push((handle, workspace, is_zoomed)),
                (false, Some(original)) => restored.push((handle, original)),
                _ => {}
            }
        }

        for (handle, workspace, native) in became_fullscreen {
            let has_siblings = self
                .windows
                .values()
                .any(|other| other.handle != handle && other.workspace == workspace);
            let discord = self.windows.get(&handle).is_some_and(|window| {
                window
                    .process_name
                    .trim_end_matches(".exe")
                    .to_ascii_lowercase()
                    .starts_with("discord")
            });
            // Keep Discord on its current workspace while maximized. Moving
            // its Electron HWND through Overbar's cloak/workspace lifecycle
            // can prevent the custom caption button from completing restore.
            let target = if has_siblings && !discord {
                self.next_available_workspace()
            } else {
                workspace
            };
            if let Some(window) = self.windows.get_mut(&handle) {
                window.maximize_restore = Some(workspace);
                window.native_maximized = native;
            }
            if target != workspace {
                self.relocate_window_to_workspace(handle, target);
                self.focus_workspace(target);
            }
            // When solo (no siblings), there is nothing to retile: the
            // window already occupies the whole workspace. Retiling it here
            // would immediately shrink it back down to `workspace_area()`
            // (which excludes the bar strip / monitor edges it just grew
            // into), making it look like it instantly un-fullscreened
            // itself. That false "shrink" then satisfied the restore-
            // detection on the very next poll, silently clearing
            // `maximize_restore` before the user ever touched the window's
            // own restore button - this was the root cause of Discord's
            // (and any other borderless/custom-chrome app's) restore button
            // appearing to do nothing: our own code had already cleared the
            // tracked maximize state moments after it was set.
        }
        for (handle, original) in restored {
            if let Some(window) = self.windows.get_mut(&handle) {
                window.maximize_restore = None;
                window.native_maximized = false;
            }
            let current_workspace = self.windows.get(&handle).map(|window| window.workspace);
            if current_workspace != Some(original) {
                self.relocate_window_to_workspace(handle, original);
                self.focus_workspace(original);
            } else if !self.paused {
                self.tile_active_workspace();
            }
        }

        // Do not resize natively maximized windows here. Electron and other
        // custom-chrome applications keep their own maximize bookkeeping;
        // forcing even a near-identical rectangle with SetWindowPos can make
        // their restore button issue another maximize instead. Windows owns
        // the native maximized geometry, while the bar independently hides
        // whenever that geometry overlaps its strip.

        // Bar auto-hide is broader than the fullscreen/maximize handling
        // above: hide it whenever ANY visible window on the active workspace
        // intrudes into its reserved strip (native maximize, borderless
        // fullscreen, or simply a window dragged up over the bar), without
        // requiring a workspace switch.
        let bar_hidden = self.any_window_over_bar_strip();
        if bar_hidden != self.bar_hidden {
            self.bar_hidden = bar_hidden;
            let _ = updates.send(WindowManagerUpdate::BarVisibility(bar_hidden));
        }
    }

    /// True if any visible, non-minimized window on the active workspace
    /// overlaps the bar's reserved strip at the top of its (primary) monitor.
    fn any_window_over_bar_strip(&self) -> bool {
        use windows::Win32::{
            Foundation::{POINT, RECT},
            Graphics::Gdi::{GetMonitorInfoW, MONITOR_DEFAULTTOPRIMARY, MONITORINFO, MonitorFromPoint},
            UI::WindowsAndMessaging::{GetWindowRect, IsIconic},
        };
        let monitor = unsafe { MonitorFromPoint(POINT { x: 0, y: 0 }, MONITOR_DEFAULTTOPRIMARY) };
        let mut info = MONITORINFO {
            cbSize: std::mem::size_of::<MONITORINFO>() as u32,
            ..Default::default()
        };
        if !unsafe { GetMonitorInfoW(monitor, &mut info) }.as_bool() {
            return false;
        }
        let strip_left = info.rcMonitor.left;
        let strip_right = info.rcMonitor.right;
        let strip_top = info.rcMonitor.top;
        let strip_bottom = info.rcMonitor.top + BAR_HEIGHT;

        self.windows.values().filter(|window| window.workspace == self.active_workspace).any(|window| {
            if unsafe { IsIconic(hwnd(window.handle)) }.as_bool() {
                return false;
            }
            let mut rect = RECT::default();
            if unsafe { GetWindowRect(hwnd(window.handle), &mut rect) }.is_err() {
                return false;
            }
            rect.left < strip_right && rect.right > strip_left && rect.top < strip_bottom && rect.bottom > strip_top
        })
    }


    fn relocate_window_to_workspace(&mut self, handle: isize, new_workspace: usize) {
        let Some(window) = self.windows.get_mut(&handle) else { return };
        let old_workspace = window.workspace;
        if old_workspace == new_workspace {
            return;
        }
        window.workspace = new_workspace;
        self.remove_from_layout(handle);
        self.insert_into_layout(new_workspace, handle, None, None, true);
        if self.last_focused.get(&old_workspace) == Some(&handle) {
            self.last_focused.remove(&old_workspace);
        }
        self.last_focused.insert(new_workspace, handle);
        if !self.paused {
            self.tile_workspace(old_workspace);
        }
    }

    fn toggle_minimized(&mut self) {
        use windows::Win32::UI::WindowsAndMessaging::{
            IsIconic, SW_MINIMIZE, SW_RESTORE, ShowWindowAsync,
        };
        let Some(handle) = self.focused.filter(|handle| self.windows.contains_key(handle)) else {
            return;
        };
        unsafe {
            let command = if IsIconic(hwnd(handle)).as_bool() {
                SW_RESTORE
            } else {
                SW_MINIMIZE
            };
            let _ = ShowWindowAsync(hwnd(handle), command);
        }
    }

    fn close_focused(&mut self) {
        if let Some(handle) = self.focused {
            self.close_window(handle);
        }
    }

    fn forget_window(&mut self, handle: isize) -> bool {
        let Some(window) = self.windows.remove(&handle) else { return false; };
        if window.workspace == self.active_workspace {
            self.last_workspace_departure = Some((window.workspace, Instant::now()));
        }
        self.remove_from_layout(handle);
        self.parked_rects.remove(&handle);
        self.insertion_directions.remove(&handle);
        self.minimum_sizes.remove(&handle);
        self.pending_growth.remove(&handle);
        self.taskbar_hidden.remove(&handle);
        self.closing.remove(&handle);
        if self
            .pending_workspace_focus
            .is_some_and(|(_, pending, _)| pending == handle)
        {
            self.pending_workspace_focus = None;
        }
        self.last_focused.retain(|_, candidate| *candidate != handle);
        if self.focused == Some(handle) {
            self.focused = None;
        }
        true
    }

    fn close_window(&mut self, handle: isize) {
        use windows::Win32::{
            Foundation::{LPARAM, WPARAM},
            UI::WindowsAndMessaging::{PostMessageW, WM_CLOSE},
        };
        if !self.windows.contains_key(&handle) || !self.closing.insert(handle) {
            return;
        }
        self.note_window_departure(handle);
        if unsafe { PostMessageW(hwnd(handle), WM_CLOSE, WPARAM(0), LPARAM(0)) }.is_err() {
            self.closing.remove(&handle);
        }
    }

    fn focus_window(&mut self, handle: isize, workspace: usize) {
        self.focus_workspace(workspace);
        if self.windows.contains_key(&handle) {
            focus_native_window(handle);
            self.focused = Some(handle);
            self.last_focused.insert(workspace, handle);
            self.pending_workspace_focus = Some((workspace, handle, Instant::now()));
        }
    }

    fn focus_active_replacement(&mut self) {
        use windows::Win32::UI::WindowsAndMessaging::GetForegroundWindow;

        let native_foreground = unsafe { GetForegroundWindow() };
        let native_foreground = (!native_foreground.is_invalid())
            .then_some(native_foreground.0 as isize)
            .filter(|handle| {
                self.windows.get(handle).is_some_and(|window| {
                    window.workspace == self.active_workspace
                        && !self.closing.contains(handle)
                })
            });
        let recent_foreground = self
            .last_foreground_event
            .filter(|(_, received)| received.elapsed() < Duration::from_millis(150))
            .map(|(handle, _)| handle)
            .filter(|handle| {
                self.windows.get(handle).is_some_and(|window| {
                    window.workspace == self.active_workspace
                        && !self.closing.contains(handle)
                })
            });
        let preferred = native_foreground
            .or(recent_foreground)
            .or_else(|| self.last_focused.get(&self.active_workspace).copied())
            .filter(|handle| self.windows.get(handle).is_some_and(|window| {
                window.workspace == self.active_workspace && !self.closing.contains(handle)
            }));
        let target = preferred.or_else(|| {
            let mut leaves = Vec::new();
            self.layouts.get(&self.active_workspace)?.leaves(&mut leaves);
            leaves.into_iter().rev().find(|handle| self.windows.contains_key(handle))
        });
        if let Some(handle) = target {
            // Closing an app normally causes Windows to reactivate the app
            // that was focused before it. Honor that native choice instead
            // of activating an arbitrary BSP leaf and starting a foreground
            // ping-pong between the OS and the WM.
            if native_foreground != Some(handle) {
                focus_native_window(handle);
            }
            self.focused = Some(handle);
            self.last_focused.insert(self.active_workspace, handle);
            // The surviving window is already visible and stable after the
            // atomic close reflow. One activation attempt is enough here;
            // retry loops are reserved for workspace unpark operations.
            self.pending_workspace_focus = None;
            self.apply_borders();
        } else {
            use windows::Win32::UI::WindowsAndMessaging::{GetShellWindow, SetForegroundWindow};
            self.focused = None;
            let shell = unsafe { GetShellWindow() };
            if !shell.is_invalid() {
                unsafe { let _ = SetForegroundWindow(shell); }
            }
        }
    }

    fn toggle_direction(&mut self) {
        self.direction = match self.direction {
            TilingDirection::Horizontal => TilingDirection::Vertical,
            TilingDirection::Vertical => TilingDirection::Horizontal,
        };
        if let Some(handle) = self.focused {
            self.insertion_directions.insert(handle, self.direction);
        }
    }

    fn resize_focused(&mut self, width_delta: f32, height_delta: f32) {
        let Some(handle) = self.focused else {
            return;
        };
        let Some(root) = self.layouts.get_mut(&self.active_workspace) else { return; };
        let changed_x = width_delta.abs() > f32::EPSILON
            && root.move_boundary_for(handle, TilingDirection::Horizontal, width_delta);
        let changed_y = height_delta.abs() > f32::EPSILON
            && root.move_boundary_for(handle, TilingDirection::Vertical, height_delta);
        if (changed_x || changed_y) && !self.paused {
            self.tile_active_workspace();
        }
    }

    fn directional_neighbor(&self, x: i32, y: i32) -> Option<isize> {
        let focused = self.focused?;
        let rects = self.layout_rects(self.active_workspace);
        let current = rects.iter().find(|(handle, _)| *handle == focused)?.1;
        let center = ((current.left + current.right) / 2, (current.top + current.bottom) / 2);
        rects.into_iter().filter(|(handle, _)| *handle != focused).filter_map(|(handle, rect)| {
            let other = ((rect.left + rect.right) / 2, (rect.top + rect.bottom) / 2);
            let vertical_overlap = current.bottom.min(rect.bottom) - current.top.max(rect.top);
            let horizontal_overlap = current.right.min(rect.right) - current.left.max(rect.left);
            let valid = if x < 0 {
                rect.right <= current.left && vertical_overlap > 0
            } else if x > 0 {
                rect.left >= current.right && vertical_overlap > 0
            } else if y < 0 {
                rect.bottom <= current.top && horizontal_overlap > 0
            } else {
                rect.top >= current.bottom && horizontal_overlap > 0
            };
            if !valid {
                return None;
            }
            let primary = if x < 0 {
                current.left - rect.right
            } else if x > 0 {
                rect.left - current.right
            } else if y < 0 {
                current.top - rect.bottom
            } else {
                rect.top - current.bottom
            };
            let cross = if x != 0 {
                (other.1 - center.1).abs()
            } else {
                (other.0 - center.0).abs()
            };
            Some((primary * 4 + cross, handle))
        }).min_by_key(|(score, _)| *score).map(|(_, handle)| handle)
    }

    fn focus_direction(&mut self, x: i32, y: i32) {
        if let Some(handle) = self.directional_neighbor(x, y) {
            focus_native_window(handle);
            self.focused = Some(handle);
            self.last_focused.insert(self.active_workspace, handle);
            self.pending_workspace_focus = Some((
                self.active_workspace,
                handle,
                Instant::now(),
            ));
        }
    }

    fn move_focused_direction(&mut self, x: i32, y: i32) {
        let Some(focused) = self.focused else { return; };
        let original = self.layouts.get(&self.active_workspace).cloned();
        if let Some(other) = self.directional_neighbor(x, y) {
            if let Some(root) = self.layouts.get_mut(&self.active_workspace) {
                let marker = isize::MIN;
                root.replace_leaf(focused, marker);
                root.replace_leaf(other, focused);
                root.replace_leaf(marker, other);
            }
        } else if let Some(root) = self.layouts.remove(&self.active_workspace) {
            // At an outer edge there is no window to swap with. Lift the focused
            // leaf out of its current subtree and make a new root split in the
            // requested direction, allowing it to escape that subtree's axis.
            if let Some(remaining) = root.remove(focused) {
                let direction = if x != 0 {
                    TilingDirection::Horizontal
                } else {
                    TilingDirection::Vertical
                };
                let focused = LayoutNode::Leaf(focused);
                let (first, second) = if x < 0 || y < 0 {
                    (focused, remaining)
                } else {
                    (remaining, focused)
                };
                self.layouts.insert(
                    self.active_workspace,
                    LayoutNode::Split {
                        direction,
                        ratio: 0.5,
                        first: Box::new(first),
                        second: Box::new(second),
                    },
                );
            } else {
                self.layouts
                    .insert(self.active_workspace, LayoutNode::Leaf(focused));
            }
        }
        if !self.constrain_workspace_to_minimum(self.active_workspace) {
            if let Some(original) = original {
                self.layouts.insert(self.active_workspace, original);
            }
            return;
        }
        self.tile_active_workspace();
    }

    fn tile_active_workspace(&mut self) {
        let _ = self.constrain_workspace_to_minimum(self.active_workspace);
        self.tile_workspace(self.active_workspace);
    }

    fn constrain_workspace_to_minimum(&mut self, workspace: usize) -> bool {
        let Some(area) = self.workspace_area(workspace) else { return false; };
        let Some(mut root) = self.layouts.remove(&workspace) else { return true; };
        let fits = self.constrain_layout_to_minimum(&mut root, area);
        self.layouts.insert(workspace, root);
        fits
    }

    fn constrain_layout_to_minimum(&self, root: &mut LayoutNode, area: LayoutRect) -> bool {
        for _ in 0..16 {
            let mut rects = Vec::new();
            root.rects(area, self.config.window_gap, &mut rects);
            let violation = rects.into_iter().find_map(|(handle, rect)| {
                let (minimum_width, minimum_height) = self.minimum_sizes
                    .get(&handle).copied().unwrap_or((64, 64));
                let placement = window_placement_for_visible_rect(handle, rect);
                let width_shortage = minimum_width - (placement.right - placement.left);
                let height_shortage = minimum_height - (placement.bottom - placement.top);
                (width_shortage > 4 || height_shortage > 4)
                    .then_some((handle, width_shortage.max(0), height_shortage.max(0)))
            });
            let Some((handle, width_shortage, height_shortage)) = violation else {
                return true;
            };
            let mut changed = false;
            if width_shortage > 4 {
                changed |= root.resize_for(
                    handle,
                    TilingDirection::Horizontal,
                    width_shortage as f32 / (area.right - area.left).max(1) as f32,
                );
            }
            if height_shortage > 4 {
                changed |= root.resize_for(
                    handle,
                    TilingDirection::Vertical,
                    height_shortage as f32 / (area.bottom - area.top).max(1) as f32,
                );
            }
            if !changed {
                return false;
            }
        }
        false
    }

    fn find_fitting_insertion(
        &self,
        root: &LayoutNode,
        area: LayoutRect,
        handle: isize,
    ) -> Option<LayoutNode> {
        let mut leaves = Vec::new();
        root.leaves(&mut leaves);
        for direction in [TilingDirection::Horizontal, TilingDirection::Vertical] {
            for target in &leaves {
                let mut candidate = root.clone();
                if candidate.insert_beside(*target, handle, direction, true)
                    && self.constrain_layout_to_minimum(&mut candidate, area)
                {
                    return Some(candidate);
                }
            }
        }
        None
    }

    fn move_workspace_to_monitor(&mut self, x_direction: i32, y_direction: i32) {
        use windows::Win32::{
            Foundation::RECT,
            Graphics::Gdi::{MONITOR_DEFAULTTONEAREST, MonitorFromWindow},
            UI::WindowsAndMessaging::{
                GetWindowRect, SWP_ASYNCWINDOWPOS, SWP_NOACTIVATE, SWP_NOOWNERZORDER,
                SWP_NOZORDER, SetWindowPos,
            },
        };

        let Some(anchor) = self
            .focused
            .filter(|handle| self.windows.get(handle).is_some_and(|window| window.workspace == self.active_workspace))
            .or_else(|| {
                self.windows
                    .values()
                    .find(|window| window.workspace == self.active_workspace)
                    .map(|window| window.handle)
            })
        else {
            return;
        };
        let current = unsafe { MonitorFromWindow(hwnd(anchor), MONITOR_DEFAULTTONEAREST) };
        let monitors = enumerate_monitors();
        let Some((_, source_rect)) = monitors
            .iter()
            .find(|(monitor, _)| *monitor == current.0 as isize)
        else {
            return;
        };
        let source_center = (
            (source_rect.left + source_rect.right) / 2,
            (source_rect.top + source_rect.bottom) / 2,
        );
        let target = monitors
            .iter()
            .filter(|(monitor, rect)| {
                if *monitor == current.0 as isize {
                    return false;
                }
                let center = ((rect.left + rect.right) / 2, (rect.top + rect.bottom) / 2);
                (x_direction < 0 && center.0 < source_center.0)
                    || (x_direction > 0 && center.0 > source_center.0)
                    || (y_direction < 0 && center.1 < source_center.1)
                    || (y_direction > 0 && center.1 > source_center.1)
            })
            .min_by_key(|(_, rect)| {
                let center = ((rect.left + rect.right) / 2, (rect.top + rect.bottom) / 2);
                let dx = center.0 - source_center.0;
                let dy = center.1 - source_center.1;
                dx * dx + dy * dy
            });
        let Some((target_monitor, target_rect)) = target else {
            return;
        };
        let offset = (
            (target_rect.left + target_rect.right - source_rect.left - source_rect.right) / 2,
            (target_rect.top + target_rect.bottom - source_rect.top - source_rect.bottom) / 2,
        );
        for window in self
            .windows
            .values()
            .filter(|window| window.workspace == self.active_workspace && window.floating)
        {
            let mut rect = RECT::default();
            if unsafe { GetWindowRect(hwnd(window.handle), &mut rect) }.is_ok() {
                unsafe {
                    let _ = SetWindowPos(
                        hwnd(window.handle),
                        None,
                        rect.left + offset.0,
                        rect.top + offset.1,
                        rect.right - rect.left,
                        rect.bottom - rect.top,
                        SWP_ASYNCWINDOWPOS | SWP_NOACTIVATE | SWP_NOOWNERZORDER | SWP_NOZORDER,
                    );
                }
            }
        }
        self.workspace_monitors.insert(self.active_workspace, *target_monitor);
        self.tile_active_workspace();
    }

    fn workspace_area(&self, workspace: usize) -> Option<LayoutRect> {
        use windows::Win32::{
            Graphics::Gdi::{GetMonitorInfoW, HMONITOR, MONITORINFO, MONITOR_DEFAULTTONEAREST, MonitorFromWindow},
        };
        let monitor = self.workspace_monitors.get(&workspace).copied().or_else(|| {
            let mut leaves = Vec::new();
            self.layouts.get(&workspace)?.leaves(&mut leaves);
            leaves.first().map(|handle| unsafe { MonitorFromWindow(hwnd(*handle), MONITOR_DEFAULTTONEAREST) }.0 as isize)
        })?;
        let mut monitor_info = MONITORINFO {
            cbSize: std::mem::size_of::<MONITORINFO>() as u32,
            ..Default::default()
        };
        if !unsafe { GetMonitorInfoW(HMONITOR(monitor as *mut c_void), &mut monitor_info) }.as_bool() {
            return None;
        }
        let mut area = monitor_info.rcWork;
        if monitor_info.dwFlags != 0 {
            area.top = area.top.max(monitor_info.rcMonitor.top + BAR_HEIGHT);
        }
        Some(LayoutRect {
            left: area.left + self.config.window_gap,
            top: area.top + self.config.window_gap,
            right: area.right - self.config.window_gap,
            bottom: area.bottom - self.config.window_gap,
        })
    }

    fn layout_rects(&self, workspace: usize) -> Vec<(isize, LayoutRect)> {
        let mut output = Vec::new();
        if let (Some(root), Some(area)) = (self.layouts.get(&workspace), self.workspace_area(workspace)) {
            root.rects(area, self.config.window_gap, &mut output);
        }
        output
    }

    fn tile_workspace(&self, workspace: usize) {
        use windows::Win32::UI::WindowsAndMessaging::{
            BeginDeferWindowPos, DeferWindowPos, EndDeferWindowPos, HWND_NOTOPMOST,
            SWP_NOACTIVATE, SWP_NOOWNERZORDER, SWP_NOSENDCHANGING, SetWindowPos,
        };
        let placements = self
            .layout_rects(workspace)
            .into_iter()
            .filter(|(handle, _)| {
                self.windows.get(handle).is_some_and(|window| {
                    !window.floating
                        && window.fullscreen_restore.is_none()
                        && window.maximize_restore.is_none()
                })
            })
            .map(|(handle, rect)| (handle, window_placement_for_visible_rect(handle, rect)))
            .collect::<Vec<_>>();

        let mut applied_as_batch = false;
        if !placements.is_empty() {
            unsafe {
                if let Ok(mut batch) = BeginDeferWindowPos(placements.len() as i32) {
                    let mut valid = true;
                    for (handle, placement) in &placements {
                        match DeferWindowPos(
                            batch,
                            hwnd(*handle),
                            HWND_NOTOPMOST,
                            placement.left,
                            placement.top,
                            (placement.right - placement.left).max(64),
                            (placement.bottom - placement.top).max(64),
                            SWP_NOACTIVATE | SWP_NOOWNERZORDER | SWP_NOSENDCHANGING,
                        ) {
                            Ok(next) => batch = next,
                            Err(_) => {
                                valid = false;
                                break;
                            }
                        }
                    }
                    if valid {
                        applied_as_batch = EndDeferWindowPos(batch).is_ok();
                    }
                }
            }
        }
        if !applied_as_batch {
            for (handle, placement) in placements {
                unsafe {
                    let _ = SetWindowPos(
                        hwnd(handle),
                        HWND_NOTOPMOST,
                        placement.left,
                        placement.top,
                        (placement.right - placement.left).max(64),
                        (placement.bottom - placement.top).max(64),
                        SWP_NOACTIVATE | SWP_NOOWNERZORDER | SWP_NOSENDCHANGING,
                    );
                }
            }
        }
        self.apply_borders();
    }

    fn reconcile_tiled_constraints(&mut self) -> bool {
        if self.workspace_area(self.active_workspace).is_none() { return false; }
        let expected = self.layout_rects(self.active_workspace);
        let single_tile = expected.len() == 1;
        let mut adjustment = None;
        for (handle, rect) in &expected {
            let (handle, rect) = (*handle, *rect);
            let Some(actual) = visible_window_rect(handle) else { continue; };
            let width_growth = (actual.right - actual.left) - (rect.right - rect.left);
            let height_growth = (actual.bottom - actual.top) - (rect.bottom - rect.top);
            let stale_single_tile = single_tile
                && ((actual.left - rect.left).abs() > 4
                    || (actual.top - rect.top).abs() > 4
                    || (actual.right - rect.right).abs() > 4
                    || (actual.bottom - rect.bottom).abs() > 4);
            if stale_single_tile {
                // Firefox-family browsers can apply their persisted window
                // rectangle shortly after the WM's initial placement. With no
                // sibling there is no split ratio to absorb or protect, so the
                // sole tiled window must always occupy the complete workspace
                // instead of being left at that stale restored size.
                self.pending_growth.remove(&handle);
                self.tile_active_workspace();
                return true;
            }
            // Only absorb app-enforced growth. Shrinkage is normally a transient
            // placement frame and should still be corrected to the tree geometry.
            if width_growth > 4 || height_growth > 4 {
                // Apps like Zen/Firefox can bounce through several internal
                // resize steps while they settle (e.g. during startup), each
                // one slightly bigger than the last. Absorbing and retiling
                // on every single tick chased that moving target and visibly
                // fought with neighboring windows the whole time it took to
                // settle. Observe a short sequence and retain its largest
                // enforced size before resolving it once. Pixel-identical
                // samples are deliberately unnecessary: Firefox can
                // oscillate slightly, which otherwise prevents an impossible
                // tile from ever being moved away.
                let outer = window_placement_for_visible_rect(handle, actual);
                let observed = (outer.right - outer.left, outer.bottom - outer.top);
                let pending = self.pending_growth.entry(handle).or_insert((0, 0, 0));
                pending.0 = pending.0.max(observed.0);
                pending.1 = pending.1.max(observed.1);
                pending.2 = pending.2.saturating_add(1);
                if pending.2 < 3 {
                    continue;
                }
                adjustment = Some((handle, (pending.0, pending.1)));
                break;
            } else {
                self.pending_growth.remove(&handle);
            }
        }
        let Some((handle, inferred_minimum)) = adjustment else { return false; };
        self.pending_growth.remove(&handle);
        let minimum = self.minimum_sizes.entry(handle).or_insert((64, 64));
        minimum.0 = minimum.0.max(inferred_minimum.0);
        minimum.1 = minimum.1.max(inferred_minimum.1);

        let workspace = self.active_workspace;
        let Some(area) = self.workspace_area(workspace) else { return false; };
        let Some(original) = self.layouts.get(&workspace).cloned() else { return false; };

        // First preserve the current tree and adjust its ratios. If that
        // cannot satisfy the newly learned minimum, try every useful row/
        // column insertion before deciding that another workspace is needed.
        let mut fitted = original.clone();
        if self.constrain_layout_to_minimum(&mut fitted, area) {
            self.layouts.insert(workspace, fitted);
            self.tile_active_workspace();
            return true;
        }

        if let Some(remaining) = original.clone().remove(handle)
            && let Some(alternate) = self.find_fitting_insertion(&remaining, area, handle)
        {
            self.layouts.insert(workspace, alternate);
            self.tile_active_workspace();
            return true;
        }

        // The window genuinely cannot coexist with the other tiles. Move it
        // to a fresh workspace rather than repeatedly fighting its enforced
        // dimensions. Follow a foreground/active launch; otherwise leave the
        // user on the current workspace and park the relocated window.
        let should_follow = self.focused == Some(handle)
            || self.last_foreground_event.is_some_and(|(foreground, received)| {
                foreground == handle && received.elapsed() < Duration::from_secs(1)
            });
        let destination = self.next_available_workspace();
        self.relocate_window_to_workspace(handle, destination);
        if should_follow {
            self.focus_workspace(destination);
        } else {
            self.park_window(handle);
            self.sync_taskbar_visibility();
            self.focus_active_replacement();
        }
        WINDOW_EVENT_DIRTY.store(true, Ordering::Release);
        true
    }



    fn update_snap_target(&mut self) {
        use windows::Win32::Foundation::POINT;
        use windows::Win32::UI::WindowsAndMessaging::GetCursorPos;
        let Some(dragged) = self.dragging else { self.snap_target = None; return; };
        if self.drag_size_delta(dragged).is_some_and(|(width, height)| width.abs() > 8 || height.abs() > 8) {
            self.snap_target = None;
            return;
        }
        let mut point = POINT::default();
        if unsafe { GetCursorPos(&mut point) }.is_err() { self.snap_target = None; return; }
        if self.snap_target.as_ref().is_some_and(|target| {
            point.x >= target.preview.left
                && point.x < target.preview.right
                && point.y >= target.preview.top
                && point.y < target.preview.bottom
        }) {
            return;
        }
        let current_layout = self.layout_rects(self.active_workspace);
        let hovered = current_layout.iter().copied()
            .find(|(handle, rect)| *handle != dragged && point.x >= rect.left && point.x < rect.right && point.y >= rect.top && point.y < rect.bottom);
        if let Some((target, rect)) = hovered {
                let cx = (rect.left + rect.right) / 2;
                let cy = (rect.top + rect.bottom) / 2;
                let nx = (point.x - cx).abs() as f32 / (rect.right - rect.left).max(1) as f32;
                let ny = (point.y - cy).abs() as f32 / (rect.bottom - rect.top).max(1) as f32;
                let (direction, after) = if nx >= ny {
                    let after = point.x >= cx;
                    (TilingDirection::Horizontal, after)
                } else {
                    let after = point.y >= cy;
                    (TilingDirection::Vertical, after)
                };
                let placements = self.preview_snap_layout(dragged, target, direction, after);
                if placements.is_empty() {
                    self.snap_target = None;
                    return;
                }
                let preview = placements.iter().find(|(handle, _)| *handle == dragged)
                    .map(|(_, rect)| *rect)
                    .unwrap_or(rect);
                self.snap_target = Some(SnapTarget {
                    target,
                    direction,
                    after,
                    changes_layout: true,
                    preview,
                    placements,
                });
        } else {
            let preview = current_layout.iter().find(|(handle, _)| *handle == dragged)
                .map(|(_, preview)| *preview);
            self.snap_target = preview.map(|preview| SnapTarget {
                    target: dragged,
                    direction: self.direction,
                    after: true,
                    changes_layout: false,
                    preview,
                    placements: current_layout,
                });
        }
    }

    fn preview_snap_layout(
        &self,
        dragged: isize,
        target: isize,
        direction: TilingDirection,
        after: bool,
    ) -> Vec<(isize, LayoutRect)> {
        let Some(area) = self.workspace_area(self.active_workspace) else {
            return Vec::new();
        };
        let Some(root) = self.layouts.get(&self.active_workspace).cloned() else {
            return Vec::new();
        };
        let Some(mut root) = root.remove(dragged) else {
            return Vec::new();
        };
        if !root.insert_beside(target, dragged, direction, after) {
            return Vec::new();
        }
        if !self.constrain_layout_to_minimum(&mut root, area) {
            return Vec::new();
        }
        let mut rects = Vec::new();
        root.rects(area, self.config.window_gap, &mut rects);
        rects
    }

    fn apply_snap_preview_layout(&self) {
        use windows::Win32::UI::WindowsAndMessaging::{
            SWP_NOACTIVATE, SWP_NOOWNERZORDER, SWP_NOSENDCHANGING, SWP_NOZORDER, SetWindowPos,
        };
        let Some(dragged) = self.dragging else { return; };
        let Some(target) = self.snap_target.as_ref() else { return; };
        for (handle, rect) in &target.placements {
            if *handle == dragged { continue; }
            let placement = window_placement_for_visible_rect(*handle, *rect);
            unsafe {
                let _ = SetWindowPos(
                    hwnd(*handle),
                    None,
                    placement.left,
                    placement.top,
                    (placement.right - placement.left).max(64),
                    (placement.bottom - placement.top).max(64),
                    SWP_NOACTIVATE | SWP_NOOWNERZORDER | SWP_NOSENDCHANGING | SWP_NOZORDER,
                );
            }
        }
        self.apply_borders();
    }

    fn finish_drag(&mut self) {
        let Some(handle) = self.dragging.take() else { return; };
        if let Some((width, height)) = self.drag_size_delta(handle)
            && (width.abs() > 8 || height.abs() > 8)
        {
            if let Some(area) = self.workspace_area(self.active_workspace)
                && let Some(root) = self.layouts.get_mut(&self.active_workspace)
            {
                if width.abs() > 8 {
                    root.resize_for(
                        handle,
                        TilingDirection::Horizontal,
                        width as f32 / (area.right - area.left).max(1) as f32,
                    );
                }
                if height.abs() > 8 {
                    root.resize_for(
                        handle,
                        TilingDirection::Vertical,
                        height as f32 / (area.bottom - area.top).max(1) as f32,
                    );
                }
            }
            self.snap_target = None;
            if !self.paused { self.tile_active_workspace(); }
            return;
        }
        if let Some(target) = self.snap_target.take().filter(|target| target.changes_layout) {
            let workspace = self.windows.get(&target.target).map_or(self.active_workspace, |window| window.workspace);
            if let Some(window) = self.windows.get_mut(&handle) { window.workspace = workspace; window.floating = false; }
            self.insert_into_layout(workspace, handle, Some(target.target), Some(target.direction), target.after);
        }
        if !self.paused { self.tile_active_workspace(); }
    }

    fn drag_size_delta(&self, handle: isize) -> Option<(i32, i32)> {
        let expected = self.layout_rects(self.active_workspace).into_iter()
            .find(|(candidate, _)| *candidate == handle)?.1;
        let actual = visible_window_rect(handle)?;
        Some((
            (actual.right - actual.left) - (expected.right - expected.left),
            (actual.bottom - actual.top) - (expected.bottom - expected.top),
        ))
    }

    fn apply_borders(&self) {
        use windows::Win32::Graphics::Dwm::{DWMWA_BORDER_COLOR, DwmSetWindowAttribute};

        let accent = native_accent_colorref();
        // COLORREF is 0x00BBGGRR: #767F84 -> 0x00847F76.
        let unfocused = 0x0084_7f76_u32;
        // DWM's documented sentinel restores the system-selected border,
        // which is effectively invisible against a window that already
        // covers the whole monitor (native maximize / fullscreen).
        let default_border = 0xffff_ffff_u32;
        for window in self.windows.values() {
            let color = if window.maximize_restore.is_some() || window.fullscreen_restore.is_some() {
                default_border
            } else if self.focused == Some(window.handle) {
                accent
            } else {
                unfocused
            };
            unsafe {
                let _ = DwmSetWindowAttribute(
                    hwnd(window.handle),
                    DWMWA_BORDER_COLOR,
                    &color as *const _ as *const c_void,
                    std::mem::size_of_val(&color) as u32,
                );
            }
        }
    }

    fn apply_foreground_event(&mut self, handle: isize) {
        if SEARCH_INPUT_ACTIVE.load(Ordering::Acquire) {
            self.pending_workspace_focus = None;
            return;
        }
        // Minimizing (e.g. clicking the active window's taskbar icon) makes
        // Windows activate the next window in z-order, which can be a parked
        // window of another workspace. That is a fallback, not a user choice:
        // don't switch workspaces for it, and don't undo the minimize.
        if self.windows.get(&handle).is_some_and(|window| window.workspace != self.active_workspace) {
            use windows::Win32::UI::WindowsAndMessaging::IsIconic;
            let recent_local = self
                .last_local_foreground
                .filter(|(_, at)| at.elapsed() < Duration::from_secs(3))
                .map(|(local, _)| local);
            let minimized = [recent_local, self.focused, self.pending_workspace_focus.map(|(_, pending, _)| pending)]
                .into_iter()
                .flatten()
                .find(|candidate| {
                    self.windows.get(candidate).is_some_and(|window| window.workspace == self.active_workspace)
                        && unsafe { IsIconic(hwnd(*candidate)) }.as_bool()
                });
            if let Some(minimized) = minimized {
                self.pending_workspace_focus = None;
                self.focus_after_local_minimize(minimized);
                return;
            }
        }
        if self.suppress_close_induced_workspace_activation(handle) {
            return;
        }
        if self.is_stale_cross_workspace_activation(handle) {
            return;
        }
        if self.recently_parked.get(&handle).is_some_and(|parked_at| {
            parked_at.elapsed() < Duration::from_millis(600)
        }) {
            // `SetWindowPos`'s off-screen move in `park_window` can make Windows
            // briefly re-foreground the window being parked before our own
            // `focus_native_window` call lands on the real target. That is
            // stale noise from our own transition, not a new user activation -
            // but a genuine taskbar click on this same (now hidden) window can
            // also land inside this window, so only actually suppress it when
            // the OS's live foreground window has already moved on to
            // something else; if this handle really is the current foreground
            // window, the user's click won a real activation and must be
            // honored (e.g. redirected or used to spawn a new Explorer window).
            use windows::Win32::UI::WindowsAndMessaging::GetForegroundWindow;
            let live_foreground = unsafe { GetForegroundWindow() }.0 as isize;
            if live_foreground != handle {
                return;
            }
        }
        if let Some((pending_workspace, pending, _)) = self.pending_workspace_focus
            && pending != handle
        {
            let event_workspace = self.windows.get(&handle).map(|window| window.workspace);
            if event_workspace.is_some_and(|workspace| workspace != pending_workspace) {
                // Parking/unparking and taskbar updates can foreground an old
                // workspace window while the requested workspace is settling.
                // It is part of the same transaction, not a new user choice.
                return;
            }
            if event_workspace == Some(pending_workspace) {
                // The user selected a different window inside the destination
                // workspace; that is a legitimate replacement for our target.
                self.pending_workspace_focus = None;
            }
        }
        self.last_foreground_event = Some((handle, Instant::now()));
        if self.windows.get(&handle).is_some_and(|window| window.workspace == self.active_workspace) {
            self.last_local_foreground = Some((handle, Instant::now()));
        }
        if self.activate_external_window(handle) {
            return;
        }
        let focused = self.windows.get(&handle)
            .filter(|window| window.workspace == self.active_workspace)
            .map(|window| window.handle);
        self.focused = focused;
        if let Some(handle) = focused {
            self.last_focused.insert(self.active_workspace, handle);
        }
        // The foreground WinEvent can arrive just before GetForegroundWindow is
        // updated. Applying its HWND directly avoids leaving the old accent border
        // visible until the fallback scan runs.
        self.apply_borders();
    }

    /// A foreground/restore notification for a window of another workspace is
    /// only a deliberate request when that window really is the foreground
    /// window now. Parked windows get transiently activated by Windows (z-order
    /// fallbacks after minimize, repeated taskbar clicks) while the user's
    /// window keeps or regains focus; switching workspaces for those is the
    /// "random jump".
    fn is_stale_cross_workspace_activation(&self, handle: isize) -> bool {
        use windows::Win32::UI::WindowsAndMessaging::GetForegroundWindow;
        self.windows.get(&handle).is_some_and(|window| window.workspace != self.active_workspace)
            && unsafe { GetForegroundWindow() }.0 as isize != handle
    }

    fn focus_after_local_minimize(&mut self, minimized: isize) {
        use windows::Win32::UI::WindowsAndMessaging::{GetShellWindow, IsIconic, SetForegroundWindow};
        let replacement = self
            .last_focused
            .get(&self.active_workspace)
            .copied()
            .into_iter()
            .chain(
                self.windows
                    .values()
                    .filter(|window| window.workspace == self.active_workspace)
                    .map(|window| window.handle),
            )
            .find(|candidate| {
                *candidate != minimized
                    && self.windows.get(candidate).is_some_and(|window| {
                        window.workspace == self.active_workspace && !self.closing.contains(candidate)
                    })
                    && !unsafe { IsIconic(hwnd(*candidate)) }.as_bool()
            });
        if let Some(local) = replacement {
            focus_native_window(local);
            self.focused = Some(local);
            self.last_focused.insert(self.active_workspace, local);
            self.last_foreground_event = Some((local, Instant::now()));
            self.pending_workspace_focus = Some((self.active_workspace, local, Instant::now()));
        } else {
            self.focused = None;
            self.last_foreground_event = None;
            let shell = unsafe { GetShellWindow() };
            if !shell.is_invalid() {
                unsafe { let _ = SetForegroundWindow(shell); }
            }
        }
        self.apply_borders();
    }

    /// Reveals a managed window that an external UI surface (taskbar, tray,
    /// notification, app IPC) activated from another workspace.
    fn activate_external_window(&mut self, handle: isize) -> bool {
        let Some(workspace) = self.windows.get(&handle).map(|window| window.workspace) else {
            return false;
        };
        if workspace == self.active_workspace {
            return false;
        }
        if self.redirect_hidden_app_activation(handle) {
            return true;
        }
        if self.workspace_switch_guard.is_some_and(|(target, started)| {
            target == self.active_workspace
                && workspace != target
                && started.elapsed() < Duration::from_millis(650)
        }) {
            return true;
        }
        self.last_focused.insert(workspace, handle);
        self.focus_workspace(workspace);
        self.focused = Some(handle);
        self.pending_workspace_focus = Some((workspace, handle, Instant::now()));
        self.apply_borders();
        true
    }

    /// Windows keeps taskbar groups global even after an individual HWND tab
    /// is removed with ITaskbarList. A repeated click can therefore activate
    /// a hidden sibling from another Overbar workspace. Keep that activation
    /// local when this workspace already owns an instance of the same app.
    /// Explorer is single-instance at the process level, so if there is no
    /// local Explorer window, explicitly ask it for a new window instead.
    fn redirect_hidden_app_activation(&mut self, handle: isize) -> bool {
        if !self.taskbar_hidden.contains(&handle) {
            return false;
        }
        let Some(process) = self.windows.get(&handle).map(|window| {
            window.process_name.trim_end_matches(".exe").to_ascii_lowercase()
        }) else {
            return false;
        };
        let local = self
            .last_focused
            .get(&self.active_workspace)
            .copied()
            .filter(|candidate| {
                self.windows.get(candidate).is_some_and(|window| {
                    window.workspace == self.active_workspace
                        && window.process_name.trim_end_matches(".exe").eq_ignore_ascii_case(&process)
                })
            })
            .or_else(|| {
                self.windows.values().find_map(|window| {
                    (window.workspace == self.active_workspace
                        && window.process_name.trim_end_matches(".exe").eq_ignore_ascii_case(&process))
                        .then_some(window.handle)
                })
            });
        if let Some(local) = local {
            focus_native_window(local);
            self.focused = Some(local);
            self.last_focused.insert(self.active_workspace, local);
            self.last_foreground_event = Some((local, Instant::now()));
            self.pending_workspace_focus = Some((self.active_workspace, local, Instant::now()));
            self.apply_borders();
            return true;
        }

        if process == "explorer" {
            // The pending flag normally gates re-spawns until `refresh()`
            // discovers the new window, but if that somehow never happens
            // (e.g. the spawn failed) don't block Explorer relaunches forever.
            if self.pending_explorer_relaunch.is_some()
                && self.last_explorer_relaunch.elapsed() >= Duration::from_secs(8)
            {
                self.pending_explorer_relaunch = None;
            }
            let will_relaunch = self.pending_explorer_relaunch.is_none()
                && self.last_explorer_relaunch.elapsed() >= Duration::from_millis(750);
            if will_relaunch {
                self.last_explorer_relaunch = Instant::now();
                // Remember which workspace asked for the window: Explorer can
                // take seconds to show it, by which point the user may have
                // switched away and it must not land on the wrong workspace.
                self.pending_explorer_relaunch = Some(self.active_workspace);
                // Overbar runs elevated, and an elevated explorer.exe cannot
                // hand the request to the user's (non-elevated) shell, so it
                // is flaky or never opens a window. Folder paths via
                // ShellExecute reuse an already-open window of that folder.
                // Running plain `explorer.exe` with the shell's own token
                // behaves like the taskbar button: always a new default window.
                if spawn_unelevated_explorer().is_err() {
                    use windows::{
                        Win32::UI::{Shell::ShellExecuteW, WindowsAndMessaging::SW_SHOWNORMAL},
                        core::{PCWSTR, w},
                    };
                    let _ = unsafe {
                        ShellExecuteW(None, w!("open"), w!("explorer.exe"), PCWSTR::null(), PCWSTR::null(), SW_SHOWNORMAL)
                    };
                }
                WINDOW_EVENT_DIRTY.store(true, Ordering::Release);
            }
            // Never let the hidden Explorer HWND pull this workspace away
            // while its new local window is being created and discovered.
            if let Some(local) = self.preferred_workspace_window(self.active_workspace) {
                focus_native_window(local);
                self.last_foreground_event = Some((local, Instant::now()));
                self.pending_workspace_focus = Some((self.active_workspace, local, Instant::now()));
            } else {
                self.last_foreground_event = None;
                use windows::Win32::UI::WindowsAndMessaging::{GetShellWindow, SetForegroundWindow};
                let shell = unsafe { GetShellWindow() };
                if !shell.is_invalid() {
                    unsafe { let _ = SetForegroundWindow(shell); }
                }
            }
            return true;
        }

        false
    }

    fn note_window_departure(&mut self, handle: isize) {
        if let Some(window) = self.windows.get(&handle)
            && window.workspace == self.active_workspace
        {
            self.last_workspace_departure = Some((window.workspace, Instant::now()));
        }
    }

    fn suppress_close_induced_workspace_activation(&self, handle: isize) -> bool {
        let Some(target_workspace) = self.windows.get(&handle).map(|window| window.workspace) else {
            return false;
        };
        target_workspace != self.active_workspace
            && self.last_workspace_departure.is_some_and(|(workspace, occurred)| {
                workspace == self.active_workspace
                    && occurred.elapsed() < Duration::from_millis(350)
            })
    }

    fn restore_windows(&self) {
        use windows::Win32::{
            Graphics::Dwm::{DWMWA_BORDER_COLOR, DwmSetWindowAttribute},
            UI::WindowsAndMessaging::{
                GWL_STYLE, SWP_FRAMECHANGED, SWP_NOACTIVATE, SWP_NOOWNERZORDER,
                SWP_NOSENDCHANGING, SWP_NOZORDER, SetWindowLongW, SetWindowPos,
            },
        };

        // DWM's documented sentinel restores the system-selected border color.
        let default_border = 0xffff_ffff_u32;
        for window in self.windows.values() {
            if window.owner.is_none() && self.taskbar_hidden.contains(&window.handle) {
                set_native_taskbar_tab_visible(window.handle, true);
            }
            unsafe {
                set_managed_window_transitions(window.handle, false);
                if let Some(restore) = &window.fullscreen_restore {
                    SetWindowLongW(hwnd(window.handle), GWL_STYLE, restore.style);
                    let _ = SetWindowPos(
                        hwnd(window.handle),
                        None,
                        restore.rect.0,
                        restore.rect.1,
                        restore.rect.2 - restore.rect.0,
                        restore.rect.3 - restore.rect.1,
                        SWP_FRAMECHANGED
                            | SWP_NOACTIVATE
                            | SWP_NOOWNERZORDER
                            | SWP_NOZORDER,
                    );
                } else if let Some(restore) = self.parked_rects.get(&window.handle) {
                    let _ = SetWindowPos(
                        hwnd(window.handle),
                        None,
                        restore.left,
                        restore.top,
                        (restore.right - restore.left).max(64),
                        (restore.bottom - restore.top).max(64),
                        SWP_NOACTIVATE
                            | SWP_NOOWNERZORDER
                            | SWP_NOSENDCHANGING
                            | SWP_NOZORDER,
                    );
                }
                set_window_cloaked(window.handle, false);
                let _ = DwmSetWindowAttribute(
                    hwnd(window.handle),
                    DWMWA_BORDER_COLOR,
                    &default_border as *const _ as *const c_void,
                    std::mem::size_of_val(&default_border) as u32,
                );
            }
        }
    }

    fn state(&self) -> WorkspacesState {
        let mut apps = self
            .windows
            .values()
            .map(|window| AppEntry {
                window_id: window.handle.to_string(),
                window_handle: Some(window.handle),
                title: window.title.clone(),
                process_name: window.process_name.clone(),
                workspace: window.workspace.to_string(),
            })
            .collect::<Vec<_>>();
        apps.sort_by_key(|app| (app.workspace.parse::<usize>().unwrap_or(0), app.title.clone()));
        let workspace_numbers = self
            .windows
            .values()
            .map(|window| window.workspace)
            .chain(std::iter::once(self.active_workspace))
            .collect::<BTreeSet<_>>();
        let active = workspace_numbers
            .iter()
            .position(|workspace| *workspace == self.active_workspace)
            .unwrap_or(0);
        WorkspacesState {
            items: workspace_numbers
                .into_iter()
                .map(|number| WorkspaceEntry {
                    name: number.to_string(),
                    active: number == self.active_workspace,
                })
                .collect(),
            active,
            apps,
        }
    }

    fn publish(&mut self, sender: &Sender<WindowManagerUpdate>, ctx: &Context, force: bool) -> bool {
        let state = self.state();
        if force || self.last_published.as_ref() != Some(&state) {
            self.last_published = Some(state.clone());
            if sender
                .send(WindowManagerUpdate::Workspaces(state))
                .is_err()
            {
                return false;
            }
            ctx.request_repaint();
        }
        true
    }
}

#[cfg(target_os = "windows")]
struct SnapPreviewWindow {
    handle: windows::Win32::Foundation::HWND,
    brush: windows::Win32::Graphics::Gdi::HBRUSH,
}

#[cfg(target_os = "windows")]
impl SnapPreviewWindow {
    fn new() -> Option<Self> {
        use windows::{core::PCWSTR, Win32::{
            Foundation::{COLORREF, HINSTANCE, HWND},
            Graphics::Gdi::CreateSolidBrush,
            System::LibraryLoader::GetModuleHandleW,
            UI::WindowsAndMessaging::{
                CreateWindowExW, DefWindowProcW, RegisterClassW, SetLayeredWindowAttributes,
                LWA_ALPHA, WNDCLASSW, WS_EX_LAYERED, WS_EX_NOACTIVATE, WS_EX_TOOLWINDOW,
                WS_EX_TRANSPARENT, WS_POPUP,
            },
        }};
        unsafe extern "system" fn proc(
            hwnd: HWND,
            message: u32,
            wparam: windows::Win32::Foundation::WPARAM,
            lparam: windows::Win32::Foundation::LPARAM,
        ) -> windows::Win32::Foundation::LRESULT {
            unsafe { DefWindowProcW(hwnd, message, wparam, lparam) }
        }
        let class_name = "OverbarSnapPreview\0".encode_utf16().collect::<Vec<_>>();
        let instance = unsafe { GetModuleHandleW(None).ok()? };
        let brush = unsafe { CreateSolidBrush(COLORREF(native_accent_colorref())) };
        let class = WNDCLASSW {
            lpfnWndProc: Some(proc),
            hInstance: HINSTANCE(instance.0),
            hbrBackground: brush,
            lpszClassName: PCWSTR(class_name.as_ptr()),
            ..Default::default()
        };
        unsafe { RegisterClassW(&class); }
        let handle = unsafe {
            CreateWindowExW(
                WS_EX_LAYERED | WS_EX_TRANSPARENT | WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE,
                PCWSTR(class_name.as_ptr()),
                PCWSTR(class_name.as_ptr()),
                WS_POPUP,
                0, 0, 0, 0,
                None, None, instance, None,
            ).ok()?
        };
        unsafe { SetLayeredWindowAttributes(handle, COLORREF(0), 92, LWA_ALPHA).ok()?; }
        Some(Self { handle, brush })
    }

    fn show(&self, rect: LayoutRect) {
        use windows::Win32::{
            Graphics::Gdi::{InvalidateRect, UpdateWindow},
            UI::WindowsAndMessaging::{
                HWND_TOPMOST, SW_SHOWNOACTIVATE, SWP_NOACTIVATE, SWP_SHOWWINDOW, SetWindowPos,
                ShowWindow,
            },
        };
        unsafe {
            let _ = SetWindowPos(
                self.handle, HWND_TOPMOST, rect.left, rect.top,
                (rect.right - rect.left).max(1), (rect.bottom - rect.top).max(1),
                SWP_NOACTIVATE | SWP_SHOWWINDOW,
            );
            let _ = ShowWindow(self.handle, SW_SHOWNOACTIVATE);
            let _ = InvalidateRect(self.handle, None, true);
            let _ = UpdateWindow(self.handle);
        }
    }

    fn hide(&self) {
        use windows::Win32::UI::WindowsAndMessaging::{SW_HIDE, ShowWindow};
        unsafe { let _ = ShowWindow(self.handle, SW_HIDE); }
    }
}

#[cfg(target_os = "windows")]
#[derive(Default)]
struct SnapPreviewOverlay {
    windows: Vec<SnapPreviewWindow>,
}

#[cfg(target_os = "windows")]
impl SnapPreviewOverlay {
    fn show(&mut self, rects: &[LayoutRect]) {
        while self.windows.len() < rects.len() {
            let Some(window) = SnapPreviewWindow::new() else { break; };
            self.windows.push(window);
        }
        for (index, window) in self.windows.iter().enumerate() {
            if let Some(rect) = rects.get(index) {
                window.show(*rect);
            } else {
                window.hide();
            }
        }
    }

    fn hide(&self) {
        for window in &self.windows {
            window.hide();
        }
    }

    fn clear(&mut self) {
        self.hide();
        self.windows.clear();
    }
}

#[cfg(target_os = "windows")]
impl Drop for SnapPreviewWindow {
    fn drop(&mut self) {
        use windows::Win32::{Graphics::Gdi::DeleteObject, UI::WindowsAndMessaging::DestroyWindow};
        unsafe {
            let _ = DestroyWindow(self.handle);
            let _ = DeleteObject(self.brush);
        }
    }
}

#[cfg(target_os = "windows")]
fn configured_hotkeys(
    config: &WmConfig,
) -> Vec<(i32, windows::Win32::UI::Input::KeyboardAndMouse::HOT_KEY_MODIFIERS, u32)> {
    let actions = [
        (201, "Focus left"), (202, "Focus right"),
        (208, "Focus up"), (209, "Focus down"),
        (203, "Move left"), (204, "Move right"),
        (210, "Move up"), (211, "Move down"),
        (205, "Tiling direction"), (212, "Set Tiled"),
        (206, "Cycle tiled/floating"),
        (213, "Fullscreen"), (214, "Minimize"), (215, "Close"),
        (216, "Previous workspace"), (217, "Next workspace"),
        (218, "Recent workspace"), (219, "Retile"), (234, "Resize mode"),
        (237, "Center floating window"),
    ];
    actions.into_iter().filter_map(|(id, name)| {
        parse_hotkey(config.keybindings.get(name)?).map(|(modifiers, key)| (id, modifiers, key))
    }).collect()
}

#[cfg(target_os = "windows")]
fn fixed_hotkey_aliases(
) -> Vec<(i32, windows::Win32::UI::Input::KeyboardAndMouse::HOT_KEY_MODIFIERS, u32)> {
    use windows::Win32::UI::Input::KeyboardAndMouse::{
        MOD_ALT, MOD_NOREPEAT, MOD_SHIFT, VK_DOWN, VK_LEFT, VK_RIGHT, VK_UP,
    };
    vec![
        (207, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'P' as u32),
        (220, MOD_ALT | MOD_NOREPEAT, VK_LEFT.0 as u32),
        (221, MOD_ALT | MOD_NOREPEAT, VK_RIGHT.0 as u32),
        (222, MOD_ALT | MOD_NOREPEAT, VK_UP.0 as u32),
        (223, MOD_ALT | MOD_NOREPEAT, VK_DOWN.0 as u32),
        (224, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, VK_LEFT.0 as u32),
        (225, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, VK_RIGHT.0 as u32),
        (226, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, VK_UP.0 as u32),
        (227, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, VK_DOWN.0 as u32),
        (230, MOD_ALT | MOD_NOREPEAT, b'U' as u32),
        (231, MOD_ALT | MOD_NOREPEAT, b'P' as u32),
        (232, MOD_ALT | MOD_NOREPEAT, b'O' as u32),
        (233, MOD_ALT | MOD_NOREPEAT, b'I' as u32),
        (235, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'E' as u32),
        (236, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'R' as u32),
        (240, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'A' as u32),
        (241, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'F' as u32),
        (242, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'D' as u32),
        (243, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'S' as u32),
    ]
}

#[cfg(target_os = "windows")]
fn parse_hotkey(
    binding: &str,
) -> Option<(windows::Win32::UI::Input::KeyboardAndMouse::HOT_KEY_MODIFIERS, u32)> {
    use windows::Win32::UI::Input::KeyboardAndMouse::{
        MOD_ALT, MOD_CONTROL, MOD_NOREPEAT, MOD_SHIFT, MOD_WIN,
        VK_DOWN, VK_ESCAPE, VK_LEFT, VK_RETURN, VK_RIGHT, VK_SPACE, VK_UP,
    };
    let mut modifiers = MOD_NOREPEAT;
    let mut key = None;
    for part in binding.split('+').map(str::trim).filter(|part| !part.is_empty()) {
        match part.to_ascii_lowercase().as_str() {
            "alt" => modifiers |= MOD_ALT,
            "shift" => modifiers |= MOD_SHIFT,
            "ctrl" | "control" => modifiers |= MOD_CONTROL,
            "win" | "super" => modifiers |= MOD_WIN,
            "left" => key = Some(VK_LEFT.0 as u32),
            "right" => key = Some(VK_RIGHT.0 as u32),
            "up" => key = Some(VK_UP.0 as u32),
            "down" => key = Some(VK_DOWN.0 as u32),
            "space" => key = Some(VK_SPACE.0 as u32),
            "enter" => key = Some(VK_RETURN.0 as u32),
            "escape" | "esc" => key = Some(VK_ESCAPE.0 as u32),
            token if token.len() == 1 => key = token.chars().next().map(|value| value.to_ascii_uppercase() as u32),
            _ => return None,
        }
    }
    key.map(|key| (modifiers, key))
}

#[cfg(target_os = "windows")]
fn run_windows_manager(
    ctx: Context,
    commands: Receiver<WindowManagerCommand>,
    updates: Sender<WindowManagerUpdate>,
    running: Arc<AtomicBool>,
    config: WmConfig,
) {
    use windows::Win32::{
        Foundation::HMODULE,
        UI::{
            Accessibility::{SetWinEventHook, UnhookWinEvent},
            Input::KeyboardAndMouse::{
                MOD_ALT, MOD_NOREPEAT, MOD_SHIFT, RegisterHotKey, UnregisterHotKey, VK_DOWN,
                VK_LEFT, VK_RIGHT, VK_UP,
            },
            WindowsAndMessaging::{
                DispatchMessageW, EVENT_OBJECT_CREATE, EVENT_OBJECT_DESTROY, EVENT_OBJECT_HIDE,
                EVENT_OBJECT_LOCATIONCHANGE, EVENT_OBJECT_NAMECHANGE, EVENT_OBJECT_SHOW,
                EVENT_SYSTEM_FOREGROUND, EVENT_SYSTEM_MINIMIZEEND, EVENT_SYSTEM_MOVESIZEEND,
                EVENT_SYSTEM_MOVESIZESTART,
                MSG, PM_REMOVE, PeekMessageW, TranslateMessage,
                WINEVENT_OUTOFCONTEXT, WINEVENT_SKIPOWNPROCESS, WM_HOTKEY,
            },
        },
    };

    let flags = WINEVENT_OUTOFCONTEXT | WINEVENT_SKIPOWNPROCESS;
    let foreground_hook = unsafe {
        SetWinEventHook(
            EVENT_SYSTEM_FOREGROUND,
            EVENT_SYSTEM_FOREGROUND,
            HMODULE::default(),
            Some(window_event_callback),
            0,
            0,
            flags,
        )
    };
    let object_hook = unsafe {
        SetWinEventHook(
            EVENT_OBJECT_CREATE,
            EVENT_OBJECT_NAMECHANGE.max(EVENT_OBJECT_LOCATIONCHANGE).max(EVENT_OBJECT_SHOW).max(EVENT_OBJECT_HIDE).max(EVENT_OBJECT_DESTROY),
            HMODULE::default(),
            Some(window_event_callback),
            0,
            0,
            flags,
        )
    };
    let move_size_hook = unsafe {
        SetWinEventHook(
            EVENT_SYSTEM_MOVESIZESTART,
            EVENT_SYSTEM_MOVESIZEEND,
            HMODULE::default(),
            Some(window_event_callback),
            0,
            0,
            flags,
        )
    };
    let restore_hook = unsafe {
        SetWinEventHook(
            EVENT_SYSTEM_MINIMIZEEND,
            EVENT_SYSTEM_MINIMIZEEND,
            HMODULE::default(),
            Some(window_event_callback),
            0,
            0,
            flags,
        )
    };

    // Alt+1..9 switches workspaces; Alt+Shift+1..9 moves the focused window.
    for number in 1..=9_i32 {
        unsafe {
            let _ = RegisterHotKey(None, number, MOD_ALT | MOD_NOREPEAT, b'0' as u32 + number as u32);
            let _ = RegisterHotKey(
                None,
                100 + number,
                MOD_ALT | MOD_SHIFT | MOD_NOREPEAT,
                b'0' as u32 + number as u32,
            );
        }
    }
    // User-configurable actions plus fixed arrow/resize/monitor aliases.
    let mut hotkeys = configured_hotkeys(&config);
    hotkeys.extend([
        (207, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'P' as u32),
        (220, MOD_ALT | MOD_NOREPEAT, VK_LEFT.0 as u32),
        (221, MOD_ALT | MOD_NOREPEAT, VK_RIGHT.0 as u32),
        (222, MOD_ALT | MOD_NOREPEAT, VK_UP.0 as u32),
        (223, MOD_ALT | MOD_NOREPEAT, VK_DOWN.0 as u32),
        (224, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, VK_LEFT.0 as u32),
        (225, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, VK_RIGHT.0 as u32),
        (226, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, VK_UP.0 as u32),
        (227, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, VK_DOWN.0 as u32),
        (230, MOD_ALT | MOD_NOREPEAT, b'U' as u32),
        (231, MOD_ALT | MOD_NOREPEAT, b'P' as u32),
        (232, MOD_ALT | MOD_NOREPEAT, b'O' as u32),
        (233, MOD_ALT | MOD_NOREPEAT, b'I' as u32),
        (234, MOD_ALT | MOD_NOREPEAT, b'R' as u32),
        (235, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'E' as u32),
        (236, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'R' as u32),
        (240, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'A' as u32),
        (241, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'F' as u32),
        (242, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'D' as u32),
        (243, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, b'S' as u32),
    ]);
    for (id, modifiers, key) in &hotkeys {
        unsafe {
            let _ = RegisterHotKey(None, *id, *modifiers, *key);
        }
    }

    let mut manager = Manager::new(config);
    let mut snap_preview = SnapPreviewOverlay::default();
    let mut last_direction = manager.direction;
    let mut last_floating = None;
    let mut last_resize_mode = None;
    let mut last_border_refresh = Instant::now() - Duration::from_secs(1);
    let mut last_composition_refresh = Instant::now() - Duration::from_secs(1);
    let mut last_fallback_scan = Instant::now() - Duration::from_secs(1);
    WINDOW_EVENT_DIRTY.store(true, Ordering::Release);

    while running.load(Ordering::Acquire) {
        let mut force_publish = false;
        let queued_events = WINDOW_EVENTS.get_or_init(Default::default)
            .lock().map(|mut events| std::mem::take(&mut *events)).unwrap_or_default();
        // Foreground and destroy/hide notifications from one close can arrive
        // in either order. Mark departures for the whole batch first so a
        // foreground fallback from another workspace cannot be mistaken for
        // an intentional tray/taskbar activation.
        for (event, handle) in &queued_events {
            if *event == EVENT_OBJECT_DESTROY || *event == EVENT_OBJECT_HIDE {
                manager.note_window_departure(*handle);
            }
        }
        for (event, handle) in queued_events {
            if event == EVENT_SYSTEM_FOREGROUND {
                manager.apply_foreground_event(handle);
                force_publish = true;
            } else if event == EVENT_SYSTEM_MINIMIZEEND {
                if manager.is_stale_cross_workspace_activation(handle) {
                    // Parked window restored/activated by the OS, not the user.
                } else if manager.activate_external_window(handle) {
                    force_publish = true;
                }
            } else if event == EVENT_OBJECT_DESTROY {
                if manager.dragging == Some(handle) {
                    manager.dragging = None;
                    manager.snap_target = None;
                    snap_preview.clear();
                }
                if manager.forget_window(handle) {
                    if !manager.paused { manager.tile_active_workspace(); }
                    manager.focus_active_replacement();
                    force_publish = true;
                }
            } else if event == EVENT_SYSTEM_MOVESIZESTART
                && manager.windows.get(&handle).is_some_and(|window| !window.floating)
            {
                manager.dragging = Some(handle);
                manager.snap_target = None;
            } else if event == EVENT_SYSTEM_MOVESIZEEND && manager.dragging == Some(handle) {
                manager.update_snap_target();
                // Destroy the native topmost preview before moving/focusing real
                // windows or refreshing blur, so DWM cannot retain a stale frame.
                snap_preview.clear();
                manager.finish_drag();
                force_publish = true;
            }
        }
        if manager.dragging.is_some() {
            manager.update_snap_target();
            if let Some(target) = manager.snap_target.as_ref() {
                manager.apply_snap_preview_layout();
                snap_preview.show(std::slice::from_ref(&target.preview));
            } else {
                snap_preview.hide();
            }
        }
        while let Ok(command) = commands.try_recv() {
            match command {
                WindowManagerCommand::FocusWorkspace(name) => {
                    if let Ok(workspace) = name.parse() {
                        manager.focus_workspace(workspace);
                        force_publish = true;
                    }
                }
                WindowManagerCommand::CloseWindow(handle) => {
                    manager.close_window(handle);
                }
                WindowManagerCommand::FocusWindow { handle, workspace } => {
                    if let Ok(workspace) = workspace.parse() {
                        manager.focus_window(handle, workspace);
                        force_publish = true;
                    }
                }
                WindowManagerCommand::ToggleTilingDirection => {
                    manager.toggle_direction();
                    let _ = updates.send(WindowManagerUpdate::TilingDirection(manager.direction));
                    force_publish = true;
                }
                WindowManagerCommand::ToggleFloating => {
                    if manager.toggle_floating() {
                        let _ = updates.send(WindowManagerUpdate::ConfigChanged(manager.config.clone()));
                    }
                    force_publish = true;
                }
                WindowManagerCommand::UpdateConfig(config) => {
                    for (id, _, _) in &hotkeys {
                        unsafe { let _ = UnregisterHotKey(None, *id); }
                    }
                    hotkeys = configured_hotkeys(&config);
                    hotkeys.extend(fixed_hotkey_aliases());
                    for (id, modifiers, key) in &hotkeys {
                        unsafe { let _ = RegisterHotKey(None, *id, *modifiers, *key); }
                    }
                    manager.update_config(config);
                    force_publish = true;
                }
            }
        }

        let mut message = MSG::default();
        while unsafe { PeekMessageW(&mut message, None, 0, 0, PM_REMOVE) }.as_bool() {
            if message.message == WM_HOTKEY {
                let id = message.wParam.0 as i32;
                if manager.resize_mode {
                    match id {
                        300 | 301 => manager.resize_focused(-0.02, 0.0),
                        302 | 303 => manager.resize_focused(0.02, 0.0),
                        304 | 305 => manager.resize_focused(0.0, 0.02),
                        306 | 307 => manager.resize_focused(0.0, -0.02),
                        308 | 309 => set_resize_mode(&mut manager, false),
                        _ => {}
                    }
                    force_publish = true;
                    continue;
                }
                if manager.paused && id != 207 {
                    continue;
                }
                match id {
                    1..=9 => manager.focus_workspace(id as usize),
                    101..=109 => {
                        let workspace = (id - 100) as usize;
                        manager.move_focused_to_workspace(workspace);
                        manager.focus_workspace(workspace);
                    }
                    201 | 220 => manager.focus_direction(-1, 0),
                    202 | 221 => manager.focus_direction(1, 0),
                    208 | 222 => manager.focus_direction(0, -1),
                    209 | 223 => manager.focus_direction(0, 1),
                    203 | 224 => manager.move_focused_direction(-1, 0),
                    204 | 225 => manager.move_focused_direction(1, 0),
                    210 | 226 => manager.move_focused_direction(0, -1),
                    211 | 227 => manager.move_focused_direction(0, 1),
                    205 => {
                        manager.toggle_direction();
                        let _ = updates.send(WindowManagerUpdate::TilingDirection(manager.direction));
                    }
                    206 => {
                        if manager.toggle_floating() {
                            let _ = updates.send(WindowManagerUpdate::ConfigChanged(manager.config.clone()));
                        }
                    }
                    207 => manager.toggle_paused(),
                    212 => {
                        if manager.set_tiled() {
                            let _ = updates.send(WindowManagerUpdate::ConfigChanged(manager.config.clone()));
                        }
                    }
                    213 => manager.toggle_fullscreen(),
                    214 => manager.toggle_minimized(),
                    215 => manager.close_focused(),
                    216 => manager.focus_relative_workspace(-1),
                    217 => manager.focus_relative_workspace(1),
                    218 => manager.focus_workspace(manager.recent_workspace),
                    219 => manager.tile_active_workspace(),
                    230 => manager.resize_focused(-0.02, 0.0),
                    231 => manager.resize_focused(0.02, 0.0),
                    232 => manager.resize_focused(0.0, 0.02),
                    233 => manager.resize_focused(0.0, -0.02),
                    234 => set_resize_mode(&mut manager, true),
                    235 => {
                        ctx.send_viewport_cmd(eframe::egui::ViewportCommand::Close);
                        running.store(false, Ordering::Release);
                    }
                    236 => {
                        WINDOW_EVENT_DIRTY.store(true, Ordering::Release);
                        manager.tile_active_workspace();
                    }
                    237 => {
                        if manager.center_focused_floating() {
                            let _ = updates.send(WindowManagerUpdate::ConfigChanged(manager.config.clone()));
                        }
                    }
                    240 => manager.move_workspace_to_monitor(-1, 0),
                    241 => manager.move_workspace_to_monitor(1, 0),
                    242 => manager.move_workspace_to_monitor(0, -1),
                    243 => manager.move_workspace_to_monitor(0, 1),
                    _ => {}
                }
                // Closing is asynchronous. Publish/recompose only after the
                // real hide/destroy event, not while the old HWND is still
                // drawing over the layout it is about to leave.
                if id != 215 {
                    force_publish = true;
                }
            } else {
                unsafe {
                    let _ = TranslateMessage(&message);
                    DispatchMessageW(&message);
                }
            }
        }

        let periodic_scan = last_fallback_scan.elapsed() >= Duration::from_millis(500);
        if periodic_scan || WINDOW_EVENT_DIRTY.swap(false, Ordering::AcqRel) {
            if periodic_scan {
                last_fallback_scan = Instant::now();
            }
            let (changed, layout_changed) = manager.refresh();
            if layout_changed && !manager.paused {
                manager.tile_active_workspace();
            }
            if layout_changed && manager.focused.is_none() {
                manager.focus_active_replacement();
            }
            force_publish |= changed;
        }
        manager.enforce_pending_workspace_focus();
        if !manager.publish(&updates, &ctx, force_publish) {
            break;
        }
        if manager.direction != last_direction {
            last_direction = manager.direction;
            if updates.send(WindowManagerUpdate::TilingDirection(last_direction)).is_err() { break; }
            ctx.request_repaint();
        }
        let focused_floating = manager
            .focused
            .and_then(|handle| manager.windows.get(&handle))
            .is_some_and(|window| window.floating);
        if last_floating != Some(focused_floating) {
            last_floating = Some(focused_floating);
            if updates.send(WindowManagerUpdate::Floating(focused_floating)).is_err() { break; }
            ctx.request_repaint();
        }
        if last_resize_mode != Some(manager.resize_mode) {
            last_resize_mode = Some(manager.resize_mode);
            if updates
                .send(WindowManagerUpdate::ResizeMode(manager.resize_mode))
                .is_err()
            {
                break;
            }
            ctx.request_repaint();
        }
        let composition_due = force_publish
            || (manager.dragging.is_some()
                && last_composition_refresh.elapsed() >= Duration::from_millis(50));
        if composition_due && updates.send(WindowManagerUpdate::LayoutChanged).is_err() {
            break;
        } else if composition_due {
            last_composition_refresh = Instant::now();
            ctx.request_repaint();
        }
        if last_border_refresh.elapsed() >= Duration::from_millis(75) {
            if manager.dragging.is_none() {
                manager.sync_native_maximize(&updates);
                ctx.request_repaint();
            }
            manager.enforce_workspace_visibility();
            if !manager.paused && manager.dragging.is_none() {
                // Firefox-family windows (including Zen) can enforce a chrome
                // minimum after placement. Absorb that once into the split
                // tree instead of fighting the app between two sizes forever.
                if manager.reconcile_tiled_constraints() {
                    let _ = updates.send(WindowManagerUpdate::LayoutChanged);
                    last_composition_refresh = Instant::now();
                    ctx.request_repaint();
                } else {
                    manager.apply_borders();
                }
            } else {
                manager.apply_borders();
            }
            last_border_refresh = Instant::now();
        }
        thread::sleep(Duration::from_millis(8));
    }

    manager.restore_windows();
    set_resize_mode(&mut manager, false);

    for id in 1..=9_i32 {
        unsafe {
            let _ = UnregisterHotKey(None, id);
            let _ = UnregisterHotKey(None, 100 + id);
        }
    }
    for (id, _, _) in hotkeys {
        unsafe {
            let _ = UnregisterHotKey(None, id);
        }
    }
    if !foreground_hook.is_invalid() {
        unsafe {
            let _ = UnhookWinEvent(foreground_hook);
        }
    }
    if !object_hook.is_invalid() {
        unsafe {
            let _ = UnhookWinEvent(object_hook);
        }
    }
    if !move_size_hook.is_invalid() {
        unsafe { let _ = UnhookWinEvent(move_size_hook); }
    }
    if !restore_hook.is_invalid() {
        unsafe { let _ = UnhookWinEvent(restore_hook); }
    }
}

#[cfg(target_os = "windows")]
fn set_resize_mode(manager: &mut Manager, enabled: bool) {
    use windows::Win32::UI::Input::KeyboardAndMouse::{
        MOD_NOREPEAT, RegisterHotKey, UnregisterHotKey, VK_DOWN, VK_ESCAPE, VK_LEFT, VK_RETURN,
        VK_RIGHT, VK_UP,
    };

    if manager.resize_mode == enabled {
        return;
    }
    const MODE_IDS: std::ops::RangeInclusive<i32> = 300..=309;
    if enabled {
        let bindings = [
            (300, b'H' as u32),
            (301, VK_LEFT.0 as u32),
            (302, b'L' as u32),
            (303, VK_RIGHT.0 as u32),
            (304, b'K' as u32),
            (305, VK_UP.0 as u32),
            (306, b'J' as u32),
            (307, VK_DOWN.0 as u32),
            (308, VK_ESCAPE.0 as u32),
            (309, VK_RETURN.0 as u32),
        ];
        let mut registered = Vec::new();
        for (id, key) in bindings {
            if unsafe { RegisterHotKey(None, id, MOD_NOREPEAT, key) }.is_ok() {
                registered.push(id);
            }
        }
        if registered.len() != MODE_IDS.clone().count() {
            for id in registered {
                unsafe {
                    let _ = UnregisterHotKey(None, id);
                }
            }
            return;
        }
    } else {
        for id in MODE_IDS {
            unsafe {
                let _ = UnregisterHotKey(None, id);
            }
        }
    }
    manager.resize_mode = enabled;
}

#[cfg(target_os = "windows")]
unsafe extern "system" fn window_event_callback(
    _hook: windows::Win32::UI::Accessibility::HWINEVENTHOOK,
    event: u32,
    event_hwnd: windows::Win32::Foundation::HWND,
    object_id: i32,
    child_id: i32,
    _event_thread: u32,
    _event_time: u32,
) {
    use windows::Win32::UI::WindowsAndMessaging::{
        EVENT_OBJECT_DESTROY, EVENT_OBJECT_HIDE, EVENT_OBJECT_SHOW, EVENT_SYSTEM_FOREGROUND,
        EVENT_SYSTEM_MINIMIZEEND, EVENT_SYSTEM_MOVESIZEEND, EVENT_SYSTEM_MOVESIZESTART,
        OBJID_WINDOW,
    };
    if event == EVENT_SYSTEM_FOREGROUND {
        if let Ok(mut events) = WINDOW_EVENTS.get_or_init(Default::default).lock() {
            events.push((event, event_hwnd.0 as isize));
        }
    } else if event == EVENT_SYSTEM_MOVESIZESTART
        || event == EVENT_SYSTEM_MOVESIZEEND
        || event == EVENT_SYSTEM_MINIMIZEEND
    {
        if !event_hwnd.is_invalid() {
            if let Ok(mut events) = WINDOW_EVENTS.get_or_init(Default::default).lock() {
                events.push((event, event_hwnd.0 as isize));
            }
        }
    }
    if (event == EVENT_OBJECT_DESTROY || event == EVENT_OBJECT_HIDE || event == EVENT_OBJECT_SHOW)
        && (object_id == OBJID_WINDOW.0 || object_id == 0)
        && child_id == 0
        && !event_hwnd.is_invalid()
    {
        if let Ok(mut events) = WINDOW_EVENTS.get_or_init(Default::default).lock() {
            events.push((event, event_hwnd.0 as isize));
        }
    }
    if (object_id == OBJID_WINDOW.0 || object_id == 0) && child_id == 0 {
        WINDOW_EVENT_DIRTY.store(true, Ordering::Release);
    }
}

#[cfg(target_os = "windows")]
fn enumerate_manageable_windows() -> Vec<ManagedWindow> {
    use windows::Win32::{
        Foundation::{BOOL, LPARAM},
        UI::WindowsAndMessaging::EnumWindows,
    };

    unsafe extern "system" fn callback(
        handle: windows::Win32::Foundation::HWND,
        parameter: LPARAM,
    ) -> BOOL {
        let windows = unsafe { &mut *(parameter.0 as *mut Vec<ManagedWindow>) };
        if let Some(window) = inspect_window(handle) {
            windows.push(window);
        }
        BOOL(1)
    }

    let mut windows = Vec::new();
    unsafe {
        let _ = EnumWindows(
            Some(callback),
            LPARAM((&mut windows as *mut Vec<ManagedWindow>) as isize),
        );
    }
    windows
}

#[cfg(target_os = "windows")]
fn enumerate_monitors() -> Vec<(isize, windows::Win32::Foundation::RECT)> {
    use windows::Win32::{
        Foundation::{BOOL, LPARAM, RECT},
        Graphics::Gdi::{EnumDisplayMonitors, HDC, HMONITOR},
    };

    unsafe extern "system" fn callback(
        monitor: HMONITOR,
        _dc: HDC,
        rect: *mut RECT,
        parameter: LPARAM,
    ) -> BOOL {
        if !rect.is_null() {
            let monitors = unsafe { &mut *(parameter.0 as *mut Vec<(isize, RECT)>) };
            monitors.push((monitor.0 as isize, unsafe { *rect }));
        }
        BOOL(1)
    }

    let mut monitors = Vec::new();
    unsafe {
        let _ = EnumDisplayMonitors(
            None,
            None,
            Some(callback),
            LPARAM((&mut monitors as *mut Vec<(isize, RECT)>) as isize),
        );
    }
    monitors
}

#[cfg(target_os = "windows")]
fn managed_window_still_present(handle: isize) -> bool {
    use windows::Win32::{
        Graphics::Dwm::{DWMWA_CLOAKED, DwmGetWindowAttribute},
        UI::WindowsAndMessaging::{IsIconic, IsWindow, IsWindowVisible},
    };

    let handle = hwnd(handle);
    if !unsafe { IsWindow(handle) }.as_bool() {
        return false;
    }
    if unsafe { IsIconic(handle) }.as_bool() {
        return true;
    }
    if !unsafe { IsWindowVisible(handle) }.as_bool() {
        return false;
    }
    let mut cloaked = 0_u32;
    unsafe {
        DwmGetWindowAttribute(
            handle,
            DWMWA_CLOAKED,
            &mut cloaked as *mut _ as *mut c_void,
            std::mem::size_of_val(&cloaked) as u32,
        )
    }
    .is_err()
        || cloaked == 0
}

#[cfg(target_os = "windows")]
fn inspect_window(handle: windows::Win32::Foundation::HWND) -> Option<ManagedWindow> {
    use windows::Win32::{
        Graphics::Dwm::{DWMWA_CLOAKED, DwmGetWindowAttribute},
        System::Threading::GetCurrentProcessId,
        UI::WindowsAndMessaging::{
            GWL_EXSTYLE, GWL_STYLE, GW_OWNER, GetClassNameW, GetWindow, GetWindowLongW,
            GetWindowRect, GetWindowTextLengthW, GetWindowTextW, GetWindowThreadProcessId,
            IsWindowVisible, WS_CHILD, WS_EX_TOOLWINDOW, WS_THICKFRAME,
        },
    };

    if handle.is_invalid() || !unsafe { IsWindowVisible(handle) }.as_bool() {
        return None;
    }
    let mut process_id = 0_u32;
    unsafe { GetWindowThreadProcessId(handle, Some(&mut process_id)) };
    if process_id == 0 || process_id == unsafe { GetCurrentProcessId() } {
        // Exclude every Overbar-owned viewport by identity. Titles can be delayed,
        // localized, or briefly empty while eframe recreates an overlay HWND.
        return None;
    }
    let style = unsafe { GetWindowLongW(handle, GWL_STYLE) } as u32;
    let ex_style = unsafe { GetWindowLongW(handle, GWL_EXSTYLE) } as u32;
    if style & WS_CHILD.0 != 0 {
        return None;
    }
    let owner = unsafe { GetWindow(handle, GW_OWNER) }.ok()
        .filter(|owner| !owner.is_invalid())
        .map(|owner| owner.0 as isize);
    // Unowned tool windows are normally palettes, tray helpers, or overlays.
    // Owned titled tool windows are dialogs and must remain independently manageable.
    if ex_style & WS_EX_TOOLWINDOW.0 != 0 && owner.is_none() {
        return None;
    }
    let mut cloaked = 0_u32;
    if unsafe {
        DwmGetWindowAttribute(
            handle,
            DWMWA_CLOAKED,
            &mut cloaked as *mut _ as *mut c_void,
            std::mem::size_of_val(&cloaked) as u32,
        )
    }
    .is_ok()
        && cloaked != 0
    {
        return None;
    }

    let mut class_buffer = [0_u16; 256];
    let class_length = unsafe { GetClassNameW(handle, &mut class_buffer) }.max(0) as usize;
    let class_name = String::from_utf16_lossy(&class_buffer[..class_length]);
    if matches!(
        class_name.as_str(),
        "Progman" | "WorkerW" | "Shell_TrayWnd" | "Shell_SecondaryTrayWnd"
    ) {
        return None;
    }

    let length = unsafe { GetWindowTextLengthW(handle) };
    if length <= 0 {
        return None;
    }
    let mut title_buffer = vec![0_u16; length as usize + 1];
    let copied = unsafe { GetWindowTextW(handle, &mut title_buffer) };
    if copied <= 0 {
        return None;
    }
    let title = String::from_utf16_lossy(&title_buffer[..copied as usize])
        .trim()
        .to_owned();
    let raw_process_name = window_process_name(handle).unwrap_or_else(|| "Application".into());
    if title.is_empty() || is_shell_surface_title(&title, &class_name, &raw_process_name) {
        return None;
    }
    let process_name = if raw_process_name.eq_ignore_ascii_case("ApplicationFrameHost.exe") {
        title.clone()
    } else {
        raw_process_name.trim_end_matches(".exe").to_owned()
    };
    let mut original = windows::Win32::Foundation::RECT::default();
    if unsafe { GetWindowRect(handle, &mut original) }.is_err() {
        return None;
    }
    let width = original.right - original.left;
    let height = original.bottom - original.top;
    let discord_chromium_splash = process_name.to_ascii_lowercase().starts_with("discord")
        && class_name.starts_with("Chrome_WidgetWin_");
    let transient = owner.is_none()
        && width > 0
        && height > 0
        && width <= 700
        && height <= 520
        && (discord_chromium_splash || style & WS_THICKFRAME.0 == 0);
    Some(ManagedWindow {
        handle: handle.0 as isize,
        title,
        process_name,
        class_name,
        owner,
        original_rect: LayoutRect {
            left: original.left,
            top: original.top,
            right: original.right,
            bottom: original.bottom,
        },
        transient,
        workspace: 1,
        floating: transient || style & WS_THICKFRAME.0 == 0,
        fullscreen_restore: None,
        maximize_restore: None,
        native_maximized: false,
    })
}

#[cfg(target_os = "windows")]
pub(super) fn window_process_name(handle: windows::Win32::Foundation::HWND) -> Option<String> {
    use windows::{
        Win32::{
            Foundation::CloseHandle,
            System::Threading::{
                OpenProcess, PROCESS_NAME_WIN32, PROCESS_QUERY_LIMITED_INFORMATION,
                QueryFullProcessImageNameW,
            },
            UI::WindowsAndMessaging::GetWindowThreadProcessId,
        },
        core::PWSTR,
    };

    let mut process_id = 0_u32;
    unsafe { GetWindowThreadProcessId(handle, Some(&mut process_id)) };
    if process_id == 0 {
        return None;
    }
    let process = unsafe { OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, false, process_id) }.ok()?;
    let mut buffer = vec![0_u16; 32_768];
    let mut length = buffer.len() as u32;
    let result = unsafe {
        QueryFullProcessImageNameW(
            process,
            PROCESS_NAME_WIN32,
            PWSTR(buffer.as_mut_ptr()),
            &mut length,
        )
    };
    unsafe {
        let _ = CloseHandle(process);
    }
    result.ok()?;
    let path = String::from_utf16_lossy(&buffer[..length as usize]);
    std::path::Path::new(&path)
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
}

#[cfg(target_os = "windows")]
fn native_accent_colorref() -> u32 {
    use windows::Win32::{Foundation::BOOL, Graphics::Dwm::DwmGetColorizationColor};
    let mut argb = 0_u32;
    let mut opaque = BOOL::default();
    if unsafe { DwmGetColorizationColor(&mut argb, &mut opaque) }.is_ok() {
        let red = (argb >> 16) & 0xff;
        let green = (argb >> 8) & 0xff;
        let blue = argb & 0xff;
        red | (green << 8) | (blue << 16)
    } else {
        0x00c5_b869
    }
}

#[cfg(target_os = "windows")]
fn set_window_cloaked(handle: isize, cloaked: bool) {
    use windows::Win32::{
        Graphics::Dwm::{DWMWA_CLOAK, DwmSetWindowAttribute},
        UI::WindowsAndMessaging::{SW_HIDE, SW_SHOWNOACTIVATE, ShowWindowAsync},
    };
    let value = u32::from(cloaked);
    let result = unsafe {
        DwmSetWindowAttribute(
            hwnd(handle),
            DWMWA_CLOAK,
            &value as *const _ as *const c_void,
            std::mem::size_of_val(&value) as u32,
        )
    };
    if result.is_err() {
        unsafe {
            let _ = ShowWindowAsync(
                hwnd(handle),
                if cloaked { SW_HIDE } else { SW_SHOWNOACTIVATE },
            );
        }
    }
}

#[cfg(target_os = "windows")]
fn set_managed_window_transitions(handle: isize, disabled: bool) {
    use windows::Win32::{
        Foundation::BOOL,
        Graphics::Dwm::{DWMWA_TRANSITIONS_FORCEDISABLED, DwmSetWindowAttribute},
    };
    let value = BOOL::from(disabled);
    unsafe {
        let _ = DwmSetWindowAttribute(
            hwnd(handle),
            DWMWA_TRANSITIONS_FORCEDISABLED,
            &value as *const _ as *const c_void,
            std::mem::size_of_val(&value) as u32,
        );
    }
}

#[cfg(target_os = "windows")]
fn flush_dwm() {
    unsafe {
        let _ = windows::Win32::Graphics::Dwm::DwmFlush();
    }
}

#[cfg(target_os = "windows")]
fn focus_native_window(handle: isize) {
    use windows::Win32::{
        System::Threading::{AttachThreadInput, GetCurrentThreadId},
        UI::{
            WindowsAndMessaging::{
                BringWindowToTop, GetForegroundWindow, GetWindowThreadProcessId, IsIconic,
                SW_RESTORE, SetForegroundWindow, ShowWindowAsync,
            },
        },
    };

    let target = hwnd(handle);
    unsafe {
        if IsIconic(target).as_bool() {
            let _ = ShowWindowAsync(target, SW_RESTORE);
        }
        if SetForegroundWindow(target).as_bool() {
            return;
        }

        // Commands originate on the manager thread, not the target application's
        // UI thread. Temporarily joining their input queues makes activation
        // deterministic after a workspace cloak/uncloak transaction.
        let current_thread = GetCurrentThreadId();
        let foreground_thread = GetWindowThreadProcessId(GetForegroundWindow(), None);
        let target_thread = GetWindowThreadProcessId(target, None);
        let attached_foreground = foreground_thread != 0
            && foreground_thread != current_thread
            && AttachThreadInput(current_thread, foreground_thread, true).as_bool();
        let attached_target = target_thread != 0
            && target_thread != current_thread
            && target_thread != foreground_thread
            && AttachThreadInput(current_thread, target_thread, true).as_bool();

        let _ = BringWindowToTop(target);
        let _ = SetForegroundWindow(target);

        if attached_target {
            let _ = AttachThreadInput(current_thread, target_thread, false);
        }
        if attached_foreground {
            let _ = AttachThreadInput(current_thread, foreground_thread, false);
        }
    }
}

#[cfg(target_os = "windows")]
fn visible_window_rect(handle: isize) -> Option<LayoutRect> {
    use windows::Win32::{
        Foundation::RECT,
        Graphics::Dwm::{DWMWA_EXTENDED_FRAME_BOUNDS, DwmGetWindowAttribute},
        UI::WindowsAndMessaging::GetWindowRect,
    };
    let mut rect = RECT::default();
    if unsafe {
        DwmGetWindowAttribute(
            hwnd(handle),
            DWMWA_EXTENDED_FRAME_BOUNDS,
            &mut rect as *mut _ as *mut c_void,
            std::mem::size_of::<RECT>() as u32,
        )
    }
    .is_err()
        && unsafe { GetWindowRect(hwnd(handle), &mut rect) }.is_err()
    {
        return None;
    }
    Some(LayoutRect {
        left: rect.left,
        top: rect.top,
        right: rect.right,
        bottom: rect.bottom,
    })
}

#[cfg(target_os = "windows")]
fn window_min_track_size(handle: isize) -> Option<(i32, i32)> {
    use windows::Win32::{
        Foundation::{LPARAM, WPARAM},
        UI::WindowsAndMessaging::{
            MINMAXINFO, SMTO_ABORTIFHUNG, SendMessageTimeoutW, WM_GETMINMAXINFO,
        },
    };
    let mut info = MINMAXINFO::default();
    let mut result = 0_usize;
    unsafe {
        let _ = SendMessageTimeoutW(
            hwnd(handle),
            WM_GETMINMAXINFO,
            WPARAM(0),
            LPARAM((&mut info as *mut MINMAXINFO) as isize),
            SMTO_ABORTIFHUNG,
            20,
            Some(&mut result),
        );
    }
    let width = info.ptMinTrackSize.x.max(64);
    let height = info.ptMinTrackSize.y.max(64);
    Some((width, height))
}

#[cfg(target_os = "windows")]
fn window_placement_for_visible_rect(handle: isize, desired: LayoutRect) -> LayoutRect {
    use windows::Win32::{Foundation::RECT, UI::WindowsAndMessaging::GetWindowRect};
    let Some(visible) = visible_window_rect(handle) else {
        return desired;
    };
    let mut outer = RECT::default();
    if unsafe { GetWindowRect(hwnd(handle), &mut outer) }.is_err() {
        return desired;
    }
    let left_frame = (visible.left - outer.left).max(0);
    let top_frame = (visible.top - outer.top).max(0);
    let right_frame = (outer.right - visible.right).max(0);
    let bottom_frame = (outer.bottom - visible.bottom).max(0);
    LayoutRect {
        left: desired.left - left_frame,
        top: desired.top - top_frame,
        right: desired.right + right_frame,
        bottom: desired.bottom + bottom_frame,
    }
}

#[cfg(target_os = "windows")]
fn hwnd(handle: isize) -> windows::Win32::Foundation::HWND {
    windows::Win32::Foundation::HWND(handle as *mut c_void)
}

#[cfg(target_os = "windows")]
fn set_native_taskbar_tab_visible(handle: isize, visible: bool) {
    use windows::Win32::{
        System::Com::{
            CLSCTX_INPROC_SERVER, COINIT_APARTMENTTHREADED, CoCreateInstance, CoInitializeEx,
            CoUninitialize,
        },
        UI::Shell::{ITaskbarList, TaskbarList},
    };
    let initialized_here = unsafe { CoInitializeEx(None, COINIT_APARTMENTTHREADED) }.is_ok();
    let taskbar: windows::core::Result<ITaskbarList> =
        unsafe { CoCreateInstance(&TaskbarList, None, CLSCTX_INPROC_SERVER) };
    if let Ok(taskbar) = taskbar {
        let _ = unsafe { taskbar.HrInit() };
        if visible {
            let _ = unsafe { taskbar.AddTab(hwnd(handle)) };
        } else {
            let _ = unsafe { taskbar.DeleteTab(hwnd(handle)) };
        }
    }
    if initialized_here {
        unsafe { CoUninitialize() };
    }
}

#[cfg(all(test, target_os = "windows"))]
mod tests {
    use super::*;

    #[test]
    fn configurable_hotkeys_parse_modifiers_and_named_keys() {
        use windows::Win32::UI::Input::KeyboardAndMouse::{MOD_ALT, MOD_SHIFT, VK_LEFT};
        let (modifiers, key) = parse_hotkey("Alt+Shift+Left").unwrap();
        assert!(modifiers.contains(MOD_ALT));
        assert!(modifiers.contains(MOD_SHIFT));
        assert_eq!(key, VK_LEFT.0 as u32);
    }

    #[test]
    fn floating_state_keys_distinguish_hosts_and_dialogs() {
        let window = |title: &str, owner| ManagedWindow {
            handle: 1,
            title: title.into(),
            process_name: "editor".into(),
            class_name: "EditorWindow".into(),
            owner,
            original_rect: LayoutRect { left: 0, top: 0, right: 800, bottom: 600 },
            transient: false,
            workspace: 1,
            floating: false,
            fullscreen_restore: None,
            maximize_restore: None,
            native_maximized: false,
        };
        let host = window("document.txt - Editor", None);
        let open_dialog = window("Open", Some(10));
        let save_dialog = window("Save As", Some(10));
        assert_ne!(host.persistence_key(), open_dialog.persistence_key());
        assert_ne!(open_dialog.persistence_key(), save_dialog.persistence_key());
    }

    #[test]
    fn split_layout_inserts_on_the_requested_side() {
        let mut root = LayoutNode::Leaf(1);
        assert!(root.insert_beside(1, 2, TilingDirection::Horizontal, true));
        assert!(root.insert_beside(1, 3, TilingDirection::Vertical, false));
        let mut rects = Vec::new();
        root.rects(
            LayoutRect {
                left: 0,
                top: 0,
                right: 1000,
                bottom: 800,
            },
            crate::DEFAULT_WM_GAP,
            &mut rects,
        );
        let first = rects.iter().find(|(handle, _)| *handle == 1).unwrap().1;
        let above = rects.iter().find(|(handle, _)| *handle == 3).unwrap().1;
        let right = rects.iter().find(|(handle, _)| *handle == 2).unwrap().1;
        assert!(above.bottom < first.top);
        assert!(first.right < right.left);
    }

    #[test]
    fn resizing_a_leaf_reflows_its_sibling() {
        let mut root = LayoutNode::Leaf(1);
        root.insert_beside(1, 2, TilingDirection::Horizontal, true);
        assert!(root.resize_for(1, TilingDirection::Horizontal, 0.1));
        let mut rects = Vec::new();
        root.rects(
            LayoutRect {
                left: 0,
                top: 0,
                right: 1000,
                bottom: 800,
            },
            crate::DEFAULT_WM_GAP,
            &mut rects,
        );
        let left = rects.iter().find(|(handle, _)| *handle == 1).unwrap().1;
        let right = rects.iter().find(|(handle, _)| *handle == 2).unwrap().1;
        assert!(left.right - left.left > right.right - right.left);
        assert_eq!(right.left - left.right, crate::DEFAULT_WM_GAP);
    }

    #[test]
    fn directional_resize_moves_the_boundary_consistently_from_either_side() {
        let area = LayoutRect {
            left: 0,
            top: 0,
            right: 1000,
            bottom: 800,
        };
        let mut from_left = LayoutNode::Leaf(1);
        from_left.insert_beside(1, 2, TilingDirection::Horizontal, true);
        assert!(from_left.move_boundary_for(1, TilingDirection::Horizontal, 0.1));
        let mut left_rects = Vec::new();
        from_left.rects(area, crate::DEFAULT_WM_GAP, &mut left_rects);
        let grown_left = left_rects.iter().find(|(handle, _)| *handle == 1).unwrap().1;

        let mut from_right = LayoutNode::Leaf(1);
        from_right.insert_beside(1, 2, TilingDirection::Horizontal, true);
        assert!(from_right.move_boundary_for(2, TilingDirection::Horizontal, 0.1));
        let mut right_rects = Vec::new();
        from_right.rects(area, crate::DEFAULT_WM_GAP, &mut right_rects);
        let shrunk_right = right_rects.iter().find(|(handle, _)| *handle == 2).unwrap().1;

        assert!(grown_left.right - grown_left.left > 500);
        assert!(shrunk_right.right - shrunk_right.left < 500);
    }

    #[test]
    fn removing_a_new_leaf_beside_an_earlier_window_restores_the_prior_tree() {
        let area = LayoutRect {
            left: 0,
            top: 0,
            right: 1600,
            bottom: 900,
        };
        let mut root = LayoutNode::Leaf(1);
        assert!(root.insert_beside(1, 2, TilingDirection::Horizontal, true));
        assert!(root.insert_beside(2, 3, TilingDirection::Vertical, true));
        let before = root.clone();

        // Reproduces: focus the first of three apps, open a fourth beside it,
        // then close that new app.
        assert!(root.insert_beside(1, 4, TilingDirection::Vertical, true));
        root = root.remove(4).expect("the original three-window tree remains");

        let mut expected = Vec::new();
        before.rects(area, crate::DEFAULT_WM_GAP, &mut expected);
        let mut actual = Vec::new();
        root.rects(area, crate::DEFAULT_WM_GAP, &mut actual);
        expected.sort_by_key(|(handle, _)| *handle);
        actual.sort_by_key(|(handle, _)| *handle);
        assert_eq!(actual, expected);
    }

    #[test]
    fn empty_inactive_workspaces_are_not_published() {
        let mut manager = Manager::new(WmConfig::default());
        manager.active_workspace = 5;
        manager.windows.insert(
            10,
            ManagedWindow {
                handle: 10,
                title: "Editor".into(),
                process_name: "editor".into(),
                class_name: "EditorWindow".into(),
                owner: None,
                original_rect: LayoutRect { left: 10, top: 10, right: 810, bottom: 610 },
                transient: false,
                workspace: 1,
                floating: false,
                fullscreen_restore: None,
                maximize_restore: None,
                native_maximized: false,
            },
        );
        let state = manager.state();
        assert_eq!(
            state
                .items
                .iter()
                .map(|workspace| workspace.name.as_str())
                .collect::<Vec<_>>(),
            ["1", "5"]
        );

        manager.active_workspace = 2;
        let state = manager.state();
        assert_eq!(
            state
                .items
                .iter()
                .map(|workspace| workspace.name.as_str())
                .collect::<Vec<_>>(),
            ["1", "2"]
        );
    }
}
