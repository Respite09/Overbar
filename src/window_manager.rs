//! Native Windows workspace and tiling manager.
//!
//! This module deliberately talks to Win32 directly. It owns workspace membership,
//! reacts to accessibility window events, lays out top-level application windows,
//! and publishes the compact state consumed by the bar.

use super::{
    AppEntry, TilingDirection, WindowManagerCommand, WindowManagerUpdate, WmConfig, WorkspaceEntry,
    WorkspacesState,
};
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
const TILE_GAP: i32 = 18;

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

    fn rects(&self, rect: LayoutRect, output: &mut Vec<(isize, LayoutRect)>) {
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
                            right: split - TILE_GAP / 2,
                            ..rect
                        },
                        output,
                    );
                    second.rects(
                        LayoutRect {
                            left: split + TILE_GAP / 2,
                            ..rect
                        },
                        output,
                    );
                }
                TilingDirection::Vertical => {
                    let split = rect.top
                        + ((rect.bottom - rect.top) as f32 * ratio).round() as i32;
                    first.rects(
                        LayoutRect {
                            bottom: split - TILE_GAP / 2,
                            ..rect
                        },
                        output,
                    );
                    second.rects(
                        LayoutRect {
                            top: split + TILE_GAP / 2,
                            ..rect
                        },
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
    layouts: HashMap<usize, LayoutNode>,
    workspace_monitors: HashMap<usize, isize>,
    insertion_directions: HashMap<isize, TilingDirection>,
    minimum_sizes: HashMap<isize, (i32, i32)>,
    dragging: Option<isize>,
    snap_target: Option<SnapTarget>,
    parked_rects: HashMap<isize, LayoutRect>,
    paused: bool,
    resize_mode: bool,
    closing: HashSet<isize>,
    taskbar_hidden: HashSet<isize>,
    last_published: Option<WorkspacesState>,
    config: WmConfig,
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
            layouts: HashMap::new(),
            workspace_monitors: HashMap::new(),
            insertion_directions: HashMap::new(),
            minimum_sizes: HashMap::new(),
            dragging: None,
            snap_target: None,
            parked_rects: HashMap::new(),
            paused: false,
            resize_mode: false,
            closing: HashSet::new(),
            taskbar_hidden: HashSet::new(),
            last_published: None,
            config,
        }
    }

    fn refresh(&mut self) -> (bool, bool) {
        use windows::Win32::UI::WindowsAndMessaging::{GetForegroundWindow, IsWindow};

        self.closing.retain(|handle| unsafe { IsWindow(hwnd(*handle)) }.as_bool());
        let discovered = enumerate_manageable_windows()
            .into_iter()
            .filter(|window| !self.closing.contains(&window.handle))
            .collect::<Vec<_>>();
        let discovered_handles = discovered.iter().map(|window| window.handle).collect::<HashSet<_>>();
        // Hidden-to-tray windows keep a valid HWND, but they are no longer a
        // visible managed window and must not keep their workspace alive.
        let removed = self.windows.keys().copied()
            .filter(|handle| !discovered_handles.contains(handle))
            .collect::<Vec<_>>();
        for handle in &removed {
            self.windows.remove(handle);
            self.parked_rects.remove(handle);
            self.remove_from_layout(*handle);
            self.insertion_directions.remove(handle);
            self.minimum_sizes.remove(handle);
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
                set_managed_window_transitions(handle, true);
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
                            workspace = self.next_available_workspace();
                            if let Some(window) = self.windows.get_mut(&handle) {
                                window.workspace = workspace;
                            }
                            self.insert_into_layout(workspace, handle, None, None, true);
                        }
                    }
                } else if should_center {
                    self.center_floating_window(handle);
                }
                newest_window = Some((handle, workspace));
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
        } else if !removed.is_empty() {
            self.focus_active_replacement();
        }

        let foreground = unsafe { GetForegroundWindow() };
        let foreground_handle = self.last_foreground_event
            .filter(|(_, received)| received.elapsed() < Duration::from_millis(100))
            .map(|(handle, _)| handle)
            .or_else(|| (!foreground.is_invalid()).then_some(foreground.0 as isize));
        let mut focused = foreground_handle
            .filter(|handle| self.windows.contains_key(handle));
        if let Some(handle) = focused
            && self.windows.get(&handle).is_some_and(|window| window.workspace != self.active_workspace)
        {
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
        if self.focused != focused {
            self.focused = focused;
            changed = true;
            if let Some(handle) = focused {
                let direction = *self
                    .insertion_directions
                    .entry(handle)
                    .or_insert(TilingDirection::Horizontal);
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
        if let Some(root) = self.layouts.get_mut(&workspace) {
            let mut leaves = Vec::new();
            root.leaves(&mut leaves);
            let target = preferred_target.filter(|candidate| root.contains(*candidate))
                .or_else(|| self.last_focused.get(&workspace).copied().filter(|candidate| root.contains(*candidate)))
                .or_else(|| leaves.last().copied());
            if let Some(target) = target {
                let direction = forced_direction
                    .or_else(|| self.insertion_directions.get(&target).copied())
                    .unwrap_or(self.direction);
                let _ = root.insert_beside(target, handle, direction, after);
            }
        } else {
            self.layouts.insert(workspace, LayoutNode::Leaf(handle));
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
        let Some((workspace, handle, started)) = self.pending_workspace_focus else { return; };
        if started.elapsed() > Duration::from_millis(1_000)
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
            area.top = area.top.max(info.rcMonitor.top + 41);
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
        unsafe {
            let _ = SetWindowPos(
                hwnd(handle),
                None,
                -32_000,
                -32_000,
                (rect.right - rect.left).max(64),
                (rect.bottom - rect.top).max(64),
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
        if self.windows.remove(&handle).is_none() {
            return false;
        }
        self.remove_from_layout(handle);
        self.parked_rects.remove(&handle);
        self.insertion_directions.remove(&handle);
        self.minimum_sizes.remove(&handle);
        self.taskbar_hidden.remove(&handle);
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
        if !self.forget_window(handle) {
            return;
        }
        self.closing.insert(handle);
        unsafe {
            let _ = PostMessageW(hwnd(handle), WM_CLOSE, WPARAM(0), LPARAM(0));
        }
        if !self.paused {
            self.tile_active_workspace();
        }
        self.focus_active_replacement();
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
        let preferred = self.last_focused.get(&self.active_workspace).copied()
            .filter(|handle| self.windows.get(handle).is_some_and(|window| {
                window.workspace == self.active_workspace && !self.closing.contains(handle)
            }));
        let target = preferred.or_else(|| {
            let mut leaves = Vec::new();
            self.layouts.get(&self.active_workspace)?.leaves(&mut leaves);
            leaves.into_iter().rev().find(|handle| self.windows.contains_key(handle))
        });
        if let Some(handle) = target {
            focus_native_window(handle);
            self.focused = Some(handle);
            self.last_focused.insert(self.active_workspace, handle);
            self.pending_workspace_focus = Some((
                self.active_workspace,
                handle,
                Instant::now(),
            ));
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
            && root.resize_for(handle, TilingDirection::Horizontal, width_delta);
        let changed_y = height_delta.abs() > f32::EPSILON
            && root.resize_for(handle, TilingDirection::Vertical, height_delta);
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
            root.rects(area, &mut rects);
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
            area.top = area.top.max(monitor_info.rcMonitor.top + 41);
        }
        Some(LayoutRect {
            left: area.left + TILE_GAP,
            top: area.top + TILE_GAP,
            right: area.right - TILE_GAP,
            bottom: area.bottom - TILE_GAP,
        })
    }

    fn layout_rects(&self, workspace: usize) -> Vec<(isize, LayoutRect)> {
        let mut output = Vec::new();
        if let (Some(root), Some(area)) = (self.layouts.get(&workspace), self.workspace_area(workspace)) {
            root.rects(area, &mut output);
        }
        output
    }

    fn tile_workspace(&self, workspace: usize) {
        use windows::Win32::UI::WindowsAndMessaging::{
            HWND_NOTOPMOST, SWP_NOACTIVATE, SWP_NOOWNERZORDER, SWP_NOSENDCHANGING, SetWindowPos,
        };
        for (handle, rect) in self.layout_rects(workspace) {
            if !self.windows.get(&handle).is_some_and(|window| !window.floating && window.fullscreen_restore.is_none()) { continue; }
            let placement = window_placement_for_visible_rect(handle, rect);
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
        self.apply_borders();
    }

    fn reconcile_tiled_constraints(&mut self) -> bool {
        let Some(area) = self.workspace_area(self.active_workspace) else { return false; };
        let expected = self.layout_rects(self.active_workspace);
        let mut adjustment = None;
        for (handle, rect) in expected {
            if self.windows.get(&handle).is_some_and(|window| self.minimum_size_ignored(&window.process_name)) {
                continue;
            }
            let Some(actual) = visible_window_rect(handle) else { continue; };
            let width_growth = (actual.right - actual.left) - (rect.right - rect.left);
            let height_growth = (actual.bottom - actual.top) - (rect.bottom - rect.top);
            // Only absorb app-enforced growth. Shrinkage is normally a transient
            // placement frame and should still be corrected to the tree geometry.
            if width_growth > 4 || height_growth > 4 {
                let outer = window_placement_for_visible_rect(handle, actual);
                adjustment = Some((
                    handle,
                    width_growth.max(0),
                    height_growth.max(0),
                    (outer.right - outer.left, outer.bottom - outer.top),
                ));
                break;
            }
        }
        let Some((handle, width_growth, height_growth, inferred_minimum)) = adjustment else { return false; };
        let minimum = self.minimum_sizes.entry(handle).or_insert((64, 64));
        minimum.0 = minimum.0.max(inferred_minimum.0);
        minimum.1 = minimum.1.max(inferred_minimum.1);
        let Some(root) = self.layouts.get_mut(&self.active_workspace) else { return false; };
        let mut changed = false;
        if width_growth > 4 {
            changed |= root.resize_for(
                handle,
                TilingDirection::Horizontal,
                width_growth as f32 / (area.right - area.left).max(1) as f32,
            );
        }
        if height_growth > 4 {
            changed |= root.resize_for(
                handle,
                TilingDirection::Vertical,
                height_growth as f32 / (area.bottom - area.top).max(1) as f32,
            );
        }
        if changed {
            self.tile_active_workspace();
        }
        changed
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
        root.rects(area, &mut rects);
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
        for window in self.windows.values() {
            let color = if self.focused == Some(window.handle) {
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
        self.last_foreground_event = Some((handle, Instant::now()));
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
        (205, "Tiling direction"), (212, "Toggle floating"),
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
        (206, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, 0x20),
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
                EVENT_SYSTEM_FOREGROUND, EVENT_SYSTEM_MOVESIZEEND, EVENT_SYSTEM_MOVESIZESTART,
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
        (206, MOD_ALT | MOD_SHIFT | MOD_NOREPEAT, 0x20),
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
    let mut last_border_refresh = Instant::now() - Duration::from_secs(1);
    let mut last_composition_refresh = Instant::now() - Duration::from_secs(1);
    let mut last_fallback_scan = Instant::now() - Duration::from_secs(1);
    WINDOW_EVENT_DIRTY.store(true, Ordering::Release);

    while running.load(Ordering::Acquire) {
        let mut force_publish = false;
        let queued_events = WINDOW_EVENTS.get_or_init(Default::default)
            .lock().map(|mut events| std::mem::take(&mut *events)).unwrap_or_default();
        for (event, handle) in queued_events {
            if event == EVENT_SYSTEM_FOREGROUND {
                manager.apply_foreground_event(handle);
                force_publish = true;
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
                    force_publish = true;
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
                        if manager.toggle_floating() {
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
                force_publish = true;
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
            manager.enforce_workspace_visibility();
            if !manager.paused && manager.dragging.is_none() {
                let has_forced_window = manager.windows.values().any(|window| {
                    window.workspace == manager.active_workspace
                        && !window.floating
                        && manager.minimum_size_ignored(&window.process_name)
                });
                if has_forced_window {
                    manager.tile_workspace(manager.active_workspace);
                }
                // Firefox-family windows can enforce a chrome minimum after
                // placement. Absorb that once into the split tree instead of
                // fighting the app between two sizes forever.
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
        EVENT_OBJECT_DESTROY, EVENT_SYSTEM_FOREGROUND, EVENT_SYSTEM_MOVESIZEEND,
        EVENT_SYSTEM_MOVESIZESTART, OBJID_WINDOW,
    };
    if event == EVENT_SYSTEM_FOREGROUND {
        if let Ok(mut events) = WINDOW_EVENTS.get_or_init(Default::default).lock() {
            events.push((event, event_hwnd.0 as isize));
        }
    } else if event == EVENT_SYSTEM_MOVESIZESTART || event == EVENT_SYSTEM_MOVESIZEEND {
        if !event_hwnd.is_invalid() {
            if let Ok(mut events) = WINDOW_EVENTS.get_or_init(Default::default).lock() {
                events.push((event, event_hwnd.0 as isize));
            }
        }
    }
    if event == EVENT_OBJECT_DESTROY
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
fn inspect_window(handle: windows::Win32::Foundation::HWND) -> Option<ManagedWindow> {
    use windows::Win32::{
        Graphics::Dwm::{DWMWA_CLOAKED, DwmGetWindowAttribute},
        UI::WindowsAndMessaging::{
            GWL_EXSTYLE, GWL_STYLE, GW_OWNER, GetClassNameW, GetWindow, GetWindowLongW,
            GetWindowRect, GetWindowTextLengthW, GetWindowTextW, IsWindowVisible, WS_CHILD,
            WS_EX_TOOLWINDOW, WS_THICKFRAME,
        },
    };

    if handle.is_invalid() || !unsafe { IsWindowVisible(handle) }.as_bool() {
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
    let shell_title = title.eq_ignore_ascii_case("Program Manager")
        || title.eq_ignore_ascii_case("System tray overflow window")
        || title.eq_ignore_ascii_case("Task Switching")
        || title.eq_ignore_ascii_case("Notification Center");
    let shell_class = matches!(
        class_name.as_str(),
        "Progman" | "WorkerW" | "Shell_TrayWnd" | "Shell_SecondaryTrayWnd"
            | "TopLevelWindowForOverflowXamlIsland" | "MultitaskingViewFrame"
    );
    if title.is_empty() || title.starts_with("Overbar") || shell_title || shell_class {
        return None;
    }
    let process_name = window_process_name(handle).unwrap_or_else(|| "Application".into());
    let process_name = if process_name.eq_ignore_ascii_case("ApplicationFrameHost.exe") {
        title.clone()
    } else {
        process_name.trim_end_matches(".exe").to_owned()
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
    })
}

#[cfg(target_os = "windows")]
fn window_process_name(handle: windows::Win32::Foundation::HWND) -> Option<String> {
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
            Input::KeyboardAndMouse::{SetActiveWindow, SetFocus},
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
            let _ = SetActiveWindow(target);
            let _ = SetFocus(target);
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
        let _ = SetActiveWindow(target);
        let _ = SetFocus(target);

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
            &mut rects,
        );
        let left = rects.iter().find(|(handle, _)| *handle == 1).unwrap().1;
        let right = rects.iter().find(|(handle, _)| *handle == 2).unwrap().1;
        assert!(left.right - left.left > right.right - right.left);
        assert_eq!(right.left - left.right, TILE_GAP);
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
