#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

mod window_manager;

use chrono::{Datelike, Local};
use eframe::{
    App, NativeOptions,
    egui::{
        Align, CentralPanel, Color32, ColorImage, Context, CornerRadius, CursorIcon, FontData,
        FontDefinitions, FontFamily, FontId, Frame, Layout, Margin, RichText, ScrollArea, Sense,
        Stroke, TextEdit, TextureHandle, TextureOptions, UiBuilder, Vec2, ViewportBuilder,
        ViewportCommand, ViewportId,
        viewport::WindowLevel,
    },
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::{
    collections::{HashMap, HashSet},
    env,
    fs,
    hash::{Hash, Hasher},
    io::{BufReader, BufWriter, Read, Write},
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc::{self, Receiver, Sender},
    },
    thread,
    time::{Duration, Instant},
};
use sysinfo::{Components, DiskKind, Disks, Networks, Pid, ProcessesToUpdate, System};

// 36 logical points is about 41 physical pixels at this display's 110-DPI scale.
const BAR_HEIGHT: f32 = 36.0;
// The bar itself is colorless; Windows supplies only the blur-behind effect.
const BAR_BACKGROUND: Color32 = Color32::TRANSPARENT;
// With the 3-point margins below this produces a 27-point / ~31-pixel pill.
const PILL_CONTENT_HEIGHT: f32 = 21.0;
const WORKSPACE_WIDTH: f32 = 22.0;
const WORKSPACE_SLIDE_SECONDS: f32 = 0.17;
const WORKSPACE_GROW_SECONDS: f32 = 0.2;
const DIRECTION_TURN_SECONDS: f32 = 0.17;
const STAT_LABEL_VALUE_GAP: f32 = 5.0;
const STAT_GROUP_GAP: f32 = 11.0;
const VOLUME_COLLAPSED_WIDTH: f32 = 29.0;
const VOLUME_EXPANDED_WIDTH: f32 = 166.0;
const PANEL_WIDTH: f32 = 395.0;
const PANEL_HEIGHT: f32 = 225.0;
const PANEL_GAP: f32 = 6.0;
const PANEL_OPEN_SECONDS: f32 = 0.2;
const POWER_PANEL_FADE_SECONDS: f32 = 0.22;
const POWER_ACTION_DELAY_SECONDS: u32 = 3;
const APPS_PANEL_WIDTH: f32 = 440.0;
const APPS_PANEL_HEIGHT: f32 = 390.0;
const WM_SETTINGS_PANEL_HEIGHT: f32 = 520.0;
const WM_SETTINGS_TRANSITION_SECONDS: f32 = 0.28;
const SEARCH_PANEL_WIDTH: f32 = 520.0;
const SEARCH_PANEL_HEIGHT: f32 = 330.0;
const SEARCH_PANEL_OPEN_SECONDS: f32 = 0.18;
const SEARCH_PANEL_CLOSE_SECONDS: f32 = 0.13;
const BAR_SLIDE_SECONDS: f32 = 0.18;
const UPDATE_CHECK_INTERVAL: Duration = Duration::from_secs(6 * 60 * 60);
const UPDATE_API_URL: &str = "https://api.github.com/repos/Respite09/Overbar/releases/latest";
const UPDATE_DOWNLOAD_PREFIX: &str =
    "https://github.com/Respite09/Overbar/releases/download/";
const TEXT_PRIMARY: Color32 = Color32::from_rgb(225, 231, 236);
const TEXT_MUTED: Color32 = Color32::from_rgb(180, 193, 201);
const STAT_LABEL: Color32 = Color32::from_rgba_premultiplied(127, 136, 142, 180);
const USAGE_WARNING: Color32 = Color32::from_rgb(208, 135, 112);
const USAGE_CRITICAL: Color32 = Color32::from_rgb(191, 97, 106);
const DEFAULT_ACCENT: Color32 = Color32::from_rgb(105, 184, 197);
const UPDATE_NOTICE: Color32 = Color32::from_rgb(235, 203, 92);
const UPDATE_COMPLETE: Color32 = Color32::from_rgb(163, 190, 140);
const BAR_FONT_SIZE: f32 = 11.0;

fn pill_background() -> Color32 {
    // #090b0f5c (unpremultiplied RGBA).
    Color32::from_rgba_unmultiplied(0x09, 0x0b, 0x0f, 0x5c)
}

fn physical_pixels(ui: &eframe::egui::Ui, pixels: f32) -> f32 {
    pixels / ui.ctx().pixels_per_point()
}

fn configure_fonts(ctx: &Context) {
    let Ok(symbol_font) = std::fs::read(r"C:\Windows\Fonts\seguisym.ttf") else {
        return;
    };
    let family = FontFamily::Name("power-symbols".into());
    let mut fonts = FontDefinitions::default();
    fonts.font_data.insert(
        "segoe-ui-symbol".into(),
        Arc::new(FontData::from_owned(symbol_font)),
    );
    fonts
        .families
        .insert(family, vec!["segoe-ui-symbol".into()]);
    ctx.set_fonts(fonts);
}

fn trigger_power_action(action: PowerAction) {
    #[cfg(target_os = "windows")]
    unsafe {
        use windows::Win32::{
            System::{
                Power::SetSuspendState,
                Shutdown::{
                    EWX_FORCEIFHUNG, EWX_LOGOFF, ExitWindowsEx, LockWorkStation,
                    SHUTDOWN_REASON,
                },
            },
        };

        match action {
            PowerAction::Lock => {
                let _ = LockWorkStation();
            }
            PowerAction::Sleep => {
                let _ = SetSuspendState(false, false, false);
            }
            PowerAction::Hibernate => {
                let _ = SetSuspendState(true, false, false);
            }
            PowerAction::Shutdown => {
                let _ = schedule_system_power_action(PowerAction::Shutdown, 0);
            }
            PowerAction::Restart => {
                let _ = schedule_system_power_action(PowerAction::Restart, 0);
            }
            PowerAction::SignOut => {
                let _ = ExitWindowsEx(EWX_LOGOFF | EWX_FORCEIFHUNG, SHUTDOWN_REASON(0));
            }
        }
    }

    #[cfg(not(target_os = "windows"))]
    let _ = action;
}

#[cfg(target_os = "windows")]
fn schedule_system_power_action(action: PowerAction, delay_seconds: u32) -> bool {
    let operation = match action {
        PowerAction::Shutdown => "/s",
        PowerAction::Restart => "/r",
        _ => return false,
    };
    let mut command = Command::new("shutdown.exe");
    command.args([
        operation,
        "/f",
        "/t",
        &delay_seconds.to_string(),
    ]);
    command.stdout(Stdio::null()).stderr(Stdio::null());
    hide_child_console(&mut command);
    command.spawn().is_ok()
}

#[cfg(not(target_os = "windows"))]
fn schedule_system_power_action(_action: PowerAction, _delay_seconds: u32) -> bool {
    false
}

fn smootherstep(value: f32) -> f32 {
    value * value * value * (value * (value * 6.0 - 15.0) + 10.0)
}

fn ease_out_cubic(value: f32) -> f32 {
    1.0 - (1.0 - value).powi(3)
}

fn usage_color(percent: f32) -> Color32 {
    if percent >= 85.0 {
        USAGE_CRITICAL
    } else if percent >= 70.0 {
        USAGE_WARNING
    } else {
        TEXT_PRIMARY
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct WorkspaceEntry {
    name: String,
    active: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct AppEntry {
    window_id: String,
    window_handle: Option<isize>,
    title: String,
    process_name: String,
    workspace: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct WorkspacesState {
    items: Vec<WorkspaceEntry>,
    active: usize,
    apps: Vec<AppEntry>,
}

#[derive(Clone, Debug, Deserialize)]
struct GithubReleaseAsset {
    name: String,
    browser_download_url: String,
    size: u64,
    #[serde(default)]
    digest: Option<String>,
}

#[derive(Clone, Debug, Deserialize)]
struct GithubRelease {
    tag_name: String,
    html_url: String,
    assets: Vec<GithubReleaseAsset>,
}

#[derive(Clone, Debug)]
struct AvailableUpdate {
    version: String,
    download_url: String,
    size: u64,
    digest: Option<String>,
    release_url: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct CompletedUpdate {
    version: String,
    release_url: String,
}

enum UpdateRequest {
    Install(AvailableUpdate),
}

enum UpdateEvent {
    CheckFinished(Result<Option<AvailableUpdate>, String>),
    ReadyToRestart,
    InstallFailed(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum UpdateNotice {
    Available,
    Failed,
    Complete,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum PanelTab {
    #[default]
    Stats,
    Storage,
    Network,
    Tasks,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum TaskSort {
    #[default]
    Name,
    Memory,
    Cpu,
}

#[derive(Clone, Debug)]
struct TaskEntry {
    pid: u32,
    name: String,
    memory: u64,
    cpu: f32,
    can_end: bool,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
struct SearchResults {
    query: String,
    pins: Vec<SearchEntry>,
    recents: Vec<SearchEntry>,
    apps: Vec<SearchEntry>,
    files: Vec<SearchEntry>,
    pinned_paths: Vec<PathBuf>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct SearchEntry {
    name: String,
    path: PathBuf,
    #[serde(default)]
    name_lower: String,
    #[serde(default)]
    path_lower: String,
}

impl SearchEntry {
    fn new(name: String, path: PathBuf) -> Self {
        let name_lower = name.to_ascii_lowercase();
        let path_lower = path.to_string_lossy().to_ascii_lowercase();
        Self {
            name,
            path,
            name_lower,
            path_lower,
        }
    }
}

#[derive(Deserialize, Serialize)]
struct StoredSearchIndex {
    version: u32,
    apps: Vec<SearchEntry>,
    files: Vec<SearchEntry>,
}

#[derive(Clone, Default, Deserialize, Serialize)]
struct StoredSearchPreferences {
    version: u32,
    #[serde(default)]
    selections: HashMap<String, PathBuf>,
    #[serde(default)]
    pins: Vec<SearchEntry>,
    #[serde(default)]
    recents: Vec<SearchEntry>,
    #[serde(default)]
    cached_queries: HashMap<String, SearchResults>,
    #[serde(default)]
    command_selections: HashMap<String, String>,
}

const SEARCH_INDEX_VERSION: u32 = 3;
const SEARCH_INDEX_CHECKPOINT_INTERVAL: Duration = Duration::from_secs(30);
const SEARCH_INDEX_REFRESH_INTERVAL: Duration = Duration::from_secs(60);
const SEARCH_PREFERENCES_VERSION: u32 = 2;
const SEARCH_RECENT_LIMIT: usize = 15;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum TilingDirection {
    #[default]
    Horizontal,
    Vertical,
}

const DEFAULT_WM_GAP: i32 = 18;
const DEFAULT_MEDIA_NAME_WIDTH: f32 = 210.0;

fn default_wm_gap() -> i32 {
    DEFAULT_WM_GAP
}

fn default_media_name_width() -> f32 {
    DEFAULT_MEDIA_NAME_WIDTH
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct WmConfig {
    #[serde(default = "default_wm_keybindings")]
    keybindings: HashMap<String, String>,
    #[serde(default)]
    ignore_minimum_size_apps: Vec<String>,
    #[serde(default)]
    window_floating_states: HashMap<String, bool>,
    #[serde(default)]
    centered_window_types: HashSet<String>,
    #[serde(default = "default_wm_gap")]
    window_gap: i32,
    #[serde(default = "default_media_name_width")]
    media_name_width: f32,
}

impl Default for WmConfig {
    fn default() -> Self {
        Self {
            keybindings: default_wm_keybindings(),
            ignore_minimum_size_apps: Vec::new(),
            window_floating_states: HashMap::new(),
            centered_window_types: HashSet::new(),
            window_gap: default_wm_gap(),
            media_name_width: default_media_name_width(),
        }
    }
}

fn default_wm_keybindings() -> HashMap<String, String> {
    [
        ("Focus left", "Alt+H"), ("Focus right", "Alt+L"),
        ("Focus up", "Alt+K"), ("Focus down", "Alt+J"),
        ("Move left", "Alt+Shift+H"), ("Move right", "Alt+Shift+L"),
        ("Move up", "Alt+Shift+K"), ("Move down", "Alt+Shift+J"),
        ("Tiling direction", "Alt+V"), ("Set Tiled", "Alt+T"),
        ("Cycle tiled/floating", "Alt+Shift+Space"),
        ("Fullscreen", "Alt+F"), ("Minimize", "Alt+M"),
        ("Close", "Alt+Shift+Q"), ("Previous workspace", "Alt+A"),
        ("Next workspace", "Alt+S"), ("Recent workspace", "Alt+D"),
        ("Retile", "Alt+Shift+W"), ("Resize mode", "Alt+R"),
        ("Center floating window", "Alt+Shift+C"),
    ].into_iter().map(|(name, binding)| (name.into(), binding.into())).collect()
}

enum WindowManagerUpdate {
    Workspaces(WorkspacesState),
    TilingDirection(TilingDirection),
    Floating(bool),
    ResizeMode(bool),
    LayoutChanged,
    ConfigChanged(WmConfig),
    BarVisibility(bool),
}

#[derive(Clone, Debug)]
enum WindowManagerCommand {
    FocusWorkspace(String),
    FocusWindow { handle: isize, workspace: String },
    CloseWindow(isize),
    ToggleTilingDirection,
    ToggleFloating,
    UpdateConfig(WmConfig),
}

enum SearchAction {
    Open(SearchEntry),
    Reveal(PathBuf),
    TogglePin(SearchEntry),
    Kill { pid: u32, name: String },
    CopyCalculation(String),
    RunCommand(LauncherCommandAction),
}

#[derive(Clone, Debug)]
enum LauncherCommandAction {
    Power(PowerAction),
    OpenTarget(String),
    Quit,
    WebSearch(String),
}

#[derive(Clone, Debug)]
struct LauncherCommand {
    name: String,
    detail: String,
    action: LauncherCommandAction,
}

enum SearchWorkerRequest {
    Query(String),
    RecordSelection { query: String, entry: SearchEntry },
    TogglePin(SearchEntry),
    RecordCommandSelection { query: String, process_name: String },
}

#[derive(Clone, Copy, Default)]
struct SearchResultClicks {
    primary: bool,
    secondary: bool,
    pin: bool,
}

#[derive(Clone, Copy, Debug)]
struct AudioState {
    volume: f32,
    muted: bool,
}

enum AudioCommand {
    SetVolume(f32),
}

#[derive(Clone, Debug)]
struct MediaState {
    title: String,
    artist: String,
    playing: bool,
    position_seconds: f64,
    duration_seconds: f64,
}

enum MediaCommand {
    TogglePlayPause,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PowerAction {
    Lock,
    Sleep,
    Hibernate,
    Shutdown,
    Restart,
    SignOut,
}

struct OverbarApp {
    workspaces: WorkspacesState,
    active_title: String,
    cpu_percent: f32,
    cpu_temperature: Option<f32>,
    ram_percent: f32,
    battery_percent: Option<u8>,
    accent_color: Color32,
    system: System,
    disks: Disks,
    networks: Networks,
    temperature_updates: Receiver<Option<f32>>,
    audio_updates: Receiver<AudioState>,
    audio_commands: Sender<AudioCommand>,
    media_updates: Receiver<Option<MediaState>>,
    media_commands: Sender<MediaCommand>,
    media: Option<MediaState>,
    media_updated_at: Instant,
    media_raw_position: Option<f64>,
    media_icon_mix_from: f32,
    media_icon_mix_to: f32,
    media_icon_transition_started: Instant,
    media_scroll_label: String,
    media_scroll_started: Instant,
    play_icon: TextureHandle,
    pause_icon: TextureHandle,
    volume: f32,
    volume_muted: bool,
    volume_expanded: bool,
    volume_last_hovered: Instant,
    panel_open: bool,
    panel_opened_at: Instant,
    stats_pill_rect: eframe::egui::Rect,
    apps_panel_open: bool,
    apps_panel_opened_at: Instant,
    apps_icon_clicked_at: Instant,
    apps_icon_rect: eframe::egui::Rect,
    power_panel_open: bool,
    power_panel_closing: bool,
    power_panel_opened_at: Instant,
    pending_power_action: Option<PowerAction>,
    scheduled_power_action: Option<PowerAction>,
    scheduled_power_action_started: Option<Instant>,
    power_button_rect: eframe::egui::Rect,
    lock_icon: TextureHandle,
    sleep_icon: TextureHandle,
    restart_icon: TextureHandle,
    shutdown_icon: TextureHandle,
    wm_settings_open: bool,
    wm_settings_closing: bool,
    wm_settings_transition_started: Instant,
    wm_config: WmConfig,
    startup_task_requests: Sender<()>,
    startup_task_updates: Receiver<Result<PathBuf, String>>,
    startup_task_in_progress: bool,
    startup_task_status: Option<(bool, String)>,
    update_requests: Sender<UpdateRequest>,
    update_events: Receiver<UpdateEvent>,
    available_update: Option<AvailableUpdate>,
    completed_update: Option<CompletedUpdate>,
    update_in_progress: bool,
    update_error: Option<String>,
    update_error_copied_at: Option<Instant>,
    update_notice: Option<UpdateNotice>,
    update_notice_seen_in_menu: bool,
    completed_update_seen_in_menu: bool,
    settings_icon: TextureHandle,
    app_icons: HashMap<isize, TextureHandle>,
    panel_tab: PanelTab,
    task_sort: TaskSort,
    task_sort_ascending: bool,
    task_end_permissions: HashMap<u32, bool>,
    window_manager_updates: Receiver<WindowManagerUpdate>,
    window_manager_commands: Sender<WindowManagerCommand>,
    title_updates: Receiver<String>,
    runtime_running: Arc<AtomicBool>,
    workspace_births: HashMap<String, Instant>,
    workspace_slot_count: usize,
    indicator_from: f32,
    indicator_to: f32,
    indicator_started: Instant,
    direction: TilingDirection,
    direction_angle_from: f32,
    direction_angle_to: f32,
    direction_angle_started: Instant,
    focused_floating: bool,
    resize_mode_active: bool,
    tiled_icon: TextureHandle,
    floating_icon: TextureHandle,
    last_metrics_refresh: Instant,
    search_active: bool,
    search_panel_closing: bool,
    search_panel_animation_started: Instant,
    // Automatically opens and closes the search panel once, right at launch,
    // so whatever one-time setup cost the first real search activation pays
    // (focus-stealing, IME, GPU surface, etc.) happens during startup instead
    // of during the user's own first Alt+Space.
    // 0 = not started, 1 = opened and waiting to auto-close, 2 = done.
    startup_search_warmup_stage: u8,
    startup_search_warmup_started: Instant,
    search_query: String,
    search_focus_pending: bool,
    search_focus_attempts: u8,
    search_selected: usize,
    search_scroll_to_selected: bool,
    search_text_transition_started: Instant,
    search_last_empty: bool,
    search_trigger_rect: eframe::egui::Rect,
    pin_icon: TextureHandle,
    pin_filled_icon: TextureHandle,
    search_icons: HashMap<PathBuf, TextureHandle>,
    search_icon_pending: HashSet<PathBuf>,
    search_icon_failed: HashSet<PathBuf>,
    search_icon_requests: Sender<PathBuf>,
    search_icon_updates: Receiver<(PathBuf, Option<ColorImage>)>,
    search_home: SearchResults,
    search_cached_queries: HashMap<String, SearchResults>,
    search_command_selections: HashMap<String, String>,
    search_results: SearchResults,
    search_requests: Sender<SearchWorkerRequest>,
    search_updates: Receiver<SearchResults>,
    search_shortcuts: Receiver<()>,
    last_bar_monitor_size: Option<Vec2>,
    bar_auto_hidden: bool,
    bar_slide_from: f32,
    bar_slide_to: f32,
    bar_slide_started: Instant,
    last_bar_position_y: Option<f32>,
}

impl OverbarApp {
    fn new(cc: &eframe::CreationContext<'_>) -> Self {
        let mut visuals = eframe::egui::Visuals::dark();
        visuals.panel_fill = Color32::TRANSPARENT;
        visuals.window_fill = Color32::from_rgba_unmultiplied(9, 11, 15, 172);
        visuals.window_stroke = Stroke::NONE;
        visuals.window_corner_radius = CornerRadius::same(5);
        visuals.popup_shadow = eframe::egui::epaint::Shadow::NONE;
        let mut style = (*cc.egui_ctx.style()).clone();
        style.visuals = visuals;
        style.spacing.menu_margin = Margin::symmetric(7, 4);
        cc.egui_ctx.set_style(style);
        configure_fonts(&cc.egui_ctx);

        #[cfg(target_os = "windows")]
        configure_windows_overlay(cc);

        let mut system = System::new_all();
        let disks = Disks::new_with_refreshed_list();
        let networks = Networks::new_with_refreshed_list();
        // The first CPU reading establishes a baseline; later readings use its delta.
        system.refresh_cpu_usage();

        let wm_config = load_wm_config();
        let (startup_task_requests, startup_task_updates) =
            spawn_startup_task_worker(cc.egui_ctx.clone());
        let (update_requests, update_events) = spawn_update_worker(cc.egui_ctx.clone());
        let completed_update = load_completed_update();
        // The handoff marker is single-use: completion is surfaced only by
        // the first process launched after that update, never a later run.
        // Invalid/mismatched markers are consumed too, so an older binary can
        // never show both "Update Complete" and "Update Available".
        clear_completed_update_marker();
        let (window_manager_commands, window_manager_updates, runtime_running) =
            window_manager::spawn(cc.egui_ctx.clone(), wm_config.clone());
        let title_updates = spawn_title_worker(
            cc.egui_ctx.clone(),
            Arc::clone(&runtime_running),
        );
        let temperature_updates = spawn_temperature_worker(
            cc.egui_ctx.clone(),
            Arc::clone(&runtime_running),
        );
        let (audio_commands, audio_updates) = spawn_audio_worker(
            cc.egui_ctx.clone(),
            Arc::clone(&runtime_running),
        );
        let (media_commands, media_updates) = spawn_media_worker(
            cc.egui_ctx.clone(),
            Arc::clone(&runtime_running),
        );
        let (search_requests, search_updates) = spawn_search_worker(cc.egui_ctx.clone());
        let stored_search_preferences = load_search_preferences();
        let search_home = search_home_results(&stored_search_preferences);
        let search_command_selections = stored_search_preferences.command_selections.clone();
        let search_cached_queries = stored_search_preferences.cached_queries;
        let (search_icon_requests, search_icon_updates) =
            spawn_search_icon_worker(cc.egui_ctx.clone());
        let search_shortcuts = spawn_search_shortcut_worker(
            cc.egui_ctx.clone(),
            Arc::clone(&runtime_running),
        );
        let pin_icon = cc.egui_ctx.load_texture(
            "overbar-pin-svg",
            ColorImage::from_rgba_unmultiplied(
                [24, 24],
                include_bytes!("../assets/pin.rgba"),
            ),
            TextureOptions::LINEAR,
        );
        let pin_filled_icon = cc.egui_ctx.load_texture(
            "overbar-pin-svg-filled",
            ColorImage::from_rgba_unmultiplied(
                [24, 24],
                include_bytes!("../assets/pin-filled.rgba"),
            ),
            TextureOptions::LINEAR,
        );
        let play_icon = cc.egui_ctx.load_texture(
            "overbar-play-svg",
            ColorImage::from_rgba_unmultiplied([24, 24], include_bytes!("../assets/play.rgba")),
            TextureOptions::LINEAR,
        );
        let pause_icon = cc.egui_ctx.load_texture(
            "overbar-pause-svg",
            ColorImage::from_rgba_unmultiplied([24, 24], include_bytes!("../assets/pause.rgba")),
            TextureOptions::LINEAR,
        );
        let tiled_icon = cc.egui_ctx.load_texture(
            "overbar-tiled-svg",
            ColorImage::from_rgba_unmultiplied(
                [24, 24],
                include_bytes!("../assets/tiled.rgba"),
            ),
            TextureOptions::LINEAR,
        );
        let floating_icon = cc.egui_ctx.load_texture(
            "overbar-floating-svg",
            ColorImage::from_rgba_unmultiplied(
                [24, 24],
                include_bytes!("../assets/floating.rgba"),
            ),
            TextureOptions::LINEAR,
        );
        let settings_icon = cc.egui_ctx.load_texture(
            "overbar-settings-svg",
            ColorImage::from_rgba_unmultiplied(
                [24, 24],
                include_bytes!("../assets/settings.rgba"),
            ),
            TextureOptions::LINEAR,
        );
        let lock_icon = cc.egui_ctx.load_texture(
            "overbar-lock-svg",
            ColorImage::from_rgba_unmultiplied([96, 96], include_bytes!("../assets/lock.rgba")),
            TextureOptions::LINEAR,
        );
        let sleep_icon = cc.egui_ctx.load_texture(
            "overbar-sleep-svg",
            ColorImage::from_rgba_unmultiplied([96, 96], include_bytes!("../assets/sleep.rgba")),
            TextureOptions::LINEAR,
        );
        let restart_icon = cc.egui_ctx.load_texture(
            "overbar-restart-svg",
            ColorImage::from_rgba_unmultiplied(
                [96, 96],
                include_bytes!("../assets/restart.rgba"),
            ),
            TextureOptions::LINEAR,
        );
        let shutdown_icon = cc.egui_ctx.load_texture(
            "overbar-shutdown-svg",
            ColorImage::from_rgba_unmultiplied(
                [96, 96],
                include_bytes!("../assets/shutdown.rgba"),
            ),
            TextureOptions::LINEAR,
        );

        let workspaces = WorkspacesState {
                items: vec![WorkspaceEntry {
                    name: "1".to_owned(),
                    active: true,
                }],
                active: 0,
                apps: Vec::new(),
            };
        let already_visible = Instant::now() - Duration::from_secs(1);
        let workspace_births = workspaces
            .items
            .iter()
            .map(|workspace| (workspace.name.clone(), already_visible))
            .collect();
        Self {
            workspaces,
            active_title: "Desktop".into(),
            cpu_percent: 0.0,
            cpu_temperature: None,
            ram_percent: 0.0,
            battery_percent: battery_percent(),
            accent_color: windows_accent_color(),
            system,
            disks,
            networks,
            temperature_updates,
            audio_updates,
            audio_commands,
            media_updates,
            media_commands,
            media: None,
            media_updated_at: Instant::now(),
            media_raw_position: None,
            media_icon_mix_from: 0.0,
            media_icon_mix_to: 0.0,
            media_icon_transition_started: Instant::now(),
            media_scroll_label: String::new(),
            media_scroll_started: Instant::now(),
            play_icon,
            pause_icon,
            volume: 0.0,
            volume_muted: false,
            volume_expanded: false,
            volume_last_hovered: Instant::now(),
            panel_open: false,
            panel_opened_at: Instant::now(),
            stats_pill_rect: eframe::egui::Rect::NOTHING,
            apps_panel_open: false,
            apps_panel_opened_at: Instant::now(),
            apps_icon_clicked_at: Instant::now() - Duration::from_secs(1),
            apps_icon_rect: eframe::egui::Rect::NOTHING,
            power_panel_open: false,
            power_panel_closing: false,
            power_panel_opened_at: Instant::now(),
            pending_power_action: None,
            scheduled_power_action: None,
            scheduled_power_action_started: None,
            power_button_rect: eframe::egui::Rect::NOTHING,
            lock_icon,
            sleep_icon,
            restart_icon,
            shutdown_icon,
            wm_settings_open: false,
            wm_settings_closing: false,
            wm_settings_transition_started: Instant::now(),
            wm_config,
            startup_task_requests,
            startup_task_updates,
            startup_task_in_progress: false,
            startup_task_status: None,
            update_requests,
            update_events,
            available_update: None,
            update_notice: completed_update
                .as_ref()
                .map(|_| UpdateNotice::Complete),
            completed_update,
            update_in_progress: false,
            update_error: None,
            update_error_copied_at: None,
            update_notice_seen_in_menu: false,
            completed_update_seen_in_menu: false,
            settings_icon,
            app_icons: HashMap::new(),
            panel_tab: PanelTab::Stats,
            task_sort: TaskSort::Name,
            task_sort_ascending: true,
            task_end_permissions: HashMap::new(),
            window_manager_updates,
            window_manager_commands,
            title_updates,
            runtime_running,
            workspace_births,
            workspace_slot_count: 1,
            indicator_from: 0.0,
            indicator_to: 0.0,
            indicator_started: Instant::now(),
            direction: TilingDirection::Horizontal,
            direction_angle_from: 0.0,
            direction_angle_to: 0.0,
            direction_angle_started: Instant::now(),
            focused_floating: false,
            resize_mode_active: false,
            tiled_icon,
            floating_icon,
            last_metrics_refresh: Instant::now() - Duration::from_secs(1),
            search_active: false,
            search_panel_closing: false,
            search_panel_animation_started: Instant::now(),
            startup_search_warmup_stage: 0,
            startup_search_warmup_started: Instant::now(),
            search_query: String::new(),
            search_focus_pending: false,
            search_focus_attempts: 0,
            search_selected: 0,
            search_scroll_to_selected: false,
            search_text_transition_started: Instant::now(),
            search_last_empty: true,
            search_trigger_rect: eframe::egui::Rect::NOTHING,
            pin_icon,
            pin_filled_icon,
            search_icons: HashMap::new(),
            search_icon_pending: HashSet::new(),
            search_icon_failed: HashSet::new(),
            search_icon_requests,
            search_icon_updates,
            search_home,
            search_cached_queries,
            search_command_selections,
            search_results: SearchResults::default(),
            search_requests,
            search_updates,
            search_shortcuts,
            last_bar_monitor_size: None,
            bar_auto_hidden: false,
            bar_slide_from: 0.0,
            bar_slide_to: 0.0,
            bar_slide_started: Instant::now(),
            last_bar_position_y: None,
        }
    }

    fn refresh_metrics(&mut self) {
        self.system.refresh_cpu_usage();
        self.system.refresh_memory();
        self.system.refresh_processes(ProcessesToUpdate::All, true);
        let process_ids = self
            .system
            .processes()
            .keys()
            .map(|pid| pid.as_u32())
            .collect::<Vec<_>>();
        self.task_end_permissions
            .retain(|pid, _| process_ids.contains(pid));
        for pid in process_ids {
            self.task_end_permissions
                .entry(pid)
                .or_insert_with(|| process_can_terminate(pid));
        }
        self.disks.refresh();
        self.networks.refresh();

        self.cpu_percent = self.system.global_cpu_usage().clamp(0.0, 100.0);
        let total_ram = self.system.total_memory();
        self.ram_percent = if total_ram == 0 {
            0.0
        } else {
            (self.system.used_memory() as f64 / total_ram as f64 * 100.0) as f32
        };
        self.battery_percent = battery_percent();
        self.accent_color = windows_accent_color();
    }

    fn status_line(&self) -> String {
        let now = Local::now();
        format!(
            "{} {} {}",
            now.format("%a %b"),
            now.day(),
            now.format("%-I:%M %p")
        )
    }

    fn focus_workspace(&self, name: &str) {
        let _ = self
            .window_manager_commands
            .send(WindowManagerCommand::FocusWorkspace(name.to_owned()));
    }

    fn close_window(&self, id: &str) {
        if let Ok(handle) = id.parse::<isize>() {
            let _ = self
                .window_manager_commands
                .send(WindowManagerCommand::CloseWindow(handle));
        }
    }

    fn focus_window(&self, handle: isize, workspace: &str) {
        let _ = self
            .window_manager_commands
            .send(WindowManagerCommand::FocusWindow {
                handle,
                workspace: workspace.to_owned(),
            });
    }

    fn active_workspace_is_empty(&self) -> bool {
        let Some(workspace) = self.workspaces.items.get(self.workspaces.active) else {
            return true;
        };
        !self
            .workspaces
            .apps
            .iter()
            .any(|app| app.workspace == workspace.name)
    }

    fn activate_search(&mut self, ctx: &Context) {
        play_launcher_open_sound();
        if self.search_active {
            self.search_focus_pending = true;
            self.search_focus_attempts = 0;
            ctx.request_repaint();
            return;
        }
        self.search_active = true;
        self.search_panel_closing = false;
        self.search_panel_animation_started = Instant::now();
        self.search_focus_pending = true;
        self.search_focus_attempts = 0;
        self.search_selected = 0;
        self.search_scroll_to_selected = false;
        self.search_text_transition_started = Instant::now();
        self.panel_open = false;
        self.apps_panel_open = false;
        self.search_results = self.search_home.clone();
        let _ = self
            .search_requests
            .send(SearchWorkerRequest::Query(String::new()));
        ctx.request_repaint();
    }

    fn search_query_changed(&mut self) {
        self.search_selected = 0;
        self.search_scroll_to_selected = true;
        let cache_key = self.search_query.trim().to_ascii_lowercase();
        self.search_results = if launcher_command(&self.search_query).is_some() {
            SearchResults {
                query: self.search_query.clone(),
                ..Default::default()
            }
        } else if cache_key.is_empty() {
            self.search_home.clone()
        } else if let Some(cached) = self.search_cached_queries.get(&cache_key) {
            cached.clone()
        } else {
            SearchResults {
                query: self.search_query.clone(),
                ..Default::default()
            }
        };
        let _ = self
            .search_requests
            .send(SearchWorkerRequest::Query(self.search_query.clone()));
    }

    fn deactivate_search(&mut self, ctx: &Context) {
        self.finish_search(ctx, true);
    }

    fn remember_search_recent(&mut self, entry: SearchEntry) {
        self.search_home
            .recents
            .retain(|recent| recent.path != entry.path);
        if !self
            .search_home
            .pinned_paths
            .iter()
            .any(|path| path == &entry.path)
        {
            self.search_home.recents.insert(0, entry);
            self.search_home.recents.truncate(SEARCH_RECENT_LIMIT);
        }
    }

    fn toggle_search_pin_local(&mut self, entry: SearchEntry) {
        if let Some(index) = self
            .search_home
            .pins
            .iter()
            .position(|pinned| pinned.path == entry.path)
        {
            self.search_home.pins.remove(index);
        } else {
            self.search_home.pins.insert(0, entry.clone());
            self.search_home
                .recents
                .retain(|recent| recent.path != entry.path);
        }
        self.search_home.pinned_paths = self
            .search_home
            .pins
            .iter()
            .map(|pinned| pinned.path.clone())
            .collect();
        self.search_results.pinned_paths = self.search_home.pinned_paths.clone();
        if self.search_query.trim().is_empty() {
            self.search_results = self.search_home.clone();
        }
    }

    fn finish_search(&mut self, ctx: &Context, restore_previous_focus: bool) {
        self.search_active = false;
        self.search_panel_closing = true;
        self.search_panel_animation_started = Instant::now();
        self.search_focus_pending = false;
        self.search_focus_attempts = 0;
        self.search_selected = 0;
        self.search_text_transition_started = Instant::now();
        set_search_keyboard_focus(false, restore_previous_focus);
        ctx.request_repaint();
    }

    fn kill_matches(&self) -> Vec<(u32, String, bool)> {
        let Some(term) = kill_command_term(&self.search_query) else {
            return Vec::new();
        };
        let term = term.to_ascii_lowercase();
        let mut matches = self
            .system
            .processes()
            .iter()
            .filter_map(|(pid, process)| {
                let name = process.name().to_string_lossy().into_owned();
                name.to_ascii_lowercase().contains(&term).then_some((
                    pid.as_u32(),
                    name,
                    self.task_end_permissions
                        .get(&pid.as_u32())
                        .copied()
                        .unwrap_or(false),
                ))
            })
            .collect::<Vec<_>>();
        matches.sort_by_key(|(_, name, _)| name.to_ascii_lowercase());
        let key = self.search_query.trim().to_ascii_lowercase();
        if let Some(preferred) = self.search_command_selections.get(&key)
            && let Some(index) = matches
                .iter()
                .position(|(_, name, _)| name.eq_ignore_ascii_case(preferred))
        {
            let preferred = matches.remove(index);
            matches.insert(0, preferred);
        }
        matches.truncate(10);
        matches
    }

    fn remember_command_selection(&mut self, process_name: String) {
        for prefix in search_prefixes(&self.search_query) {
            self.search_command_selections
                .insert(prefix, process_name.clone());
        }
        let _ = self
            .search_requests
            .send(SearchWorkerRequest::RecordCommandSelection {
                query: self.search_query.clone(),
                process_name,
            });
    }

    fn active_launcher_command(&self) -> Option<LauncherCommand> {
        launcher_command(&self.search_query).or_else(|| {
            let query = self.search_query.trim();
            (!query.is_empty()
                && kill_command_term(query).is_none()
                && calculator_result(query).is_none()
                && self.search_results.pins.is_empty()
                && self.search_results.recents.is_empty()
                && self.search_results.apps.is_empty()
                && self.search_results.files.is_empty())
            .then(|| LauncherCommand {
                name: format!("Search the web for “{query}”"),
                detail: "No local matches · Opens in your default browser".to_owned(),
                action: LauncherCommandAction::WebSearch(query.to_owned()),
            })
        })
    }

    fn search_result_count(&self) -> usize {
        if let Some(term) = kill_command_term(&self.search_query) {
            let _ = term;
            self.kill_matches().len()
        } else {
            usize::from(self.active_launcher_command().is_some())
                + usize::from(calculator_result(&self.search_query).is_some())
                + self.search_results.pins.len()
                + self.search_results.recents.len()
                + self.search_results.apps.len()
                + self.search_results.files.len()
        }
    }

    fn execute_selected_search_result(&mut self, ctx: &Context) {
        if kill_command_term(&self.search_query).is_some() {
            if let Some((pid, name, can_end)) = self.kill_matches().get(self.search_selected).cloned() {
                self.remember_command_selection(name);
                self.finish_search(ctx, false);
                if can_end {
                if self
                    .task_end_permissions
                    .get(&pid)
                    .copied()
                    .unwrap_or(false)
                {
                    if let Some(process) = self.system.process(Pid::from_u32(pid)) {
                        let _ = process.kill();
                    }
                }
                }
            }
        } else {
            let command = self.active_launcher_command();
            if self.search_selected == 0
                && let Some(command) = command.clone()
            {
                self.execute_launcher_command(ctx, command.action);
                return;
            }
            let command_offset = usize::from(command.is_some());
            let calculation = calculator_result(&self.search_query);
            if self.search_selected == command_offset
                && let Some(result) = calculation.as_ref()
            {
                ctx.copy_text(result.clone());
                self.finish_search(ctx, false);
                return;
            }
            let selected = self
                .search_selected
                .saturating_sub(command_offset + usize::from(calculation.is_some()));
            let result = self
                .search_results
                .pins
                .iter()
                .chain(self.search_results.recents.iter())
                .chain(self.search_results.apps.iter())
                .chain(self.search_results.files.iter())
                .nth(selected)
                .cloned();
            if let Some(result) = result {
                let _ = self.search_requests.send(SearchWorkerRequest::RecordSelection {
                    query: self.search_query.clone(),
                    entry: result.clone(),
                });
                self.remember_search_recent(result.clone());
                self.finish_search(ctx, false);
                let path = result.path;
                let _ = thread::Builder::new()
                    .name("overbar-search-open".into())
                    .spawn(move || open_search_path(&path));
            }
        }
    }

    fn execute_launcher_command(&mut self, ctx: &Context, action: LauncherCommandAction) {
        self.finish_search(ctx, false);
        match action {
            LauncherCommandAction::Power(action) => {
                let _ = thread::Builder::new()
                    .name("overbar-power-command".into())
                    .spawn(move || {
                        thread::sleep(Duration::from_secs_f32(SEARCH_PANEL_CLOSE_SECONDS));
                        trigger_power_action(action);
                    });
            }
            LauncherCommandAction::OpenTarget(target) => {
                let _ = thread::Builder::new()
                    .name("overbar-command-open".into())
                    .spawn(move || open_search_path(Path::new(&target)));
            }
            LauncherCommandAction::Quit => {
                ctx.send_viewport_cmd(ViewportCommand::Close);
            }
            LauncherCommandAction::WebSearch(query) => {
                let target = format!(
                    "https://www.google.com/search?q={}",
                    percent_encode_query(&query)
                );
                let _ = thread::Builder::new()
                    .name("overbar-web-search".into())
                    .spawn(move || open_search_path(Path::new(&target)));
            }
        }
    }

    fn draw_search_panel(&mut self, ctx: &Context, monitor_width: f32) {
        // Windows' blur-behind backdrop is a compositor-level effect tied to the
        // HWND's rect; it renders regardless of our own content alpha. So the
        // panel must be parked off-screen while closed - opacity alone cannot
        // hide it, as proven by the frosted rectangle that stayed visible when
        // it was kept at its on-screen slot permanently.
        let panel_is_visible = self.search_active || self.search_panel_closing;
        let panel_builder = ViewportBuilder::default()
            .with_title("Overbar Search Panel")
            .with_inner_size([SEARCH_PANEL_WIDTH, SEARCH_PANEL_HEIGHT])
            .with_min_inner_size([SEARCH_PANEL_WIDTH, SEARCH_PANEL_HEIGHT])
            .with_max_inner_size([SEARCH_PANEL_WIDTH, SEARCH_PANEL_HEIGHT])
            .with_position([
                ((monitor_width - SEARCH_PANEL_WIDTH) / 2.0).max(0.0),
                if panel_is_visible {
                    BAR_HEIGHT + PANEL_GAP
                } else {
                    -SEARCH_PANEL_HEIGHT - 64.0
                },
            ])
            .with_transparent(true)
            .with_decorations(false)
            .with_resizable(false)
            .with_taskbar(false)
            .with_active(false)
            // Keep one stable transparent HWND and park it off-screen while closed.
            // Recreating it or toggling its blur policy makes DWM flash the bar.
            .with_visible(true)
            .with_window_level(WindowLevel::AlwaysOnTop);

        let kill_matches = kill_command_term(&self.search_query).map(|_| self.kill_matches());
        let command = kill_matches
            .is_none()
            .then(|| self.active_launcher_command())
            .flatten();
        let calculation = kill_matches
            .is_none()
            .then(|| calculator_result(&self.search_query))
            .flatten();
        let apps = self.search_results.apps.clone();
        let files = self.search_results.files.clone();
        let pins = self.search_results.pins.clone();
        let recents = self.search_results.recents.clone();
        let pinned_paths = self
            .search_results
            .pinned_paths
            .iter()
            .cloned()
            .collect::<HashSet<_>>();
        let mut icons_queued_this_frame = 0_usize;
        for entry in pins
            .iter()
            .chain(recents.iter())
            .chain(apps.iter())
            .chain(files.iter())
        {
            if !self.search_icons.contains_key(&entry.path)
                && !self.search_icon_pending.contains(&entry.path)
                && !self.search_icon_failed.contains(&entry.path)
            {
                if icons_queued_this_frame >= 8 {
                    continue;
                }
                icons_queued_this_frame += 1;
                if self.search_icon_requests.send(entry.path.clone()).is_ok() {
                    self.search_icon_pending.insert(entry.path.clone());
                }
            }
        }
        let icons = self.search_icons.clone();
        let pin_icon = self.pin_icon.clone();
        let pin_filled_icon = self.pin_filled_icon.clone();
        let accent_color = self.accent_color;
        let scroll_to_selected = self.search_scroll_to_selected;
        let mut action = None;
        let (key_up, key_down, key_enter, key_escape) = if self.search_active {
            ctx.input(|input| {
                (
                    input.key_pressed(eframe::egui::Key::ArrowUp),
                    input.key_pressed(eframe::egui::Key::ArrowDown),
                    input.key_pressed(eframe::egui::Key::Enter),
                    input.key_pressed(eframe::egui::Key::Escape),
                )
            })
        } else {
            (false, false, false, false)
        };
        let elapsed = self.search_panel_animation_started.elapsed().as_secs_f32();
        let open_progress = if self.search_active {
            ease_out_cubic((elapsed / SEARCH_PANEL_OPEN_SECONDS).clamp(0.0, 1.0))
        } else if self.search_panel_closing {
            1.0
        } else {
            0.0
        };
        let panel_opacity = if self.search_panel_closing {
            1.0 - (elapsed / SEARCH_PANEL_CLOSE_SECONDS).clamp(0.0, 1.0)
        } else if self.search_active {
            1.0
        } else {
            0.0
        };
        ctx.show_viewport_immediate(
            ViewportId::from_hash_of("overbar-search-panel"),
            panel_builder,
            |panel_ctx, _| {
                CentralPanel::default()
                    .frame(Frame::new().fill(Color32::TRANSPARENT).inner_margin(Margin::ZERO))
                    .show(panel_ctx, |ui| {
                        ui.set_opacity(panel_opacity);
                        ui.set_clip_rect(eframe::egui::Rect::from_min_max(
                            ui.max_rect().min,
                            eframe::egui::pos2(
                                ui.max_rect().max.x,
                                ui.max_rect().min.y + ui.max_rect().height() * open_progress,
                            ),
                        ));
                        Frame::new()
                            .fill(pill_background())
                            .inner_margin(Margin::same(12))
                            .show(ui, |ui| {
                                ui.set_width(SEARCH_PANEL_WIDTH - 24.0);
                                ui.set_height(SEARCH_PANEL_HEIGHT - 24.0);
                                ScrollArea::vertical().auto_shrink([false, false]).show(
                                    ui,
                                    |ui| {
                                        if let Some(matches) = &kill_matches {
                                            Self::draw_search_heading(ui, "COMMAND");
                                            if matches.is_empty() {
                                                ui.label(
                                                    RichText::new("No matching process")
                                                        .font(FontId::monospace(10.0))
                                                        .color(TEXT_MUTED),
                                                );
                                            }
                                            for (index, (pid, name, can_end)) in
                                                matches.iter().enumerate()
                                            {
                                                let suffix = if *can_end {
                                                    format!("End process · PID {pid}")
                                                } else {
                                                    format!("Protected · PID {pid}")
                                                };
                                                if Self::draw_search_result(
                                                    ui,
                                                    name,
                                                    &suffix,
                                                    *can_end,
                                                    index == self.search_selected,
                                                    None,
                                                    &pin_icon,
                                                    &pin_filled_icon,
                                                    accent_color,
                                                    scroll_to_selected,
                                                    None,
                                                )
                                                .primary
                                                {
                                                    action = Some(SearchAction::Kill {
                                                        pid: *pid,
                                                        name: name.clone(),
                                                    });
                                                }
                                            }
                                        } else {
                                            let mut index_offset = 0;
                                            if let Some(command) = &command {
                                                Self::draw_search_heading(ui, "COMMAND");
                                                if Self::draw_search_result(
                                                    ui,
                                                    &command.name,
                                                    &command.detail,
                                                    true,
                                                    self.search_selected == 0,
                                                    None,
                                                    &pin_icon,
                                                    &pin_filled_icon,
                                                    accent_color,
                                                    scroll_to_selected,
                                                    None,
                                                )
                                                .primary
                                                {
                                                    action = Some(SearchAction::RunCommand(
                                                        command.action.clone(),
                                                    ));
                                                }
                                                index_offset = 1;
                                                ui.add_space(7.0);
                                            }
                                            if let Some(result) = &calculation {
                                                Self::draw_search_heading(ui, "CALCULATOR");
                                                if Self::draw_search_result(
                                                    ui,
                                                    &format!("= {result}"),
                                                    "Press Enter to copy result",
                                                    true,
                                                    self.search_selected == index_offset,
                                                    None,
                                                    &pin_icon,
                                                    &pin_filled_icon,
                                                    accent_color,
                                                    scroll_to_selected,
                                                    None,
                                                )
                                                .primary
                                                {
                                                    action = Some(SearchAction::CopyCalculation(
                                                        result.clone(),
                                                    ));
                                                }
                                                index_offset += 1;
                                                ui.add_space(7.0);
                                            }
                                            if self.search_query.trim().is_empty() {
                                                if !pins.is_empty() {
                                                    Self::draw_search_heading(ui, "PINNED");
                                                    for (index, entry) in pins.iter().enumerate() {
                                                        let clicks = Self::draw_search_result(
                                                            ui,
                                                            &entry.name,
                                                            &entry.path.to_string_lossy(),
                                                            true,
                                                            index_offset + index == self.search_selected,
                                                            icons.get(&entry.path),
                                                            &pin_icon,
                                                            &pin_filled_icon,
                                                            accent_color,
                                                            scroll_to_selected,
                                                            Some(true),
                                                        );
                                                        if clicks.pin {
                                                            action = Some(SearchAction::TogglePin(entry.clone()));
                                                        } else if clicks.primary {
                                                            action = Some(SearchAction::Open(entry.clone()));
                                                        } else if clicks.secondary {
                                                            action = Some(SearchAction::Reveal(entry.path.clone()));
                                                        }
                                                    }
                                                    index_offset += pins.len();
                                                    ui.add_space(7.0);
                                                }
                                                Self::draw_search_heading(ui, "RECENT");
                                                for (recent_index, entry) in recents.iter().enumerate() {
                                                    let clicks = Self::draw_search_result(
                                                        ui,
                                                        &entry.name,
                                                        &entry.path.to_string_lossy(),
                                                        true,
                                                        index_offset + recent_index == self.search_selected,
                                                        icons.get(&entry.path),
                                                        &pin_icon,
                                                        &pin_filled_icon,
                                                        accent_color,
                                                        scroll_to_selected,
                                                        Some(pinned_paths.contains(&entry.path)),
                                                    );
                                                    if clicks.pin {
                                                        action = Some(SearchAction::TogglePin(entry.clone()));
                                                    } else if clicks.primary {
                                                        action = Some(SearchAction::Open(entry.clone()));
                                                    } else if clicks.secondary {
                                                        action = Some(SearchAction::Reveal(entry.path.clone()));
                                                    }
                                                }
                                                if recents.is_empty() {
                                                    Self::draw_empty_search_category(ui);
                                                }
                                            } else {
                                            if !pins.is_empty() {
                                                Self::draw_search_heading(ui, "PINNED");
                                                for (index, entry) in pins.iter().enumerate() {
                                                    let clicks = Self::draw_search_result(
                                                        ui,
                                                        &entry.name,
                                                        &entry.path.to_string_lossy(),
                                                        true,
                                                        index_offset + index == self.search_selected,
                                                        icons.get(&entry.path),
                                                        &pin_icon,
                                                        &pin_filled_icon,
                                                        accent_color,
                                                        scroll_to_selected,
                                                        Some(true),
                                                    );
                                                    if clicks.pin {
                                                        action = Some(SearchAction::TogglePin(entry.clone()));
                                                    } else if clicks.primary {
                                                        action = Some(SearchAction::Open(entry.clone()));
                                                    } else if clicks.secondary {
                                                        action = Some(SearchAction::Reveal(entry.path.clone()));
                                                    }
                                                }
                                                index_offset += pins.len();
                                                ui.add_space(7.0);
                                            }
                                            Self::draw_search_heading(ui, "APPS");
                                            for (app_index, entry) in apps.iter().enumerate() {
                                                let clicks = Self::draw_search_result(
                                                    ui,
                                                    &entry.name,
                                                    &entry.path.to_string_lossy(),
                                                    true,
                                                    index_offset + app_index == self.search_selected,
                                                    icons.get(&entry.path),
                                                    &pin_icon,
                                                    &pin_filled_icon,
                                                    accent_color,
                                                    scroll_to_selected,
                                                    Some(pinned_paths.contains(&entry.path)),
                                                );
                                                if clicks.pin {
                                                    action = Some(SearchAction::TogglePin(entry.clone()));
                                                } else if clicks.primary {
                                                    action = Some(SearchAction::Open(entry.clone()));
                                                } else if clicks.secondary {
                                                    action = Some(SearchAction::Reveal(
                                                        entry.path.clone(),
                                                    ));
                                                }
                                            }
                                            if apps.is_empty() {
                                                Self::draw_empty_search_category(ui);
                                            }
                                            ui.add_space(7.0);
                                            Self::draw_search_heading(ui, "FILES");
                                            for (file_index, entry) in files.iter().enumerate() {
                                                    let index = index_offset + apps.len() + file_index;
                                                    let clicks = Self::draw_search_result(
                                                        ui,
                                                        &entry.name,
                                                        &entry.path.to_string_lossy(),
                                                        true,
                                                        index == self.search_selected,
                                                        icons.get(&entry.path),
                                                        &pin_icon,
                                                        &pin_filled_icon,
                                                        accent_color,
                                                        scroll_to_selected,
                                                        Some(pinned_paths.contains(&entry.path)),
                                                    );
                                                    if clicks.pin {
                                                        action = Some(SearchAction::TogglePin(entry.clone()));
                                                    } else if clicks.primary {
                                                        action = Some(SearchAction::Open(entry.clone()));
                                                    } else if clicks.secondary {
                                                        action = Some(SearchAction::Reveal(
                                                            entry.path.clone(),
                                                        ));
                                                    }
                                                }
                                            if files.is_empty() {
                                                Self::draw_empty_search_category(ui);
                                            }
                                            }
                                        }
                                    },
                                );
                            });
                    });
            },
        );
        configure_windows_search_overlay();
        self.search_scroll_to_selected = false;

        let result_count = self.search_result_count();
        if key_down && result_count > 0 {
            self.search_selected = (self.search_selected + 1) % result_count;
            self.search_scroll_to_selected = true;
            ctx.request_repaint();
        }
        if key_up && result_count > 0 {
            self.search_selected = (self.search_selected + result_count - 1) % result_count;
            self.search_scroll_to_selected = true;
            ctx.request_repaint();
        }
        if key_escape {
            self.deactivate_search(ctx);
            return;
        }
        if key_enter {
            self.execute_selected_search_result(ctx);
            return;
        }

        match action {
            Some(SearchAction::Open(entry)) => {
                let _ = self.search_requests.send(SearchWorkerRequest::RecordSelection {
                    query: self.search_query.clone(),
                    entry: entry.clone(),
                });
                self.remember_search_recent(entry.clone());
                self.finish_search(ctx, false);
                let path = entry.path;
                let _ = thread::Builder::new()
                    .name("overbar-search-open".into())
                    .spawn(move || open_search_path(&path));
            }
            Some(SearchAction::Reveal(path)) => {
                reveal_search_path(&path);
                self.finish_search(ctx, false);
            }
            Some(SearchAction::TogglePin(entry)) => {
                self.toggle_search_pin_local(entry.clone());
                let _ = self
                    .search_requests
                    .send(SearchWorkerRequest::TogglePin(entry));
            }
            Some(SearchAction::Kill { pid, name }) => {
                self.remember_command_selection(name);
                self.finish_search(ctx, false);
                if self
                    .task_end_permissions
                    .get(&pid)
                    .copied()
                    .unwrap_or(false)
                {
                    if let Some(process) = self.system.process(Pid::from_u32(pid)) {
                        let _ = process.kill();
                    }
                }
            }
            Some(SearchAction::CopyCalculation(result)) => {
                ctx.copy_text(result);
                self.finish_search(ctx, false);
            }
            Some(SearchAction::RunCommand(action)) => {
                self.execute_launcher_command(ctx, action);
            }
            None => {}
        }
    }

    fn draw_search_heading(ui: &mut eframe::egui::Ui, text: &str) {
        ui.label(
            RichText::new(text)
                .font(FontId::monospace(9.0))
                .strong()
                .color(STAT_LABEL),
        );
        ui.add_space(2.0);
    }

    fn draw_empty_search_category(ui: &mut eframe::egui::Ui) {
        ui.label(
            RichText::new("No matches yet")
                .font(FontId::monospace(9.0))
                .color(STAT_LABEL),
        );
    }

    fn draw_search_result(
        ui: &mut eframe::egui::Ui,
        name: &str,
        detail: &str,
        enabled: bool,
        selected: bool,
        icon: Option<&TextureHandle>,
        pin_icon: &TextureHandle,
        pin_filled_icon: &TextureHandle,
        accent_color: Color32,
        scroll_to_selected: bool,
        pinned: Option<bool>,
    ) -> SearchResultClicks {
        let (rect, response) = ui.allocate_exact_size(
            Vec2::new(ui.available_width(), 35.0),
            if enabled { Sense::click() } else { Sense::hover() },
        );
        let response = if enabled {
            response.on_hover_cursor(CursorIcon::PointingHand)
        } else {
            response
        };
        if selected && scroll_to_selected {
            response.scroll_to_me(Some(Align::Center));
        }
        if selected {
            ui.painter().rect_filled(
                rect,
                CornerRadius::same(5),
                Color32::from_rgba_unmultiplied(0, 0, 0, 42),
            );
        } else if response.hovered() && enabled {
            ui.painter().rect_filled(
                rect,
                CornerRadius::same(5),
                Color32::from_rgba_unmultiplied(0, 0, 0, 30),
            );
        }
        if let Some(icon) = icon {
            let icon_rect = eframe::egui::Rect::from_center_size(
                eframe::egui::pos2(rect.left() + 18.0, rect.center().y),
                Vec2::splat(24.0),
            );
            ui.put(
                icon_rect,
                eframe::egui::Image::new((icon.id(), Vec2::splat(24.0))),
            );
        }
        let pin_response = pinned.map(|is_pinned| {
            let pin_rect = eframe::egui::Rect::from_center_size(
                eframe::egui::pos2(rect.right() - 21.0, rect.center().y),
                Vec2::splat(24.0),
            );
            let response = ui
                .interact(pin_rect, ui.id().with(("search-pin", name, detail)), Sense::click())
                .on_hover_cursor(CursorIcon::PointingHand);
            let color = if response.hovered() || is_pinned {
                accent_color
            } else {
                STAT_LABEL
            };
            ui.painter().image(
                if is_pinned {
                    pin_filled_icon.id()
                } else {
                    pin_icon.id()
                },
                eframe::egui::Rect::from_center_size(pin_rect.center(), Vec2::splat(18.0)),
                eframe::egui::Rect::from_min_max(
                    eframe::egui::Pos2::ZERO,
                    eframe::egui::pos2(1.0, 1.0),
                ),
                color,
            );
            response
        });
        let text_left = if icon.is_some() { 38.0 } else { 8.0 };
        let mut clip_rect = rect.shrink2(Vec2::new(8.0, 0.0));
        if pinned.is_some() {
            clip_rect.max.x -= 25.0;
        }
        let painter = ui.painter().with_clip_rect(clip_rect);
        painter.text(
            rect.left_center() + Vec2::new(text_left, -6.0),
            eframe::egui::Align2::LEFT_CENTER,
            name,
            FontId::monospace(10.5),
            if enabled { TEXT_PRIMARY } else { STAT_LABEL },
        );
        painter.text(
            rect.left_center() + Vec2::new(text_left, 7.0),
            eframe::egui::Align2::LEFT_CENTER,
            detail,
            FontId::monospace(8.5),
            STAT_LABEL,
        );
        SearchResultClicks {
            primary: enabled
                && response.clicked()
                && !pin_response.as_ref().is_some_and(|response| response.clicked()),
            secondary: enabled && response.secondary_clicked(),
            pin: pin_response.is_some_and(|response| response.clicked()),
        }
    }

    fn toggle_tiling_direction(&mut self, current_angle: f32) {
        let _ = self
            .window_manager_commands
            .send(WindowManagerCommand::ToggleTilingDirection);

        // Respond immediately; the native manager confirms the state on its event stream.
        self.direction = match self.direction {
            TilingDirection::Horizontal => TilingDirection::Vertical,
            TilingDirection::Vertical => TilingDirection::Horizontal,
        };
        self.direction_angle_from = current_angle;
        self.direction_angle_to = match self.direction {
            TilingDirection::Horizontal => 0.0,
            TilingDirection::Vertical => std::f32::consts::FRAC_PI_2,
        };
        self.direction_angle_started = Instant::now();
    }

    fn draw_left(&mut self, ui: &mut eframe::egui::Ui) {
        let now = Instant::now();
        let edge_padding = physical_pixels(ui, 12.0);
        ui.add_space(edge_padding);

        let (icon_rect, icon_response) =
            ui.allocate_exact_size(Vec2::splat(15.0), Sense::click());
        let icon_response = icon_response.on_hover_cursor(CursorIcon::PointingHand);
        self.apps_icon_rect = icon_rect;
        if icon_response.clicked() {
            self.apps_icon_clicked_at = now;
            // Settings is a child view of the app manager. Do not allow the
            // underlying launcher button to open a second panel through it.
            if !self.wm_settings_open {
                if !self.apps_panel_open {
                    self.apps_panel_opened_at = Instant::now();
                }
                self.apps_panel_open = !self.apps_panel_open;
                self.panel_open = false;
            }
        }
        let hover_fill = ui.ctx().animate_bool_with_time(
            ui.id().with("apps-icon-hover"),
            icon_response.hovered(),
            0.12,
        );
        let open_fill = ui.ctx().animate_bool_with_time(
            ui.id().with("apps-icon-open"),
            self.apps_panel_open,
            0.2,
        );
        let fill_progress = open_fill.max(hover_fill * 0.12);
        let click_progress = (now.duration_since(self.apps_icon_clicked_at).as_secs_f32() / 0.22)
            .clamp(0.0, 1.0);
        if click_progress < 1.0 {
            ui.ctx().request_repaint();
        }
        let click_scale = 1.0 - 0.16 * (std::f32::consts::PI * click_progress).sin();
        let icon_scale = (1.0 + hover_fill * 0.07) * click_scale;
        let painter = ui.painter();
        for row in 0..2 {
            for column in 0..2 {
                let offset = Vec2::new(
                    (column as f32 - 0.5) * 7.0 * icon_scale,
                    (row as f32 - 0.5) * 7.0 * icon_scale,
                );
                let cell = eframe::egui::Rect::from_center_size(
                    icon_rect.center() + offset,
                    Vec2::splat(4.0 * icon_scale),
                );
                if fill_progress > 0.01 {
                    let fill = Color32::from_rgba_unmultiplied(
                        255,
                        255,
                        255,
                        (255.0 * fill_progress) as u8,
                    );
                    painter.rect_filled(
                        cell.shrink((1.0 - fill_progress) * 1.5),
                        CornerRadius::same(1),
                        fill,
                    );
                }
                painter.rect_stroke(
                    cell,
                    CornerRadius::same(1),
                    Stroke::new(1.3_f32, TEXT_PRIMARY),
                    eframe::egui::StrokeKind::Middle,
                );
            }
        }
        if let Some(notice) = self.update_notice.filter(|_| !self.update_in_progress) {
            painter.circle_filled(
                eframe::egui::pos2(icon_rect.right() - 0.5, icon_rect.top() + 0.5),
                2.5,
                match notice {
                    UpdateNotice::Available => UPDATE_NOTICE,
                    UpdateNotice::Failed => USAGE_CRITICAL,
                    UpdateNotice::Complete => UPDATE_COMPLETE,
                },
            );
        }

        ui.add_space(9.0);
        if self.resize_mode_active {
            let (resize_rect, _) =
                ui.allocate_exact_size(Vec2::new(32.0, 15.0), Sense::hover());
            ui.painter().text(
                resize_rect.center(),
                eframe::egui::Align2::CENTER_CENTER,
                "resize",
                FontId::monospace(9.0),
                self.accent_color,
            );
        } else {
            let turn_progress = (now
                .duration_since(self.direction_angle_started)
                .as_secs_f32()
                / DIRECTION_TURN_SECONDS)
                .clamp(0.0, 1.0);
            let direction_angle = self.direction_angle_from
                + (self.direction_angle_to - self.direction_angle_from)
                    * smootherstep(turn_progress);
            if turn_progress < 1.0 {
                ui.ctx().request_repaint();
            }
            let (arrow_rect, arrow_response) =
                ui.allocate_exact_size(Vec2::new(10.0, 15.0), Sense::click());
            let arrow_response = arrow_response.on_hover_cursor(CursorIcon::PointingHand);
            let rotate = |point: Vec2| {
                Vec2::new(
                    point.x * direction_angle.cos() - point.y * direction_angle.sin(),
                    point.x * direction_angle.sin() + point.y * direction_angle.cos(),
                )
            };
            let arrow_center = arrow_rect.center();
            let arrow_stroke = Stroke::new(1.45_f32, TEXT_PRIMARY);
            ui.painter().line_segment(
                [
                    arrow_center + rotate(Vec2::new(-2.0, -3.0)),
                    arrow_center + rotate(Vec2::new(1.5, 0.0)),
                ],
                arrow_stroke,
            );
            ui.painter().line_segment(
                [
                    arrow_center + rotate(Vec2::new(1.5, 0.0)),
                    arrow_center + rotate(Vec2::new(-2.0, 3.0)),
                ],
                arrow_stroke,
            );
            if arrow_response.clicked() {
                self.toggle_tiling_direction(direction_angle);
            }
            ui.add_space(7.0);
            let (mode_rect, mode_response) =
                ui.allocate_exact_size(Vec2::splat(15.0), Sense::click());
            let mode_response = mode_response.on_hover_cursor(CursorIcon::PointingHand);
            let mode_icon = if self.focused_floating {
                &self.floating_icon
            } else {
                &self.tiled_icon
            };
            ui.painter().image(
                mode_icon.id(),
                eframe::egui::Rect::from_center_size(mode_rect.center(), Vec2::splat(14.0)),
                eframe::egui::Rect::from_min_max(
                    eframe::egui::Pos2::ZERO,
                    eframe::egui::pos2(1.0, 1.0),
                ),
                TEXT_PRIMARY,
            );
            if mode_response.clicked() {
                let _ = self
                    .window_manager_commands
                    .send(WindowManagerCommand::ToggleFloating);
                self.focused_floating = !self.focused_floating;
            }
        }
        ui.add_space(10.0);

        self.workspace_births.retain(|name, _| {
            self.workspaces
                .items
                .iter()
                .any(|workspace| workspace.name == *name)
        });
        let slots_grew = self.workspaces.items.len() > self.workspace_slot_count;
        let existing_slot = now - Duration::from_secs(1);
        for workspace in &self.workspaces.items {
            self.workspace_births
                .entry(workspace.name.clone())
                .or_insert(if slots_grew { now } else { existing_slot });
        }
        self.workspace_slot_count = self.workspaces.items.len();

        let indicator_target = self.workspaces.active as f32;
        if indicator_target != self.indicator_to {
            let elapsed = now.duration_since(self.indicator_started).as_secs_f32()
                / WORKSPACE_SLIDE_SECONDS;
            let progress = smootherstep(elapsed.clamp(0.0, 1.0));
            let current = self.indicator_from
                + (self.indicator_to - self.indicator_from) * progress;
            self.indicator_from = current;
            self.indicator_to = indicator_target;
            self.indicator_started = now;
        }
        let slide_progress = (now.duration_since(self.indicator_started).as_secs_f32()
            / WORKSPACE_SLIDE_SECONDS)
            .clamp(0.0, 1.0);
        let animated_workspace = self.indicator_from
            + (self.indicator_to - self.indicator_from) * smootherstep(slide_progress);
        if slide_progress < 1.0 {
            ui.ctx().request_repaint();
        }

        let mut clicked_workspace = None;
        Frame::new()
            .fill(pill_background())
            .corner_radius(CornerRadius::same(18))
            .inner_margin(Margin::symmetric(4, 3))
            .show(ui, |ui| {
                ui.set_height(PILL_CONTENT_HEIGHT);
                ui.spacing_mut().item_spacing.x = 0.0;
                // `small` below opts out of egui's global minimum interaction
                // height; otherwise it silently overrides our 19-point pill row.
                ui.spacing_mut().button_padding.y = 0.0;

                let workspace_origin = ui.cursor().min;
                let indicator_rect = eframe::egui::Rect::from_min_size(
                    workspace_origin + Vec2::new(animated_workspace * WORKSPACE_WIDTH, 0.0),
                    Vec2::new(WORKSPACE_WIDTH, PILL_CONTENT_HEIGHT),
                );
                let active_hover_rect = eframe::egui::Rect::from_min_size(
                    workspace_origin
                        + Vec2::new(self.workspaces.active as f32 * WORKSPACE_WIDTH, 0.0),
                    Vec2::new(WORKSPACE_WIDTH, PILL_CONTENT_HEIGHT),
                );
                let active_hovered = ui.input(|input| {
                    input
                        .pointer
                        .hover_pos()
                        .is_some_and(|position| active_hover_rect.contains(position))
                });
                let active_hover = ui.ctx().animate_bool_with_time(
                    ui.id().with("active-workspace-hover"),
                    active_hovered,
                    0.12,
                );
                ui.painter().circle_filled(
                    indicator_rect.center(),
                    indicator_rect.width() / 2.0 + active_hover * 1.35,
                    self.accent_color,
                );

                for (index, workspace) in self.workspaces.items.iter().enumerate() {
                        let active = index == self.workspaces.active || workspace.active;
                        let birth = self.workspace_births[&workspace.name];
                        let grow_progress = (now.duration_since(birth).as_secs_f32()
                            / WORKSPACE_GROW_SECONDS)
                            .clamp(0.0, 1.0);
                        let growth = ease_out_cubic(grow_progress);
                        if grow_progress < 1.0 {
                            ui.ctx().request_repaint();
                        }

                        let (rect, response) = ui.allocate_exact_size(
                            Vec2::new(WORKSPACE_WIDTH * growth, PILL_CONTENT_HEIGHT),
                            Sense::click(),
                        );
                        let response = response.on_hover_cursor(CursorIcon::PointingHand);
                        if growth > 0.05 {
                            let inactive_hover = ui.ctx().animate_bool_with_time(
                                ui.id().with(("workspace-hover", &workspace.name)),
                                response.hovered() && !active,
                                0.12,
                            );
                            if inactive_hover > 0.0 {
                                ui.painter().circle_filled(
                                    rect.center(),
                                    8.5 + inactive_hover * 2.0,
                                    Color32::from_rgba_unmultiplied(
                                        205,
                                        211,
                                        216,
                                        (42.0 * inactive_hover) as u8,
                                    ),
                                );
                            }
                            let active_fade = ui.ctx().animate_bool_with_time(
                                ui.id().with(("workspace-number", &workspace.name)),
                                active,
                                0.16,
                            );
                            let center = rect.center();
                            ui.painter().text(
                                center,
                                eframe::egui::Align2::CENTER_CENTER,
                                &workspace.name,
                                FontId::monospace(BAR_FONT_SIZE),
                                TEXT_MUTED.gamma_multiply(growth),
                            );
                            ui.painter().text(
                                center,
                                eframe::egui::Align2::CENTER_CENTER,
                                &workspace.name,
                                FontId::monospace(BAR_FONT_SIZE),
                                Color32::WHITE.gamma_multiply(active_fade * growth),
                            );
                        }

                        if response.clicked() {
                            clicked_workspace = Some((index, workspace.name.clone()));
                        }
                }
            });

        if let Some((active_index, name)) = clicked_workspace {
            // Update in this same frame; the event subscription will confirm the state.
            self.workspaces.active = active_index;
            for (index, workspace) in self.workspaces.items.iter_mut().enumerate() {
                workspace.active = index == active_index;
            }
            self.focus_workspace(&name);
        }

        if self.media.is_some() {
            ui.add_space(10.0);
            self.draw_media_pill(ui);
        }
    }

    fn draw_media_pill(&mut self, ui: &mut eframe::egui::Ui) {
        let Some(media) = self.media.clone() else {
            return;
        };
        let label = if media.artist.trim().is_empty() {
            media.title.clone()
        } else {
            format!("{} - {}", media.artist.trim(), media.title.trim())
        };
        let font = FontId::monospace(BAR_FONT_SIZE);
        let text_width = ui
            .painter()
            .layout_no_wrap(label.clone(), font.clone(), TEXT_PRIMARY)
            .size()
            .x;
        if self.media_scroll_label != label {
            self.media_scroll_label = label.clone();
            self.media_scroll_started = Instant::now();
        }
        let configured_text_width = self.wm_config.media_name_width.clamp(80.0, 500.0);
        let width = (40.0 + text_width.min(configured_text_width)).max(112.0);
        let height = PILL_CONTENT_HEIGHT + 6.0;
        let (rect, response) = ui.allocate_exact_size(Vec2::new(width, height), Sense::click());
        let response = response.on_hover_cursor(CursorIcon::PointingHand);
        let hover = ui.ctx().animate_bool_with_time(
            ui.id().with("media-pill-hover"),
            response.hovered(),
            0.14,
        );
        ui.painter().rect_filled(
            rect,
            CornerRadius::same(18),
            Color32::from_rgba_unmultiplied(9, 11, 15, (92.0 + 26.0 * hover) as u8),
        );

        let icon_rect = eframe::egui::Rect::from_center_size(
            eframe::egui::pos2(rect.left() + 17.0, rect.center().y - 0.5),
            Vec2::splat(15.0),
        );
        let icon_mix = self.current_media_icon_mix();
        let play_rect = eframe::egui::Rect::from_center_size(
            icon_rect.center(),
            Vec2::splat(15.0 - icon_mix * 1.5),
        );
        let pause_rect = eframe::egui::Rect::from_center_size(
            icon_rect.center(),
            Vec2::splat(13.5 + icon_mix * 1.5),
        );
        ui.painter().image(
            self.play_icon.id(),
            play_rect,
            eframe::egui::Rect::from_min_max(
                eframe::egui::Pos2::ZERO,
                eframe::egui::pos2(1.0, 1.0),
            ),
            TEXT_MUTED.gamma_multiply(1.0 - icon_mix),
        );
        ui.painter().image(
            self.pause_icon.id(),
            pause_rect,
            eframe::egui::Rect::from_min_max(
                eframe::egui::Pos2::ZERO,
                eframe::egui::pos2(1.0, 1.0),
            ),
            TEXT_MUTED.gamma_multiply(icon_mix),
        );

        let text_rect = eframe::egui::Rect::from_min_max(
            eframe::egui::pos2(rect.left() + 31.0, rect.top()),
            eframe::egui::pos2(rect.right() - 9.0, rect.bottom() - 2.0),
        );
        let text_painter = ui.painter().with_clip_rect(text_rect);
        if text_width > text_rect.width() + 0.5 {
            const MARQUEE_DELAY_SECONDS: f32 = 0.85;
            const MARQUEE_SPEED: f32 = 28.0;
            const MARQUEE_GAP: f32 = 36.0;
            let elapsed = self.media_scroll_started.elapsed().as_secs_f32();
            let offset = if elapsed <= MARQUEE_DELAY_SECONDS {
                0.0
            } else {
                ((elapsed - MARQUEE_DELAY_SECONDS) * MARQUEE_SPEED)
                    % (text_width + MARQUEE_GAP)
            };
            for x in [
                text_rect.left() - offset,
                text_rect.left() - offset + text_width + MARQUEE_GAP,
            ] {
                text_painter.text(
                    eframe::egui::pos2(x, rect.center().y - 0.5),
                    eframe::egui::Align2::LEFT_CENTER,
                    &label,
                    font.clone(),
                    TEXT_PRIMARY,
                );
            }
            ui.ctx().request_repaint_after(Duration::from_millis(16));
        } else {
            text_painter.text(
                eframe::egui::pos2(text_rect.left(), rect.center().y - 0.5),
                eframe::egui::Align2::LEFT_CENTER,
                label,
                font,
                TEXT_PRIMARY,
            );
        }

        let elapsed = if media.playing {
            self.media_updated_at.elapsed().as_secs_f64()
        } else {
            0.0
        };
        let progress = if media.duration_seconds > 0.0 {
            ((media.position_seconds + elapsed) / media.duration_seconds).clamp(0.0, 1.0)
        } else {
            0.0
        };
        let track = eframe::egui::Rect::from_min_max(
            eframe::egui::pos2(rect.left() + 12.0, rect.bottom() - 1.5),
            eframe::egui::pos2(rect.right() - 12.0, rect.bottom() - 0.5),
        );
        ui.painter().rect_filled(
            track,
            CornerRadius::same(1),
            Color32::from_rgba_unmultiplied(0, 0, 0, 55),
        );
        if progress > 0.0 {
            let progress_rect = eframe::egui::Rect::from_min_max(
                track.min,
                eframe::egui::pos2(track.left() + track.width() * progress as f32, track.bottom()),
            );
            ui.painter().rect_filled(
                progress_rect,
                CornerRadius::same(1),
                self.accent_color,
            );
        }

        if media.playing || (self.media_icon_mix_to - icon_mix).abs() > 0.001 {
            ui.ctx().request_repaint_after(Duration::from_millis(16));
        }
        if response.clicked() {
            let _ = self.media_commands.send(MediaCommand::TogglePlayPause);
            self.animate_media_icon_to(!media.playing);
            if let Some(current) = self.media.as_mut() {
                if current.playing {
                    current.position_seconds = (current.position_seconds
                        + self.media_updated_at.elapsed().as_secs_f64())
                        .min(current.duration_seconds.max(0.0));
                }
                current.playing = !current.playing;
            }
            self.media_updated_at = Instant::now();
            ui.ctx().request_repaint();
        }
    }

    fn current_media_icon_mix(&self) -> f32 {
        let progress = (self.media_icon_transition_started.elapsed().as_secs_f32() / 0.18)
            .clamp(0.0, 1.0);
        let eased = progress * progress * (3.0 - 2.0 * progress);
        self.media_icon_mix_from
            + (self.media_icon_mix_to - self.media_icon_mix_from) * eased
    }

    fn animate_media_icon_to(&mut self, playing: bool) {
        let target = if playing { 1.0 } else { 0.0 };
        let current = self.current_media_icon_mix();
        if (target - self.media_icon_mix_to).abs() > f32::EPSILON
            || (current - target).abs() > 0.001
        {
            self.media_icon_mix_from = current;
            self.media_icon_mix_to = target;
            self.media_icon_transition_started = Instant::now();
        }
    }

    fn draw_right(&mut self, ui: &mut eframe::egui::Ui) {
        // Every horizontal gap in this row is explicit; avoid egui adding its
        // default item spacing on top of the pixel measurements below.
        ui.spacing_mut().item_spacing.x = 0.0;
        let edge_padding = physical_pixels(ui, 12.0);
        let ten_pixel_gap = physical_pixels(ui, 10.0);
        ui.add_space(edge_padding);
        let power_color = Color32::from_rgb(230, 91, 104);
        let power_font = FontId::new(12.0, FontFamily::Name("power-symbols".into()));
        let power_galley = ui
            .painter()
            .layout_no_wrap("⏻".to_owned(), power_font.clone(), power_color);
        let (power_rect, _) = ui.allocate_exact_size(
            Vec2::new(power_galley.size().x.max(15.0), PILL_CONTENT_HEIGHT),
            Sense::hover(),
        );
        self.power_button_rect = power_rect;
        let power_response = ui
            .interact(power_rect, ui.id().with("power-button"), Sense::click())
            .on_hover_cursor(CursorIcon::PointingHand);
        let hover_tint = if power_response.hovered() {
            Color32::from_rgba_unmultiplied(
                power_color.r(),
                power_color.g(),
                power_color.b(),
                180,
            )
        } else {
            power_color
        };
        ui.painter().galley(
            eframe::egui::pos2(
                power_rect.center().x - power_galley.size().x / 2.0,
                power_rect.center().y - power_galley.size().y / 2.0,
            ),
            power_galley,
            hover_tint,
        );
        if power_response.clicked() {
            if self.scheduled_power_action.is_some() {
                // Keep the cancellation UI available until Windows accepts an
                // abort request or completes the scheduled power action.
            } else if self.power_panel_open {
                self.begin_power_panel_close();
            } else {
                self.power_panel_opened_at = Instant::now();
                self.power_panel_open = true;
                self.power_panel_closing = false;
                self.pending_power_action = None;
            }
            self.panel_open = false;
            self.apps_panel_open = false;
        }
        ui.add_space(edge_padding);
        let status = self.status_line();
        let status_font = FontId::monospace(BAR_FONT_SIZE);
        let status_size = ui.painter()
            .layout_no_wrap(status.clone(), status_font.clone(), TEXT_PRIMARY)
            .size();
        let (status_rect, _) = ui.allocate_exact_size(status_size, Sense::hover());
        let status_center = status_rect.center() + Vec2::new(0.0, 1.0);
        for offset in [-0.2_f32, 0.2] {
            ui.painter().text(
                status_center + Vec2::new(offset, 0.0),
                eframe::egui::Align2::CENTER_CENTER,
                &status,
                status_font.clone(),
                TEXT_PRIMARY,
            );
        }
        ui.add_space(ten_pixel_gap);
        self.draw_volume(ui);
        ui.add_space(ten_pixel_gap);

        let stats_frame = Frame::new()
            .fill(pill_background())
            .corner_radius(CornerRadius::same(18))
            .inner_margin(Margin::symmetric(10, 3))
            .show(ui, |ui| {
                // Match the workspace buttons' content height so both pills have
                // identical vertical padding and total height.
                ui.set_height(PILL_CONTENT_HEIGHT);
                ui.spacing_mut().item_spacing.x = STAT_GROUP_GAP;
                // This closure is right-to-left, so add items in reverse visual order.
                Self::draw_stat(
                    ui,
                    "BAT",
                    self.battery_percent
                        .map_or_else(|| "--%".to_owned(), |percent| format!("{percent}%")),
                    TEXT_PRIMARY,
                );
                if let Some(temp) = self.cpu_temperature {
                    Self::draw_stat(
                        ui,
                        "TEMP",
                        format!("{temp:.0}°C"),
                        usage_color(temp),
                    );
                }
                Self::draw_stat(
                    ui,
                    "RAM",
                    format!("{:.0}%", self.ram_percent),
                    usage_color(self.ram_percent),
                );
                Self::draw_stat(
                    ui,
                    "CPU",
                    format!("{:.0}%", self.cpu_percent),
                    usage_color(self.cpu_percent),
                );
            });
        let stats_click = ui
            .interact(
                stats_frame.response.rect,
                ui.id().with("stats-pill"),
                Sense::click(),
            )
            .on_hover_cursor(CursorIcon::PointingHand);
        self.stats_pill_rect = stats_frame.response.rect;
        if stats_click.clicked() {
            if !self.panel_open {
                self.panel_opened_at = Instant::now();
            }
            self.panel_open = !self.panel_open;
            self.apps_panel_open = false;
        }
    }

    fn draw_volume(&mut self, ui: &mut eframe::egui::Ui) {
        let expansion = ui.ctx().animate_bool_with_time(
            ui.id().with("volume-expanded"),
            self.volume_expanded,
            0.18,
        );
        let width = VOLUME_COLLAPSED_WIDTH
            + (VOLUME_EXPANDED_WIDTH - VOLUME_COLLAPSED_WIDTH) * expansion;

        let frame = Frame::new()
            .fill(pill_background())
            .corner_radius(CornerRadius::same(18))
            .inner_margin(Margin::symmetric(4, 3))
            .show(ui, |ui| {
                let content_width = (width - 8.0).max(1.0);
                ui.set_width(content_width);
                ui.set_height(PILL_CONTENT_HEIGHT);
                let (rect, response) = ui.allocate_exact_size(
                    Vec2::new(content_width, PILL_CONTENT_HEIGHT),
                    Sense::click_and_drag(),
                );
                let response = response.on_hover_cursor(CursorIcon::PointingHand);
                let icon_center = eframe::egui::pos2(
                    rect.left() + PILL_CONTENT_HEIGHT / 2.0,
                    rect.center().y,
                );
                let icon_color = TEXT_MUTED;
                let speaker = vec![
                    icon_center + Vec2::new(-6.0, -2.0),
                    icon_center + Vec2::new(-3.5, -2.0),
                    icon_center + Vec2::new(-0.5, -5.0),
                    icon_center + Vec2::new(-0.5, 5.0),
                    icon_center + Vec2::new(-3.5, 2.0),
                    icon_center + Vec2::new(-6.0, 2.0),
                ];
                ui.painter().add(eframe::egui::Shape::convex_polygon(
                    speaker,
                    icon_color,
                    Stroke::NONE,
                ));
                if !self.volume_muted && self.volume > 0.001 {
                    ui.painter().add(eframe::egui::Shape::line(
                        vec![
                            icon_center + Vec2::new(1.0, -3.0),
                            icon_center + Vec2::new(2.8, -1.5),
                            icon_center + Vec2::new(2.8, 1.5),
                            icon_center + Vec2::new(1.0, 3.0),
                        ],
                        Stroke::new(1.3_f32, icon_color),
                    ));
                    if self.volume >= 0.67 {
                        ui.painter().add(eframe::egui::Shape::line(
                            vec![
                                icon_center + Vec2::new(4.0, -4.8),
                                icon_center + Vec2::new(6.3, -2.5),
                                icon_center + Vec2::new(6.3, 2.5),
                                icon_center + Vec2::new(4.0, 4.8),
                            ],
                            Stroke::new(1.3_f32, icon_color),
                        ));
                    }
                }

                let slider_start = rect.left() + 29.0;
                let slider_end = rect.right() - 7.0;
                if slider_end > slider_start {
                    let track = eframe::egui::Rect::from_min_max(
                        eframe::egui::pos2(slider_start, rect.center().y - 3.0),
                        eframe::egui::pos2(slider_end, rect.center().y + 3.0),
                    );
                    ui.painter().rect_filled(
                        track,
                        CornerRadius::same(4),
                        Color32::from_rgba_premultiplied(80, 94, 101, 125),
                    );
                    let shown_volume = if self.volume_muted { 0.0 } else { self.volume };
                    let fill = eframe::egui::Rect::from_min_max(
                        track.min,
                        eframe::egui::pos2(
                            track.left() + track.width() * shown_volume.clamp(0.0, 1.0),
                            track.bottom(),
                        ),
                    );
                    ui.painter()
                        .rect_filled(fill, CornerRadius::same(4), self.accent_color);
                }

                if let Some(pointer) = response.interact_pointer_pos() {
                    let using_slider = self.volume_expanded
                        && pointer.x >= slider_start - 4.0
                        && (response.dragged() || response.clicked());
                    if using_slider && slider_end > slider_start {
                        self.volume = ((pointer.x - slider_start) / (slider_end - slider_start))
                            .clamp(0.0, 1.0);
                        self.volume_muted = false;
                        let _ = self
                            .audio_commands
                            .send(AudioCommand::SetVolume(self.volume));
                    } else if response.clicked() {
                        self.volume_expanded = !self.volume_expanded;
                    }
                }
                response.hovered() || response.dragged()
            });

        let now = Instant::now();
        if frame.inner || frame.response.hovered() {
            self.volume_last_hovered = now;
        } else if self.volume_expanded {
            let elapsed = now.duration_since(self.volume_last_hovered);
            if elapsed >= Duration::from_secs(1) {
                self.volume_expanded = false;
            } else {
                ui.ctx()
                    .request_repaint_after(Duration::from_secs(1) - elapsed);
            }
        }
    }

    fn begin_power_panel_close(&mut self) {
        if self.power_panel_open {
            self.power_panel_open = false;
            self.power_panel_closing = true;
            self.power_panel_opened_at = Instant::now();
        }
    }

    fn draw_power_option(
        ui: &mut eframe::egui::Ui,
        rect: eframe::egui::Rect,
        id: eframe::egui::Id,
        icon: eframe::egui::TextureId,
        label: &str,
        hover_color: Color32,
        opacity: f32,
    ) -> bool {
        let response = ui
            .interact(rect, id, Sense::click())
            .on_hover_cursor(CursorIcon::PointingHand);
        let hover = ui
            .ctx()
            .animate_bool_with_time(id.with("hover"), response.hovered(), 0.18);
        let card_rect = eframe::egui::Rect::from_center_size(
            rect.center() - Vec2::new(0.0, 5.0 * hover),
            rect.size() * (1.0 + 0.035 * hover),
        );
        let background_alpha = ((18.0 + 48.0 * hover) * opacity).round() as u8;
        ui.painter().rect_filled(
            card_rect,
            CornerRadius::same(18),
            Color32::from_rgba_unmultiplied(9, 11, 15, background_alpha),
        );
        if hover > 0.0 {
            ui.painter().rect_stroke(
                card_rect,
                CornerRadius::same(18),
                Stroke::new(
                    1.0_f32,
                    hover_color.gamma_multiply(hover * opacity * 0.75),
                ),
                eframe::egui::StrokeKind::Middle,
            );
        }

        let blend = |from: u8, to: u8| {
            (from as f32 + (to as f32 - from as f32) * hover).round() as u8
        };
        let foreground = Color32::from_rgb(
            blend(TEXT_PRIMARY.r(), hover_color.r()),
            blend(TEXT_PRIMARY.g(), hover_color.g()),
            blend(TEXT_PRIMARY.b(), hover_color.b()),
        )
        .gamma_multiply(opacity);
        let icon_size = 66.0 + 8.0 * hover;
        let icon_rect = eframe::egui::Rect::from_center_size(
            card_rect.center() - Vec2::new(0.0, 24.0),
            Vec2::splat(icon_size),
        );
        ui.painter().image(
            icon,
            icon_rect,
            eframe::egui::Rect::from_min_max(
                eframe::egui::Pos2::ZERO,
                eframe::egui::pos2(1.0, 1.0),
            ),
            foreground,
        );
        ui.painter().text(
            card_rect.center() + Vec2::new(0.0, 51.0),
            eframe::egui::Align2::CENTER_CENTER,
            label,
            FontId::monospace(14.0),
            foreground,
        );
        response.clicked()
    }

    fn draw_power_panel(&mut self, ctx: &Context, monitor_size: Vec2) {
        if let (Some(action), Some(started)) = (
            self.scheduled_power_action,
            self.scheduled_power_action_started,
        ) && started.elapsed() >= Duration::from_secs(POWER_ACTION_DELAY_SECONDS as u64)
        {
            // Keep the cancellable countdown entirely inside Overbar. Calling
            // shutdown.exe only after it expires with /t 0 avoids Windows'
            // separate "You're about to be signed out" countdown dialog.
            self.scheduled_power_action_started = None;
            if !schedule_system_power_action(action, 0) {
                self.scheduled_power_action = None;
                record_startup_event(&format!(
                    "failed to launch immediate {}",
                    if action == PowerAction::Restart {
                        "restart"
                    } else {
                        "shutdown"
                    }
                ));
            }
        }
        if self.power_panel_closing
            && self.power_panel_opened_at.elapsed()
                >= Duration::from_secs_f32(POWER_PANEL_FADE_SECONDS)
        {
            self.power_panel_closing = false;
            if let Some(action) = self.pending_power_action.take() {
                trigger_power_action(action);
            }
        }

        let animation_time = self.power_panel_opened_at.elapsed().as_secs_f32()
            / POWER_PANEL_FADE_SECONDS;
        let animation = smootherstep(animation_time.clamp(0.0, 1.0));
        let opacity = if self.power_panel_closing {
            1.0 - animation
        } else if self.power_panel_open {
            animation
        } else {
            0.0
        };
        let panel_visible = self.power_panel_open || self.power_panel_closing;
        let panel_builder = ViewportBuilder::default()
            .with_title("Overbar Power Menu")
            .with_inner_size([monitor_size.x, monitor_size.y])
            .with_min_inner_size([monitor_size.x, monitor_size.y])
            .with_max_inner_size([monitor_size.x, monitor_size.y])
            .with_position([0.0, 0.0])
            .with_transparent(true)
            .with_decorations(false)
            .with_resizable(false)
            .with_taskbar(false)
            .with_active(false)
            .with_visible(panel_visible)
            .with_window_level(WindowLevel::AlwaysOnTop);

        let lock_icon = self.lock_icon.id();
        let sleep_icon = self.sleep_icon.id();
        let restart_icon = self.restart_icon.id();
        let shutdown_icon = self.shutdown_icon.id();
        let accent = self.accent_color;
        let scheduled_action = self.scheduled_power_action;
        let scheduled_action_can_cancel = self.scheduled_power_action_started.is_some();
        let mut action = None::<PowerAction>;
        let mut cancel_requested = false;
        let mut close_requested = false;
        ctx.show_viewport_immediate(
            ViewportId::from_hash_of("overbar-power-menu"),
            panel_builder,
            |panel_ctx, _viewport_class| {
                if panel_visible {
                    panel_ctx.request_repaint_after(Duration::from_millis(16));
                }
                if panel_ctx.input(|input| input.viewport().close_requested()) {
                    close_requested = true;
                }
                CentralPanel::default()
                    .frame(Frame::new().fill(Color32::TRANSPARENT).inner_margin(Margin::ZERO))
                    .show(panel_ctx, |ui| {
                        let screen = ui.max_rect();
                        ui.painter().rect_filled(
                            screen,
                            CornerRadius::ZERO,
                            Color32::from_rgba_unmultiplied(
                                9,
                                11,
                                15,
                                (92.0 * opacity).round() as u8,
                            ),
                        );

                        if let Some(scheduled_action) = scheduled_action {
                            let status = match scheduled_action {
                                PowerAction::Shutdown => "Waiting for shutdown...",
                                PowerAction::Restart => "Waiting for restart...",
                                _ => "Waiting...",
                            };
                            ui.painter().text(
                                screen.center() - Vec2::new(0.0, 22.0),
                                eframe::egui::Align2::CENTER_CENTER,
                                status,
                                FontId::monospace(19.0),
                                TEXT_PRIMARY.gamma_multiply(opacity),
                            );

                            if scheduled_action_can_cancel {
                                let cancel_rect = eframe::egui::Rect::from_center_size(
                                    screen.center() + Vec2::new(0.0, 30.0),
                                    Vec2::new(116.0, 38.0),
                                );
                                let cancel_id = ui.id().with("cancel-scheduled-power-action");
                                let cancel_response = ui
                                    .interact(cancel_rect, cancel_id, Sense::click())
                                    .on_hover_cursor(CursorIcon::PointingHand);
                                let hover = ui.ctx().animate_bool_with_time(
                                    cancel_id.with("hover"),
                                    cancel_response.hovered(),
                                    0.16,
                                );
                                ui.painter().rect_filled(
                                    cancel_rect.expand(2.0 * hover),
                                    CornerRadius::same(9),
                                    Color32::from_rgba_unmultiplied(
                                        9,
                                        11,
                                        15,
                                        ((38.0 + 82.0 * hover) * opacity).round() as u8,
                                    ),
                                );
                                ui.painter().text(
                                    cancel_rect.center(),
                                    eframe::egui::Align2::CENTER_CENTER,
                                    "Cancel",
                                    FontId::monospace(12.0),
                                    TEXT_PRIMARY.gamma_multiply(opacity),
                                );
                                if cancel_response.clicked() {
                                    cancel_requested = true;
                                }
                            }
                            return;
                        }

                        let back_rect = eframe::egui::Rect::from_min_size(
                            screen.min + Vec2::new(24.0, 22.0),
                            Vec2::new(104.0, 38.0),
                        );
                        let back_id = ui.id().with("power-back");
                        let back_response = ui
                            .interact(back_rect, back_id, Sense::click())
                            .on_hover_cursor(CursorIcon::PointingHand);
                        let back_hover = ui.ctx().animate_bool_with_time(
                            back_id.with("hover"),
                            back_response.hovered(),
                            0.16,
                        );
                        ui.painter().rect_filled(
                            back_rect.expand(2.0 * back_hover),
                            CornerRadius::same(9),
                            Color32::from_rgba_unmultiplied(
                                9,
                                11,
                                15,
                                ((20.0 + 50.0 * back_hover) * opacity).round() as u8,
                            ),
                        );
                        ui.painter().text(
                            back_rect.center(),
                            eframe::egui::Align2::CENTER_CENTER,
                            "‹  Back",
                            FontId::monospace(12.0),
                            TEXT_PRIMARY.gamma_multiply(opacity),
                        );
                        if back_response.clicked() {
                            close_requested = true;
                        }

                        let card_width = (screen.width() * 0.12).clamp(145.0, 190.0);
                        let card_height = (screen.height() * 0.22).clamp(170.0, 205.0);
                        let gap = (screen.width() * 0.018).clamp(18.0, 34.0);
                        let row_width = card_width * 4.0 + gap * 3.0;
                        let row_origin = eframe::egui::pos2(
                            screen.center().x - row_width / 2.0,
                            screen.center().y - card_height / 2.0
                                + 12.0 * (1.0 - opacity),
                        );
                        for (index, (label, icon, power_action, color)) in [
                            ("Lock", lock_icon, PowerAction::Lock, accent),
                            ("Sleep", sleep_icon, PowerAction::Sleep, accent),
                            ("Restart", restart_icon, PowerAction::Restart, accent),
                            (
                                "Shutdown",
                                shutdown_icon,
                                PowerAction::Shutdown,
                                USAGE_CRITICAL,
                            ),
                        ]
                        .into_iter()
                        .enumerate()
                        {
                            let card_rect = eframe::egui::Rect::from_min_size(
                                row_origin + Vec2::new(index as f32 * (card_width + gap), 0.0),
                                Vec2::new(card_width, card_height),
                            );
                            if Self::draw_power_option(
                                ui,
                                card_rect,
                                ui.id().with(("power-option", label)),
                                icon,
                                label,
                                color,
                                opacity,
                            ) {
                                action = Some(power_action);
                            }
                        }
                    });
            },
        );
        configure_windows_power_overlay();
        if panel_visible {
            ensure_windows_overlay_topmost("Overbar Power Menu");
        }

        if cancel_requested {
            self.scheduled_power_action = None;
            self.scheduled_power_action_started = None;
            self.power_panel_open = true;
            self.power_panel_closing = false;
            self.power_panel_opened_at = Instant::now() -
                Duration::from_secs_f32(POWER_PANEL_FADE_SECONDS);
        }
        if let Some(action) = action {
            if matches!(action, PowerAction::Shutdown | PowerAction::Restart) {
                self.scheduled_power_action = Some(action);
                self.scheduled_power_action_started = Some(Instant::now());
                self.pending_power_action = None;
                self.power_panel_open = true;
                self.power_panel_closing = false;
            } else {
                self.pending_power_action = Some(action);
                close_requested = true;
            }
        }
        if close_requested && self.scheduled_power_action.is_none() {
            self.begin_power_panel_close();
        }
        if panel_visible {
            ctx.request_repaint_after(Duration::from_millis(16));
        }
    }

    fn draw_apps_panel(&mut self, ctx: &Context, monitor_width: f32) {
        let apps = self.workspaces.apps.clone();
        if self.apps_panel_open {
            for app in &apps {
                let Some(handle) = app.window_handle else {
                    continue;
                };
                if self.app_icons.contains_key(&handle) {
                    continue;
                }
                if let Some(image) = window_icon_image(handle, 24) {
                    let texture = ctx.load_texture(
                        format!("app-icon-{handle}"),
                        image,
                        TextureOptions::LINEAR,
                    );
                    self.app_icons.insert(handle, texture);
                }
            }
        }

        let open_progress = ease_out_cubic(
            (self.apps_panel_opened_at.elapsed().as_secs_f32() / PANEL_OPEN_SECONDS)
                .clamp(0.0, 1.0),
        );
        let animated_height = (APPS_PANEL_HEIGHT * open_progress).max(1.0);
        let panel_x = self
            .apps_icon_rect
            .left()
            .clamp(0.0, (monitor_width - APPS_PANEL_WIDTH).max(0.0));
        let panel_builder = ViewportBuilder::default()
            .with_title("Overbar Apps Panel")
            .with_inner_size([APPS_PANEL_WIDTH, APPS_PANEL_HEIGHT])
            .with_min_inner_size([APPS_PANEL_WIDTH, APPS_PANEL_HEIGHT])
            .with_max_inner_size([APPS_PANEL_WIDTH, APPS_PANEL_HEIGHT])
            .with_position([panel_x, BAR_HEIGHT + PANEL_GAP])
            .with_transparent(true)
            .with_decorations(false)
            .with_resizable(false)
            .with_taskbar(false)
            .with_active(false)
            .with_visible(self.apps_panel_open)
            .with_window_level(WindowLevel::AlwaysOnTop);

        let workspace_names = self
            .workspaces
            .items
            .iter()
            .map(|workspace| workspace.name.clone())
            .collect::<Vec<_>>();
        let available_update = self.available_update.clone();
        let completed_update = self.completed_update.clone();
        let icons = self.app_icons.clone();
        let mut jump_to: Option<(Option<isize>, String)> = None;
        let mut close_window = None;
        let mut start_update = false;
        let mut view_changelog = None;
        ctx.show_viewport_immediate(
            ViewportId::from_hash_of("overbar-apps-panel"),
            panel_builder,
            |panel_ctx, _viewport_class| {
                if panel_ctx.input(|input| input.viewport().close_requested()) {
                    self.apps_panel_open = false;
                }
                CentralPanel::default()
                    .frame(Frame::new().fill(Color32::TRANSPARENT).inner_margin(Margin::ZERO))
                    .show(panel_ctx, |ui| {
                        let reveal_rect = eframe::egui::Rect::from_min_size(
                            ui.max_rect().min,
                            Vec2::new(APPS_PANEL_WIDTH, animated_height),
                        );
                        ui.set_clip_rect(reveal_rect);
                        Frame::new()
                            .fill(pill_background())
                            .inner_margin(Margin::same(12))
                            .show(ui, |ui| {
                                ui.set_width(APPS_PANEL_WIDTH - 24.0);
                                ui.set_height(APPS_PANEL_HEIGHT - 24.0);
                                ui.horizontal(|ui| {
                                    ui.spacing_mut().item_spacing.x = 10.0;
                                    ui.label(
                                        RichText::new("Apps")
                                            .font(FontId::monospace(13.0))
                                            .strong()
                                            .color(TEXT_PRIMARY),
                                    );
                                    ui.label(
                                        RichText::new("·")
                                            .font(FontId::monospace(13.0))
                                            .color(TEXT_MUTED),
                                    );
                                    ui.label(
                                        RichText::new(format!("{} open", apps.len()))
                                            .font(FontId::monospace(13.0))
                                            .color(TEXT_MUTED),
                                    );
                                });
                                ui.add_space(8.0);
                                let footer_height = if available_update.is_some()
                                    || completed_update.is_some()
                                {
                                    44.0
                                } else {
                                    32.0
                                };
                                let footer_gap = 6.0;
                                let scroll_height =
                                    (ui.available_height() - footer_height - footer_gap).max(1.0);
                                ScrollArea::vertical()
                                    .auto_shrink([false, false])
                                    .min_scrolled_height(scroll_height)
                                    .max_height(scroll_height)
                                    .show(ui, |ui| {
                                        if apps.is_empty() {
                                            ui.label(
                                                RichText::new("No managed apps")
                                                    .font(FontId::monospace(10.0))
                                                    .color(TEXT_MUTED),
                                            );
                                        }
                                        for workspace in &workspace_names {
                                            let workspace_apps = apps
                                                .iter()
                                                .filter(|app| &app.workspace == workspace)
                                                .collect::<Vec<_>>();
                                            if workspace_apps.is_empty() {
                                                continue;
                                            }
                                            ui.horizontal(|ui| {
                                                ui.label(
                                                    RichText::new(format!(
                                                        "Workspace {workspace}"
                                                    ))
                                                    .font(FontId::monospace(11.0))
                                                    .strong()
                                                    .color(self.accent_color),
                                                );
                                                ui.label(
                                                    RichText::new(format!(
                                                        "{} {}",
                                                        workspace_apps.len(),
                                                        if workspace_apps.len() == 1 {
                                                            "app"
                                                        } else {
                                                            "apps"
                                                        }
                                                    ))
                                                    .font(FontId::monospace(9.0))
                                                    .color(TEXT_MUTED),
                                                );
                                            });
                                            ui.add_space(4.0);
                                            for app in workspace_apps {
                                                ui.allocate_ui_with_layout(
                                                    Vec2::new(404.0, 42.0),
                                                    Layout::left_to_right(Align::Center),
                                                    |ui| {
                                                        let row_rect = ui.max_rect();
                                                        let actions_rect = eframe::egui::Rect::from_min_max(
                                                            eframe::egui::pos2(
                                                                row_rect.right() - 100.0,
                                                                row_rect.top(),
                                                            ),
                                                            row_rect.max,
                                                        );
                                                        let info_rect = eframe::egui::Rect::from_min_max(
                                                            row_rect.min,
                                                            eframe::egui::pos2(
                                                                actions_rect.left() - 10.0,
                                                                row_rect.bottom(),
                                                            ),
                                                        );
                                                        let info_response = ui.interact(
                                                            info_rect,
                                                            ui.id().with(("open-app", &app.window_id)),
                                                            Sense::click(),
                                                        );
                                                        let info_response = info_response
                                                            .on_hover_cursor(
                                                                CursorIcon::PointingHand,
                                                            );
                                                        let (name_color, title_color) = if info_response.hovered() {
                                                            (self.accent_color, self.accent_color)
                                                        } else {
                                                            (TEXT_PRIMARY, TEXT_MUTED)
                                                        };
                                                        let icon_rect = eframe::egui::Rect::from_center_size(
                                                            eframe::egui::pos2(
                                                                info_rect.left() + 12.0,
                                                                info_rect.center().y,
                                                            ),
                                                            Vec2::splat(24.0),
                                                        );
                                                        if let Some(texture) = app
                                                            .window_handle
                                                            .and_then(|handle| icons.get(&handle))
                                                        {
                                                            ui.put(
                                                                icon_rect,
                                                                eframe::egui::Image::new((
                                                                    texture.id(),
                                                                    Vec2::splat(24.0),
                                                                )),
                                                            );
                                                        } else {
                                                            ui.painter().rect_filled(
                                                                icon_rect,
                                                                CornerRadius::same(4),
                                                                Color32::from_rgba_unmultiplied(
                                                                    self.accent_color.r(),
                                                                    self.accent_color.g(),
                                                                    self.accent_color.b(),
                                                                    65,
                                                                ),
                                                            );
                                                            ui.painter().text(
                                                                icon_rect.center(),
                                                                eframe::egui::Align2::CENTER_CENTER,
                                                                app.process_name
                                                                    .chars()
                                                                    .next()
                                                                    .unwrap_or('?')
                                                                    .to_uppercase()
                                                                    .to_string(),
                                                                FontId::monospace(11.0),
                                                                TEXT_PRIMARY,
                                                            );
                                                        }
                                                        let text_x = info_rect.left() + 34.0;
                                                        let text_painter = ui
                                                            .painter()
                                                            .with_clip_rect(info_rect.shrink2(
                                                                Vec2::new(0.0, 2.0),
                                                            ));
                                                        let name_pos = eframe::egui::pos2(
                                                            text_x,
                                                            info_rect.center().y - 6.5,
                                                        );
                                                        let title_pos = eframe::egui::pos2(
                                                            text_x,
                                                            info_rect.center().y + 7.0,
                                                        );
                                                        for offset in [-0.2_f32, 0.2] {
                                                            text_painter.text(
                                                                name_pos + Vec2::new(offset, 0.0),
                                                                eframe::egui::Align2::LEFT_CENTER,
                                                                &app.process_name,
                                                                FontId::monospace(10.0),
                                                                name_color,
                                                            );
                                                        }
                                                        text_painter.text(
                                                            title_pos,
                                                            eframe::egui::Align2::LEFT_CENTER,
                                                            ellipsize_title(&app.title, 34),
                                                            FontId::monospace(9.0),
                                                            title_color,
                                                        );
                                                        if info_response.clicked() {
                                                            jump_to = Some((
                                                                app.window_handle,
                                                                app.workspace.clone(),
                                                            ));
                                                        }
                                                        let end_rect = eframe::egui::Rect::from_center_size(
                                                            eframe::egui::pos2(
                                                                actions_rect.right() - 24.0,
                                                                actions_rect.center().y,
                                                            ),
                                                            Vec2::new(48.0, 26.0),
                                                        );
                                                        let jump_rect = eframe::egui::Rect::from_center_size(
                                                            eframe::egui::pos2(
                                                                actions_rect.left() + 18.0,
                                                                actions_rect.center().y,
                                                            ),
                                                            Vec2::new(36.0, 22.0),
                                                        );
                                                        if Self::draw_end_action_at(
                                                            ui,
                                                            end_rect,
                                                            ui.id().with(("end-app", &app.window_id)),
                                                            true,
                                                        ) {
                                                            close_window =
                                                                Some(app.window_id.clone());
                                                        }
                                                        if Self::draw_text_action_at(
                                                            ui,
                                                            jump_rect,
                                                            ui.id().with(("jump-app", &app.window_id)),
                                                            "Jump",
                                                            TEXT_PRIMARY,
                                                            self.accent_color,
                                                        ) {
                                                            jump_to = Some((
                                                                app.window_handle,
                                                                app.workspace.clone(),
                                                            ));
                                                        }
                                                    },
                                                );
                                            }
                                            ui.add_space(9.0);
                                        }
                                    });
                                ui.add_space(footer_gap);
                                let (footer_rect, _) = ui.allocate_exact_size(
                                    Vec2::new(ui.available_width(), footer_height),
                                    Sense::hover(),
                                );
                                let settings_rect = eframe::egui::Rect::from_center_size(
                                    eframe::egui::pos2(
                                        footer_rect.left() + 16.0,
                                        footer_rect.bottom() - 16.0,
                                    ),
                                    Vec2::splat(24.0),
                                );
                                let settings_response = ui
                                    .interact(
                                        settings_rect,
                                        ui.id().with("wm-settings"),
                                        Sense::click(),
                                    )
                                    .on_hover_cursor(CursorIcon::PointingHand);
                                let settings_tint = if settings_response.hovered() {
                                    self.accent_color
                                } else {
                                    TEXT_PRIMARY
                                };
                                ui.painter().image(
                                    self.settings_icon.id(),
                                    eframe::egui::Rect::from_center_size(
                                        settings_rect.center(),
                                        Vec2::splat(18.0),
                                    ),
                                    eframe::egui::Rect::from_min_max(
                                        eframe::egui::Pos2::ZERO,
                                        eframe::egui::pos2(1.0, 1.0),
                                    ),
                                    settings_tint,
                                );
                                let update_error = self.update_error.clone();
                                let copied_feedback = self
                                    .update_error_copied_at
                                    .is_some_and(|copied_at| {
                                        copied_at.elapsed() < Duration::from_millis(1500)
                                    });
                                if copied_feedback {
                                    ui.ctx().request_repaint_after(Duration::from_millis(50));
                                } else {
                                    self.update_error_copied_at = None;
                                }
                                let footer_status = if copied_feedback {
                                    "Copied!".to_owned()
                                } else {
                                    update_error.as_ref().map_or_else(
                                        || format!("v{}", env!("CARGO_PKG_VERSION")),
                                        |error| {
                                        let summary = error
                                            .split_whitespace()
                                            .collect::<Vec<_>>()
                                            .join(" ");
                                        format!("Copy · {}", ellipsize_title(&summary, 55))
                                        },
                                    )
                                };
                                let footer_status_rect = eframe::egui::Rect::from_min_max(
                                    eframe::egui::pos2(
                                        footer_rect.left() + 34.0,
                                        footer_rect.bottom() - 17.0,
                                    ),
                                    footer_rect.right_bottom(),
                                );
                                let footer_status_response = ui
                                    .interact(
                                        footer_status_rect,
                                        ui.id().with("copy-update-error"),
                                        if update_error.is_some() {
                                            Sense::click()
                                        } else {
                                            Sense::hover()
                                        },
                                    )
                                    .on_hover_cursor(if update_error.is_some() {
                                        CursorIcon::PointingHand
                                    } else {
                                        CursorIcon::Default
                                    });
                                ui.painter().text(
                                    eframe::egui::pos2(
                                        footer_rect.right() - 4.0,
                                        footer_rect.bottom() - 3.0,
                                    ),
                                    eframe::egui::Align2::RIGHT_BOTTOM,
                                    footer_status,
                                    FontId::monospace(8.0),
                                    if update_error.is_some() {
                                        if copied_feedback {
                                            USAGE_CRITICAL
                                        } else if footer_status_response.hovered() {
                                            Color32::from_rgb(225, 125, 135)
                                        } else {
                                            USAGE_CRITICAL
                                        }
                                    } else {
                                        STAT_LABEL
                                    },
                                );
                                if footer_status_response.clicked()
                                    && let Some(error) = update_error
                                {
                                    ui.ctx().copy_text(error);
                                    self.update_error_copied_at = Some(Instant::now());
                                }
                                if available_update.is_some() || completed_update.is_some() {
                                    let update_rect = eframe::egui::Rect::from_min_size(
                                        eframe::egui::pos2(
                                            footer_rect.right() - 118.0,
                                            footer_rect.top(),
                                        ),
                                        Vec2::new(114.0, 22.0),
                                    );
                                    let update_response = ui
                                        .interact(
                                            update_rect,
                                            ui.id().with("install-overbar-update"),
                                            if self.update_in_progress
                                                && completed_update.is_none()
                                            {
                                                Sense::hover()
                                            } else {
                                                Sense::click()
                                            },
                                        )
                                        .on_hover_cursor(if self.update_in_progress
                                            && completed_update.is_none()
                                        {
                                            CursorIcon::Default
                                        } else {
                                            CursorIcon::PointingHand
                                        });
                                    let update_text = if completed_update.is_some() {
                                        if update_response.hovered() {
                                            "View Changelog".to_owned()
                                        } else {
                                            "Update Complete!".to_owned()
                                        }
                                    } else if self.update_in_progress {
                                        "Updating...".to_owned()
                                    } else if self.update_error.is_some() {
                                        "Retry Update?".to_owned()
                                    } else {
                                        "Update Available!".to_owned()
                                    };
                                    let update_text_color = if completed_update.is_some() {
                                        if update_response.hovered() {
                                            Color32::from_rgb(196, 218, 177)
                                        } else {
                                            UPDATE_COMPLETE
                                        }
                                    } else if self.update_in_progress {
                                        TEXT_MUTED
                                    } else if self.update_error.is_some() {
                                        if update_response.hovered() {
                                            Color32::from_rgb(225, 125, 135)
                                        } else {
                                            USAGE_CRITICAL
                                        }
                                    } else if update_response.hovered() {
                                        Color32::from_rgb(250, 226, 132)
                                    } else {
                                        UPDATE_NOTICE
                                    };
                                    let update_font = FontId::monospace(9.0);
                                    let update_text_width = ui
                                        .painter()
                                        .layout_no_wrap(
                                            update_text.clone(),
                                            update_font.clone(),
                                            update_text_color,
                                        )
                                        .size()
                                        .x;
                                    ui.painter().text(
                                        update_rect.right_center(),
                                        eframe::egui::Align2::RIGHT_CENTER,
                                        update_text,
                                        update_font,
                                        update_text_color,
                                    );
                                    if let Some(notice) = self
                                        .update_notice
                                        .filter(|_| !self.update_in_progress)
                                    {
                                        ui.painter().circle_filled(
                                            eframe::egui::pos2(
                                                update_rect.right()
                                                    - update_text_width
                                                    - 7.0,
                                                update_rect.center().y,
                                            ),
                                            2.5,
                                            match notice {
                                                UpdateNotice::Available => UPDATE_NOTICE,
                                                UpdateNotice::Failed => USAGE_CRITICAL,
                                                UpdateNotice::Complete => UPDATE_COMPLETE,
                                            },
                                        );
                                    }
                                    if update_response.clicked() {
                                        if let Some(completed) = &completed_update {
                                            view_changelog = Some(completed.release_url.clone());
                                        } else if !self.update_in_progress {
                                            start_update = true;
                                        }
                                    }
                                }
                                if settings_response.clicked() {
                                    self.apps_panel_open = false;
                                    reset_windows_wm_settings_overlay();
                                    self.wm_settings_closing = false;
                                    self.wm_settings_transition_started = Instant::now();
                                    self.wm_settings_open = true;
                                }
                            });
                    });
            },
        );
        configure_windows_apps_overlay();
        if self.apps_panel_open {
            ensure_windows_overlay_topmost("Overbar Apps Panel");
        }

        if let Some((handle, workspace)) = jump_to {
            if let Some(handle) = handle {
                self.focus_window(handle, &workspace);
            } else {
                self.focus_workspace(&workspace);
            }
            self.apps_panel_open = false;
        }
        if let Some(window_id) = close_window {
            self.close_window(&window_id);
        }
        if let Some(release_url) = view_changelog {
            let _ = thread::Builder::new()
                .name("overbar-changelog-open".into())
                .spawn(move || open_search_path(Path::new(&release_url)));
        }
        if start_update {
            self.update_error = None;
            self.update_error_copied_at = None;
            self.update_notice = None;
            self.update_notice_seen_in_menu = false;
            if let Some(update) = self.available_update.clone() {
                if self
                    .update_requests
                    .send(UpdateRequest::Install(update))
                    .is_ok()
                {
                    self.update_in_progress = true;
                } else {
                    self.update_error = Some("Update worker is unavailable".to_owned());
                }
            }
        }
    }

    fn draw_wm_settings_panel(&mut self, ctx: &Context) {
        if !self.wm_settings_open { return; }
        let linear = (self.wm_settings_transition_started.elapsed().as_secs_f32()
            / WM_SETTINGS_TRANSITION_SECONDS).clamp(0.0, 1.0);
        let eased = ease_out_cubic(linear);
        let settings_mix = if self.wm_settings_closing { 1.0 - eased } else { eased };
        let height_mix = if self.wm_settings_closing {
            // Let the content leave first, then collapse the panel back to the
            // app-manager height beneath it.
            1.0 - ease_out_cubic(((linear - 0.35) / 0.65).clamp(0.0, 1.0))
        } else {
            // Expand first, then let the settings page travel into the new room.
            ease_out_cubic((linear / 0.65).clamp(0.0, 1.0))
        };
        let animated_height = APPS_PANEL_HEIGHT
            + (WM_SETTINGS_PANEL_HEIGHT - APPS_PANEL_HEIGHT) * height_mix;
        if linear < 1.0 {
            ctx.request_repaint();
        }
        let builder = ViewportBuilder::default()
            .with_title("Overbar WM Settings")
            .with_inner_size([440.0, animated_height])
            .with_min_inner_size([440.0, animated_height])
            .with_max_inner_size([440.0, animated_height])
            .with_position([12.0, BAR_HEIGHT + PANEL_GAP])
            .with_transparent(true)
            .with_decorations(false)
            .with_resizable(false)
            .with_taskbar(false)
            .with_visible(true)
            .with_window_level(WindowLevel::AlwaysOnTop);
        let mut changed = false;
        let mut close = false;
        let mut back = false;
        ctx.show_viewport_immediate(
            ViewportId::from_hash_of("overbar-wm-settings"),
            builder,
            |settings_ctx, _| {
                if settings_ctx.input(|input| input.viewport().close_requested()) { close = true; }
                CentralPanel::default()
                    .frame(Frame::new().fill(Color32::TRANSPARENT).inner_margin(Margin::ZERO))
                    .show(settings_ctx, |ui| {
                        Frame::new()
                            .fill(pill_background())
                            .inner_margin(Margin::same(14))
                            .show(ui, |ui| {
                        let content_rect = ui.max_rect().translate(Vec2::new(
                            (1.0 - settings_mix) * APPS_PANEL_WIDTH,
                            0.0,
                        ));
                        ui.set_clip_rect(ui.max_rect());
                        ui.scope_builder(UiBuilder::new().max_rect(content_rect), |ui| {
                        ui.set_min_size(Vec2::new(412.0, 492.0));
                        ui.style_mut().visuals.extreme_bg_color = Color32::from_rgba_unmultiplied(0, 0, 0, 32);
                        ui.horizontal(|ui| {
                            ui.label(RichText::new("Window Manager Settings").font(FontId::monospace(13.0)).strong().color(TEXT_PRIMARY));
                            ui.with_layout(Layout::right_to_left(Align::Center), |ui| {
                                if Self::draw_panel_text_button(
                                    ui,
                                    ui.id().with("wm-settings-back"),
                                    "‹ Back",
                                    48.0,
                                    TEXT_MUTED,
                                    self.accent_color,
                                ) {
                                    back = true;
                                }
                            });
                        });
                        ui.add_space(10.0);
                        ScrollArea::vertical().auto_shrink([false, false]).show(ui, |ui| {
                            ui.label(RichText::new("Layout & media").font(FontId::monospace(11.0)).strong().color(self.accent_color));
                            ui.add_space(5.0);
                            ui.horizontal(|ui| {
                                ui.set_width(400.0);
                                ui.label(RichText::new("Window gap").font(FontId::monospace(9.5)).color(TEXT_PRIMARY));
                                ui.with_layout(Layout::right_to_left(Align::Center), |ui| {
                                    if Self::draw_panel_text_button(ui, ui.id().with("window-gap-plus"), "+", 24.0, TEXT_PRIMARY, self.accent_color) {
                                        self.wm_config.window_gap = (self.wm_config.window_gap + 1).min(64);
                                        changed = true;
                                    }
                                    ui.label(RichText::new(format!("{} px", self.wm_config.window_gap)).font(FontId::monospace(9.5)).color(TEXT_MUTED));
                                    if Self::draw_panel_text_button(ui, ui.id().with("window-gap-minus"), "−", 24.0, TEXT_PRIMARY, self.accent_color) {
                                        self.wm_config.window_gap = (self.wm_config.window_gap - 1).max(0);
                                        changed = true;
                                    }
                                });
                            });
                            ui.horizontal(|ui| {
                                ui.set_width(400.0);
                                ui.label(RichText::new("Media name width").font(FontId::monospace(9.5)).color(TEXT_PRIMARY));
                                ui.with_layout(Layout::right_to_left(Align::Center), |ui| {
                                    if Self::draw_panel_text_button(ui, ui.id().with("media-width-plus"), "+", 24.0, TEXT_PRIMARY, self.accent_color) {
                                        self.wm_config.media_name_width = (self.wm_config.media_name_width + 10.0).min(500.0);
                                        changed = true;
                                    }
                                    ui.label(RichText::new(format!("{:.0} px", self.wm_config.media_name_width)).font(FontId::monospace(9.5)).color(TEXT_MUTED));
                                    if Self::draw_panel_text_button(ui, ui.id().with("media-width-minus"), "−", 24.0, TEXT_PRIMARY, self.accent_color) {
                                        self.wm_config.media_name_width = (self.wm_config.media_name_width - 10.0).max(80.0);
                                        changed = true;
                                    }
                                });
                            });
                            ui.label(RichText::new("Long media names scroll after reaching the configured width.").font(FontId::monospace(8.5)).color(TEXT_MUTED));
                            ui.add_space(14.0);
                            ui.label(RichText::new("Keybindings").font(FontId::monospace(11.0)).strong().color(self.accent_color));
                            ui.add_space(5.0);
                            let mut keybinding_names = default_wm_keybindings().into_keys().collect::<Vec<_>>();
                            keybinding_names.sort();
                            for name in &keybinding_names {
                                ui.horizontal(|ui| {
                                    ui.set_width(400.0);
                                    ui.label(RichText::new(name).font(FontId::monospace(9.5)).color(TEXT_PRIMARY));
                                    ui.with_layout(Layout::right_to_left(Align::Center), |ui| {
                                        let binding = self.wm_config.keybindings.entry(name.clone()).or_default();
                                        changed |= ui.add(TextEdit::singleline(binding).desired_width(145.0).font(FontId::monospace(9.5))).changed();
                                    });
                                });
                            }
                            ui.add_space(14.0);
                            ui.label(RichText::new("Ignore minimum size").font(FontId::monospace(11.0)).strong().color(self.accent_color));
                            ui.label(RichText::new("Executable names here are forcibly tiled, ignoring their reported minimum size.").font(FontId::monospace(8.5)).color(TEXT_MUTED));
                            ui.add_space(5.0);
                            let mut remove = None;
                            for (index, app) in self.wm_config.ignore_minimum_size_apps.iter_mut().enumerate() {
                                ui.horizontal(|ui| {
                                    changed |= ui.add(TextEdit::singleline(app).hint_text("example.exe").desired_width(330.0).font(FontId::monospace(9.5))).changed();
                                    if Self::draw_panel_text_button(
                                        ui,
                                        ui.id().with(("remove-minimum-size-ignore", index)),
                                        "Remove",
                                        52.0,
                                        TEXT_MUTED,
                                        USAGE_CRITICAL,
                                    ) { remove = Some(index); }
                                });
                            }
                            if let Some(index) = remove {
                                self.wm_config.ignore_minimum_size_apps.remove(index);
                                changed = true;
                            }
                            if Self::draw_panel_text_button(
                                ui,
                                ui.id().with("add-minimum-size-ignore"),
                                "+ Add application",
                                112.0,
                                TEXT_PRIMARY,
                                self.accent_color,
                            ) {
                                self.wm_config.ignore_minimum_size_apps.push(String::new());
                                changed = true;
                            }
                            ui.add_space(14.0);
                            ui.label(
                                RichText::new("Startup")
                                    .font(FontId::monospace(11.0))
                                    .strong()
                                    .color(self.accent_color),
                            );
                            ui.label(
                                RichText::new(
                                    "Create task pointing to current executable location to run at startup.",
                                )
                                .font(FontId::monospace(8.5))
                                .color(TEXT_MUTED),
                            );
                            if let Ok(executable) = env::current_exe() {
                                let path = executable.display().to_string();
                                ui.label(
                                    RichText::new(ellipsize_title(&path, 62))
                                        .font(FontId::monospace(8.5))
                                        .color(STAT_LABEL),
                                );
                            }
                            ui.add_space(4.0);
                            if self.startup_task_in_progress {
                                ui.label(
                                    RichText::new("Creating startup task...")
                                        .font(FontId::monospace(10.0))
                                        .color(TEXT_MUTED),
                                );
                            } else if Self::draw_panel_text_button(
                                ui,
                                ui.id().with("create-startup-task"),
                                "Create / refresh startup task",
                                190.0,
                                TEXT_PRIMARY,
                                self.accent_color,
                            ) {
                                self.startup_task_status = None;
                                if self.startup_task_requests.send(()).is_ok() {
                                    self.startup_task_in_progress = true;
                                } else {
                                    self.startup_task_status = Some((
                                        false,
                                        "Startup task worker is unavailable".to_owned(),
                                    ));
                                }
                            }
                            if let Some((success, status)) = &self.startup_task_status {
                                ui.label(
                                    RichText::new(ellipsize_title(status, 62))
                                        .font(FontId::monospace(8.5))
                                        .color(if *success {
                                            self.accent_color
                                        } else {
                                            USAGE_CRITICAL
                                        }),
                                );
                            }
                            ui.add_space(12.0);
                            if Self::draw_panel_text_button(
                                ui,
                                ui.id().with("restore-default-wm-keybindings"),
                                "Restore default keybindings",
                                170.0,
                                TEXT_PRIMARY,
                                self.accent_color,
                            ) {
                                self.wm_config.keybindings = default_wm_keybindings();
                                changed = true;
                            }
                        });
                        });
                            });
                    });
            },
        );
        configure_windows_wm_settings_overlay();
        ensure_windows_overlay_topmost("Overbar WM Settings");
        if changed {
            save_wm_config(&self.wm_config);
            let _ = self.window_manager_commands.send(WindowManagerCommand::UpdateConfig(self.wm_config.clone()));
        }
        if back {
            self.wm_settings_closing = true;
            self.wm_settings_transition_started = Instant::now();
        } else if close {
            self.wm_settings_open = false;
            self.wm_settings_closing = false;
            reset_windows_wm_settings_overlay();
        }
        if self.wm_settings_closing && linear >= 1.0 {
            self.wm_settings_open = false;
            self.wm_settings_closing = false;
            reset_windows_wm_settings_overlay();
            self.apps_panel_opened_at = Instant::now();
            self.apps_panel_open = true;
        }
    }

    fn draw_panel_text_button(
        ui: &mut eframe::egui::Ui,
        id: eframe::egui::Id,
        text: &str,
        width: f32,
        normal_color: Color32,
        hover_color: Color32,
    ) -> bool {
        let (rect, _) = ui.allocate_exact_size(Vec2::new(width, 22.0), Sense::hover());
        let response = ui.interact(rect, id, Sense::click()).on_hover_cursor(CursorIcon::PointingHand);
        ui.painter().text(
            rect.center(),
            eframe::egui::Align2::CENTER_CENTER,
            text,
            FontId::monospace(10.0),
            if response.hovered() { hover_color } else { normal_color },
        );
        response.clicked()
    }

    fn draw_text_action_at(
        ui: &mut eframe::egui::Ui,
        rect: eframe::egui::Rect,
        id: eframe::egui::Id,
        text: &str,
        normal_color: Color32,
        hover_color: Color32,
    ) -> bool {
        let font = FontId::monospace(10.0);
        let response = ui
            .interact(rect, id, Sense::click())
            .on_hover_cursor(CursorIcon::PointingHand);
        ui.painter().text(
            rect.center(),
            eframe::egui::Align2::CENTER_CENTER,
            text,
            font,
            if response.hovered() {
                hover_color
            } else {
                normal_color
            },
        );
        response.clicked()
    }

    fn draw_end_action_at(
        ui: &mut eframe::egui::Ui,
        rect: eframe::egui::Rect,
        id: eframe::egui::Id,
        enabled: bool,
    ) -> bool {
        let response = ui.interact(
            rect,
            id,
            if enabled {
                Sense::click()
            } else {
                Sense::hover()
            },
        );
        let response = if enabled {
            response.on_hover_cursor(CursorIcon::PointingHand)
        } else {
            Self::with_task_tooltip(response, "Windows protects this process")
        };
        let expansion = ui
            .ctx()
            .animate_bool_with_time(id.with("expanded"), enabled && response.hovered(), 0.14);

        if expansion > 0.0 {
            let button_rect = eframe::egui::Rect::from_center_size(
                rect.center(),
                Vec2::new(24.0 + 24.0 * expansion, 12.0 + 14.0 * expansion),
            );
            ui.painter().rect_filled(
                button_rect,
                CornerRadius::same(6),
                Color32::from_rgba_unmultiplied(191, 97, 106, (245.0 * expansion) as u8),
            );
        }

        let blend = |from: u8, to: u8| {
            (from as f32 + (to as f32 - from as f32) * expansion).round() as u8
        };
        let normal_color = if enabled { USAGE_CRITICAL } else { STAT_LABEL };
        ui.painter().text(
            rect.center(),
            eframe::egui::Align2::CENTER_CENTER,
            "End",
            FontId::monospace(10.0),
            Color32::from_rgb(
                blend(normal_color.r(), 255),
                blend(normal_color.g(), 255),
                blend(normal_color.b(), 255),
            ),
        );
        enabled && response.clicked()
    }

    fn with_task_tooltip(
        response: eframe::egui::Response,
        text: impl Into<String>,
    ) -> eframe::egui::Response {
        let text = text.into();
        response.on_hover_ui(move |ui| {
            // The native tooltip frame is styled once at startup. Keeping the
            // contents frame-free avoids a second border and doubled padding.
            ui.label(
                RichText::new(&text)
                    .font(FontId::monospace(9.0))
                    .color(TEXT_PRIMARY),
            );
        })
    }

    fn draw_panel(&mut self, ctx: &Context, monitor_width: f32) {
        let open_progress = ease_out_cubic(
            (self.panel_opened_at.elapsed().as_secs_f32() / PANEL_OPEN_SECONDS).clamp(0.0, 1.0),
        );
        let animated_height = (PANEL_HEIGHT * open_progress).max(1.0);
        let panel_pos = eframe::egui::pos2(
            (self.stats_pill_rect.right() - PANEL_WIDTH)
                .clamp(0.0, (monitor_width - PANEL_WIDTH).max(0.0)),
            BAR_HEIGHT + PANEL_GAP,
        );
        let panel_builder = ViewportBuilder::default()
            .with_title("Overbar System Panel")
            .with_inner_size([PANEL_WIDTH, PANEL_HEIGHT])
            .with_min_inner_size([PANEL_WIDTH, PANEL_HEIGHT])
            .with_max_inner_size([PANEL_WIDTH, PANEL_HEIGHT])
            .with_position(panel_pos)
            .with_transparent(true)
            .with_decorations(false)
            .with_resizable(false)
            .with_taskbar(false)
            .with_active(false)
            .with_visible(self.panel_open)
            .with_window_level(WindowLevel::AlwaysOnTop);

        let disks = self
            .disks
            .list()
            .iter()
            .map(|disk| {
                let name = disk.name().to_string_lossy();
                let mount = disk.mount_point().to_string_lossy();
                let display_name = if name.is_empty() {
                    mount.into_owned()
                } else if mount.is_empty() || name == mount {
                    name.into_owned()
                } else {
                    format!("{name} ({mount})")
                };
                (
                    display_name,
                    match disk.kind() {
                        DiskKind::SSD => "SSD".to_owned(),
                        DiskKind::HDD => "HDD".to_owned(),
                        DiskKind::Unknown(_) if disk.is_removable() => "USB".to_owned(),
                        DiskKind::Unknown(_) => "?".to_owned(),
                    },
                    disk.total_space(),
                    disk.available_space(),
                )
            })
            .collect::<Vec<_>>();
        let network = self
            .networks
            .iter()
            .filter(|(_, data)| {
                !data.mac_address().is_unspecified()
                    && data
                        .ip_networks()
                        .iter()
                        .any(|network| !network.addr.is_loopback())
            })
            .max_by_key(|(_, data)| data.total_received() + data.total_transmitted())
            .map(|(name, data)| {
                let ip = data
                    .ip_networks()
                    .iter()
                    .find(|network| network.addr.is_ipv4() && !network.addr.is_loopback())
                    .or_else(|| {
                        data.ip_networks()
                            .iter()
                            .find(|network| !network.addr.is_loopback())
                    })
                    .map_or_else(|| "Not available".to_owned(), |network| network.addr.to_string());
                (
                    name.clone(),
                    data.received(),
                    data.transmitted(),
                    data.total_received(),
                    data.total_transmitted(),
                    ip,
                    data.mac_address().to_string(),
                )
            });
        let logical_cpu_count = self.system.cpus().len().max(1) as f32;
        let mut tasks = self
            .system
            .processes()
            .iter()
            .map(|(pid, process)| TaskEntry {
                pid: pid.as_u32(),
                name: process.name().to_string_lossy().into_owned(),
                memory: process.memory(),
                cpu: (process.cpu_usage() / logical_cpu_count).clamp(0.0, 100.0),
                can_end: self
                    .task_end_permissions
                    .get(&pid.as_u32())
                    .copied()
                    .unwrap_or(false),
            })
            .collect::<Vec<_>>();
        tasks.sort_by(|left, right| {
            let ordering = match self.task_sort {
                TaskSort::Name => left
                    .name
                    .to_ascii_lowercase()
                    .cmp(&right.name.to_ascii_lowercase()),
                TaskSort::Memory => left.memory.cmp(&right.memory),
                TaskSort::Cpu => left.cpu.total_cmp(&right.cpu),
            };
            if self.task_sort_ascending {
                ordering
            } else {
                ordering.reverse()
            }
        });
        let mut requested_sort = None;
        let mut end_process = None;
        ctx.show_viewport_immediate(
            ViewportId::from_hash_of("overbar-system-panel"),
            panel_builder,
            |panel_ctx, _viewport_class| {
                if panel_ctx.input(|input| input.viewport().close_requested()) {
                    self.panel_open = false;
                }
                CentralPanel::default()
                    .frame(Frame::new().fill(Color32::TRANSPARENT).inner_margin(Margin::ZERO))
                    .show(panel_ctx, |ui| {
                let reveal_rect = eframe::egui::Rect::from_min_size(
                    ui.max_rect().min,
                    Vec2::new(PANEL_WIDTH, animated_height),
                );
                ui.set_clip_rect(reveal_rect);
                Frame::new()
                    .fill(pill_background())
                    .inner_margin(Margin::ZERO)
                    .show(ui, |ui| {
                        ui.set_width(PANEL_WIDTH);
                        ui.set_height(PANEL_HEIGHT);
                        ui.spacing_mut().item_spacing.x = 0.0;
                        ui.horizontal(|ui| {
                            ui.allocate_ui_with_layout(
                                Vec2::new(122.0, PANEL_HEIGHT),
                                Layout::top_down(Align::Min),
                                |ui| {
                                    ui.spacing_mut().item_spacing.y = 0.0;
                                    if Self::draw_panel_tab(
                                        ui,
                                        "▥",
                                        "Stats",
                                        self.panel_tab == PanelTab::Stats,
                                        self.accent_color,
                                    ) {
                                        self.panel_tab = PanelTab::Stats;
                                    }
                                    if Self::draw_panel_tab(
                                        ui,
                                        "▱",
                                        "Storage",
                                        self.panel_tab == PanelTab::Storage,
                                        self.accent_color,
                                    ) {
                                        self.panel_tab = PanelTab::Storage;
                                    }
                                    if Self::draw_panel_tab(
                                        ui,
                                        "◎",
                                        "Network",
                                        self.panel_tab == PanelTab::Network,
                                        self.accent_color,
                                    ) {
                                        self.panel_tab = PanelTab::Network;
                                    }
                                    if Self::draw_panel_tab(
                                        ui,
                                        "▤",
                                        "Tasks",
                                        self.panel_tab == PanelTab::Tasks,
                                        self.accent_color,
                                    ) {
                                        self.panel_tab = PanelTab::Tasks;
                                    }
                                },
                            );
                            ui.add_space(12.0);
                            ui.allocate_ui_with_layout(
                                Vec2::new(250.0, PANEL_HEIGHT),
                                Layout::top_down(Align::Min),
                                |ui| {
                                    ui.add_space(10.0);
                                    match self.panel_tab {
                                    PanelTab::Stats => {
                                        ui.label(
                                            RichText::new("System Stats")
                                                .font(FontId::monospace(13.0))
                                                .strong()
                                                .color(TEXT_PRIMARY),
                                        );
                                        ui.add_space(4.0);
                                        let host = System::host_name()
                                            .unwrap_or_else(|| "Windows PC".into());
                                        let os = System::long_os_version()
                                            .unwrap_or_else(|| "Windows".into());
                                        ui.label(
                                            RichText::new(format!("{host}  ·  {os}"))
                                                .font(FontId::monospace(10.0))
                                                .color(TEXT_MUTED),
                                        );
                                        ui.add_space(8.0);
                                        Self::draw_panel_metric(
                                            ui,
                                            "CPU",
                                            self.cpu_percent / 100.0,
                                            format!("{:.0}%", self.cpu_percent),
                                            usage_color(self.cpu_percent),
                                        );
                                        Self::draw_panel_metric(
                                            ui,
                                            "RAM",
                                            self.ram_percent / 100.0,
                                            format!("{:.0}%", self.ram_percent),
                                            usage_color(self.ram_percent),
                                        );
                                        if let Some(temp) = self.cpu_temperature {
                                            Self::draw_panel_metric(
                                                ui,
                                                "CPU temperature",
                                                temp / 100.0,
                                                format!("{temp:.0}°C"),
                                                usage_color(temp),
                                            );
                                        }
                                        let battery = self
                                            .battery_percent
                                            .map_or_else(|| "Not available".into(), |value| {
                                                format!("{value}%")
                                            });
                                        ui.horizontal(|ui| {
                                            ui.label(
                                                RichText::new("Battery")
                                                    .font(FontId::monospace(10.0))
                                                    .color(STAT_LABEL),
                                            );
                                            ui.with_layout(
                                                Layout::right_to_left(Align::Center),
                                                |ui| {
                                                    ui.label(
                                                        RichText::new(battery)
                                                            .font(FontId::monospace(10.0))
                                                            .color(TEXT_PRIMARY),
                                                    );
                                                },
                                            );
                                        });
                                        let uptime = System::uptime();
                                        ui.label(
                                            RichText::new(format!(
                                                "Uptime  {}d {:02}h {:02}m",
                                                uptime / 86_400,
                                                (uptime / 3_600) % 24,
                                                (uptime / 60) % 60
                                            ))
                                            .font(FontId::monospace(10.0))
                                            .color(TEXT_MUTED),
                                        );
                                    }
                                    PanelTab::Storage => {
                                        ui.label(
                                            RichText::new("Storage")
                                                .font(FontId::monospace(13.0))
                                                .strong()
                                                .color(TEXT_PRIMARY),
                                        );
                                        ui.add_space(6.0);
                                        ScrollArea::vertical()
                                            .auto_shrink([false, false])
                                            .show(ui, |ui| {
                                                if disks.is_empty() {
                                                    ui.label(
                                                        RichText::new("No storage volumes found")
                                                            .font(FontId::monospace(10.0))
                                                            .color(TEXT_MUTED),
                                                    );
                                                }
                                                for (name, kind, total, available) in &disks {
                                                    ui.horizontal(|ui| {
                                                        ui.label(
                                                            RichText::new(name)
                                                                .font(FontId::monospace(10.0))
                                                                .strong()
                                                                .color(TEXT_PRIMARY),
                                                        );
                                                        ui.with_layout(
                                                            Layout::right_to_left(Align::Center),
                                                            |ui| {
                                                                ui.label(
                                                                    RichText::new(kind)
                                                                    .font(FontId::monospace(10.0))
                                                                    .strong()
                                                                    .color(TEXT_PRIMARY),
                                                                );
                                                            },
                                                        );
                                                    });
                                                    let used = total.saturating_sub(*available);
                                                    let fraction = if *total == 0 {
                                                        0.0
                                                    } else {
                                                        used as f32 / *total as f32
                                                    };
                                                    ui.add(
                                                        eframe::egui::ProgressBar::new(fraction)
                                                            .desired_height(5.0)
                                                            .fill(self.accent_color),
                                                    );
                                                    ui.label(
                                                        RichText::new(format!(
                                                            "{} free of {}",
                                                            format_capacity(*available),
                                                            format_capacity(*total)
                                                        ))
                                                        .font(FontId::monospace(10.0))
                                                        .color(TEXT_PRIMARY),
                                                    );
                                                    ui.add_space(12.0);
                                                }
                                            });
                                    }
                                    PanelTab::Network => {
                                        ui.label(
                                            RichText::new("Network")
                                                .font(FontId::monospace(13.0))
                                                .strong()
                                                .color(TEXT_PRIMARY),
                                        );
                                        ui.add_space(6.0);
                                        if let Some((
                                            name,
                                            received,
                                            transmitted,
                                            total_received,
                                            total_transmitted,
                                            ip,
                                            mac,
                                        )) = &network
                                        {
                                            ui.label(
                                                RichText::new(name)
                                                    .font(FontId::monospace(10.0))
                                                    .color(TEXT_MUTED),
                                            );
                                            ui.add_space(5.0);
                                            Self::draw_panel_value(
                                                ui,
                                                "Download",
                                                &format!("↓ {}", format_rate(*received)),
                                            );
                                            Self::draw_panel_value(
                                                ui,
                                                "Upload",
                                                &format!("↑ {}", format_rate(*transmitted)),
                                            );
                                            ui.add_space(4.0);
                                            Self::draw_panel_value(
                                                ui,
                                                "Traffic received",
                                                &format_capacity(*total_received),
                                            );
                                            Self::draw_panel_value(
                                                ui,
                                                "Traffic sent",
                                                &format_capacity(*total_transmitted),
                                            );
                                            ui.add_space(4.0);
                                            Self::draw_panel_value(ui, "IP", ip);
                                            Self::draw_panel_value(ui, "MAC", mac);
                                        } else {
                                            ui.label(
                                                RichText::new("No active network interface")
                                                    .font(FontId::monospace(10.0))
                                                    .color(TEXT_MUTED),
                                            );
                                        }
                                    }
                                    PanelTab::Tasks => {
                                        ui.label(
                                            RichText::new("Tasks")
                                                .font(FontId::monospace(13.0))
                                                .strong()
                                                .color(TEXT_PRIMARY),
                                        );
                                        ui.add_space(3.0);
                                        ui.horizontal(|ui| {
                                            ui.spacing_mut().item_spacing.x = 0.0;
                                            if Self::draw_task_sort_header(
                                                ui,
                                                96.0,
                                                "Name",
                                                TaskSort::Name,
                                                self.task_sort,
                                                self.task_sort_ascending,
                                                self.accent_color,
                                            ) {
                                                requested_sort = Some(TaskSort::Name);
                                            }
                                            if Self::draw_task_sort_header(
                                                ui,
                                                52.0,
                                                "Memory",
                                                TaskSort::Memory,
                                                self.task_sort,
                                                self.task_sort_ascending,
                                                self.accent_color,
                                            ) {
                                                requested_sort = Some(TaskSort::Memory);
                                            }
                                            if Self::draw_task_sort_header(
                                                ui,
                                                36.0,
                                                "CPU",
                                                TaskSort::Cpu,
                                                self.task_sort,
                                                self.task_sort_ascending,
                                                self.accent_color,
                                            ) {
                                                requested_sort = Some(TaskSort::Cpu);
                                            }
                                            ui.allocate_space(Vec2::new(48.0, 18.0));
                                        });
                                        ui.add_space(2.0);
                                        ScrollArea::vertical()
                                            .auto_shrink([false, false])
                                            .show(ui, |ui| {
                                                ui.spacing_mut().item_spacing.y = 1.0;
                                                for task in &tasks {
                                                    let (row_rect, row_response) =
                                                        ui.allocate_exact_size(
                                                            Vec2::new(232.0, 24.0),
                                                            Sense::hover(),
                                                        );
                                                    let row_response = Self::with_task_tooltip(
                                                        row_response,
                                                        format!("PID {}", task.pid),
                                                    );
                                                    if row_response.hovered() {
                                                        ui.painter().rect_filled(
                                                            row_rect,
                                                            CornerRadius::same(4),
                                                            Color32::from_rgba_unmultiplied(
                                                                0, 0, 0, 28,
                                                            ),
                                                        );
                                                    }

                                                    let name_rect =
                                                        eframe::egui::Rect::from_min_size(
                                                            row_rect.min,
                                                            Vec2::new(96.0, 24.0),
                                                        );
                                                    let memory_rect =
                                                        eframe::egui::Rect::from_min_size(
                                                            eframe::egui::pos2(
                                                                name_rect.right(),
                                                                row_rect.top(),
                                                            ),
                                                            Vec2::new(52.0, 24.0),
                                                        );
                                                    let cpu_rect =
                                                        eframe::egui::Rect::from_min_size(
                                                            eframe::egui::pos2(
                                                                memory_rect.right(),
                                                                row_rect.top(),
                                                            ),
                                                            Vec2::new(36.0, 24.0),
                                                        );
                                                    let end_rect =
                                                        eframe::egui::Rect::from_min_size(
                                                            eframe::egui::pos2(
                                                                cpu_rect.right(),
                                                                row_rect.top(),
                                                            ),
                                                            Vec2::new(48.0, 24.0),
                                                        );
                                                    ui.painter()
                                                        .with_clip_rect(name_rect)
                                                        .text(
                                                            name_rect.left_center()
                                                                + Vec2::new(2.0, 0.0),
                                                            eframe::egui::Align2::LEFT_CENTER,
                                                            &task.name,
                                                            FontId::monospace(9.0),
                                                            TEXT_PRIMARY,
                                                        );
                                                    ui.painter().text(
                                                        memory_rect.center(),
                                                        eframe::egui::Align2::CENTER_CENTER,
                                                        format_task_memory(task.memory),
                                                        FontId::monospace(8.5),
                                                        TEXT_MUTED,
                                                    );
                                                    ui.painter().text(
                                                        cpu_rect.center(),
                                                        eframe::egui::Align2::CENTER_CENTER,
                                                        format!("{:.0}%", task.cpu),
                                                        FontId::monospace(8.5),
                                                        usage_color(task.cpu),
                                                    );
                                                    if Self::draw_end_action_at(
                                                        ui,
                                                        end_rect,
                                                        ui.id().with(("end-process", task.pid)),
                                                        task.can_end,
                                                    ) {
                                                        end_process = Some(task.pid);
                                                    }
                                                }
                                            });
                                    }
                                }
                                },
                            );
                        });
                    });
                });
            },
        );
        if let Some(sort) = requested_sort {
            if sort == self.task_sort {
                self.task_sort_ascending = !self.task_sort_ascending;
            } else {
                self.task_sort = sort;
                self.task_sort_ascending = sort == TaskSort::Name;
            }
            ctx.request_repaint();
        }
        if let Some(pid) = end_process {
            if let Some(process) = self.system.process(Pid::from_u32(pid)) {
                let _ = process.kill();
            }
            self.system
                .refresh_processes(ProcessesToUpdate::All, true);
            ctx.request_repaint();
        }
        configure_windows_panel_overlay();
        if self.panel_open {
            ensure_windows_overlay_topmost("Overbar System Panel");
        }
    }

    fn draw_task_sort_header(
        ui: &mut eframe::egui::Ui,
        width: f32,
        label: &str,
        column: TaskSort,
        selected: TaskSort,
        ascending: bool,
        accent_color: Color32,
    ) -> bool {
        let (rect, response) = ui.allocate_exact_size(Vec2::new(width, 18.0), Sense::click());
        let response = response.on_hover_cursor(CursorIcon::PointingHand);
        let text = if column == selected {
            format!("{label} {}", if ascending { "↑" } else { "↓" })
        } else {
            label.to_owned()
        };
        ui.painter().text(
            rect.left_center() + Vec2::new(2.0, 0.0),
            eframe::egui::Align2::LEFT_CENTER,
            text,
            FontId::monospace(8.5),
            if column == selected {
                accent_color
            } else if response.hovered() {
                TEXT_PRIMARY
            } else {
                STAT_LABEL
            },
        );
        response.clicked()
    }

    fn draw_panel_tab(
        ui: &mut eframe::egui::Ui,
        icon: &str,
        label: &str,
        selected: bool,
        accent_color: Color32,
    ) -> bool {
        let (rect, response) = ui.allocate_exact_size(
            Vec2::new(ui.available_width(), 38.0),
            Sense::click(),
        );
        let response = response.on_hover_cursor(CursorIcon::PointingHand);
        let background = if selected {
            Some(Color32::from_rgba_unmultiplied(
                accent_color.r(),
                accent_color.g(),
                accent_color.b(),
                90,
            ))
        } else if response.hovered() {
            Some(Color32::from_rgba_unmultiplied(0, 0, 0, 26))
        } else {
            None
        };
        if let Some(background) = background {
            ui.painter().rect_filled(rect, 0.0, background);
        }

        let icon_pos = eframe::egui::pos2(rect.left() + 14.0, rect.center().y);
        let label_pos = eframe::egui::pos2(rect.left() + 38.0, rect.center().y);
        ui.painter().text(
            icon_pos,
            eframe::egui::Align2::LEFT_CENTER,
            icon,
            FontId::monospace(13.0),
            TEXT_MUTED,
        );
        ui.painter().text(
            label_pos - Vec2::new(0.2, 0.0),
            eframe::egui::Align2::LEFT_CENTER,
            label,
            FontId::monospace(11.0),
            TEXT_PRIMARY,
        );
        ui.painter().text(
            label_pos + Vec2::new(0.2, 0.0),
            eframe::egui::Align2::LEFT_CENTER,
            label,
            FontId::monospace(11.0),
            TEXT_PRIMARY,
        );
        response.clicked()
    }

    fn draw_panel_value(ui: &mut eframe::egui::Ui, label: &str, value: &str) {
        ui.horizontal(|ui| {
            ui.label(
                RichText::new(label)
                    .font(FontId::monospace(10.0))
                    .color(STAT_LABEL),
            );
            ui.with_layout(Layout::right_to_left(Align::Center), |ui| {
                ui.label(
                    RichText::new(value)
                        .font(FontId::monospace(10.0))
                        .color(TEXT_PRIMARY),
                );
            });
        });
    }

    fn draw_panel_metric(
        ui: &mut eframe::egui::Ui,
        label: &str,
        fraction: f32,
        value: String,
        color: Color32,
    ) {
        ui.horizontal(|ui| {
            ui.label(
                RichText::new(label)
                    .font(FontId::monospace(10.0))
                    .color(STAT_LABEL),
            );
            ui.with_layout(Layout::right_to_left(Align::Center), |ui| {
                ui.label(
                    RichText::new(value)
                        .font(FontId::monospace(10.0))
                        .strong()
                        .color(color),
                );
            });
        });
        ui.add(
            eframe::egui::ProgressBar::new(fraction.clamp(0.0, 1.0))
                .desired_height(5.0)
                .fill(color),
        );
        ui.add_space(4.0);
    }

    fn draw_stat(
        ui: &mut eframe::egui::Ui,
        label: &str,
        value: String,
        value_color: Color32,
    ) {
        let label = ui
            .painter()
            .layout_no_wrap(label.to_owned(), FontId::monospace(BAR_FONT_SIZE), STAT_LABEL);
        let value = ui
            .painter()
            .layout_no_wrap(value, FontId::monospace(BAR_FONT_SIZE), value_color);
        let label_width = label.size().x;
        let total_width = label_width + STAT_LABEL_VALUE_GAP + value.size().x;
        let (rect, _) = ui.allocate_exact_size(
            Vec2::new(total_width, PILL_CONTENT_HEIGHT),
            Sense::hover(),
        );
        let start_x = rect.min.x;

        ui.painter().galley(
            eframe::egui::pos2(start_x, rect.center().y - label.size().y / 2.0),
            label,
            STAT_LABEL,
        );
        ui.painter().galley(
            eframe::egui::pos2(
                start_x + label_width + STAT_LABEL_VALUE_GAP,
                rect.center().y - value.size().y / 2.0,
            ),
            value,
            value_color,
        );
    }
}

fn format_capacity(bytes: u64) -> String {
    const KB: f64 = 1_000.0;
    const MB: f64 = 1_000_000.0;
    const GB: f64 = 1_000_000_000.0;
    const TB: f64 = 1_000_000_000_000.0;
    let bytes = bytes as f64;
    if bytes >= TB {
        format!("{:.2} TB", bytes / TB)
    } else if bytes >= GB {
        format!("{:.2} GB", bytes / GB)
    } else if bytes >= MB {
        format!("{:.2} MB", bytes / MB)
    } else if bytes >= KB {
        format!("{:.2} KB", bytes / KB)
    } else {
        format!("{bytes:.0} B")
    }
}

fn format_task_memory(bytes: u64) -> String {
    const KB: f64 = 1_000.0;
    const MB: f64 = 1_000_000.0;
    const GB: f64 = 1_000_000_000.0;
    let bytes = bytes as f64;
    if bytes >= GB {
        format!("{:.1}G", bytes / GB)
    } else if bytes >= MB {
        format!("{:.0}M", bytes / MB)
    } else if bytes >= KB {
        format!("{:.0}K", bytes / KB)
    } else {
        format!("{bytes:.0}B")
    }
}

fn format_rate(bytes: u64) -> String {
    const KB: f64 = 1_000.0;
    const MB: f64 = 1_000_000.0;
    const GB: f64 = 1_000_000_000.0;
    let bytes = bytes as f64;
    if bytes >= GB {
        format!("{:.1} GB/s", bytes / GB)
    } else if bytes >= MB {
        format!("{:.1} MB/s", bytes / MB)
    } else if bytes >= KB {
        format!("{:.1} KB/s", bytes / KB)
    } else {
        format!("{bytes:.0} B/s")
    }
}

fn ellipsize_title(title: &str, max_chars: usize) -> String {
    if title.chars().count() <= max_chars {
        return title.to_owned();
    }
    let mut shortened = title
        .chars()
        .take(max_chars.saturating_sub(1))
        .collect::<String>();
    shortened.push('…');
    shortened
}

fn calculator_result(query: &str) -> Option<String> {
    let normalized = query
        .trim()
        .strip_prefix('=')
        .unwrap_or(query.trim())
        .replace('×', "*")
        .replace('÷', "/")
        .replace('−', "-");
    if normalized.is_empty()
        || !normalized.chars().any(|character| {
            "+-*/%^!(),".contains(character) || character.is_ascii_alphabetic()
        })
    {
        return None;
    }
    let value = ScientificParser::new(&normalized).parse()?;
    if !value.is_finite() {
        return None;
    }
    let value = if value == -0.0 { 0.0 } else { value };
    if value.fract() == 0.0 && value.abs() < 1.0e15 {
        return Some(format!("{value:.0}"));
    }
    if value != 0.0 && !(1.0e-8..1.0e12).contains(&value.abs()) {
        return Some(format!("{value:.10e}"));
    }
    let mut formatted = format!("{value:.12}");
    while formatted.ends_with('0') {
        formatted.pop();
    }
    if formatted.ends_with('.') {
        formatted.pop();
    }
    Some(formatted)
}

struct ScientificParser<'a> {
    input: &'a [u8],
    position: usize,
}

impl<'a> ScientificParser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input: input.as_bytes(),
            position: 0,
        }
    }

    fn parse(mut self) -> Option<f64> {
        let value = self.parse_sum()?;
        self.skip_whitespace();
        (self.position == self.input.len()).then_some(value)
    }

    fn parse_sum(&mut self) -> Option<f64> {
        let mut value = self.parse_product()?;
        loop {
            if self.consume(b'+') {
                value += self.parse_product()?;
            } else if self.consume(b'-') {
                value -= self.parse_product()?;
            } else {
                return Some(value);
            }
        }
    }

    fn parse_product(&mut self) -> Option<f64> {
        let mut value = self.parse_unary()?;
        loop {
            if self.consume(b'*') {
                value *= self.parse_unary()?;
            } else if self.consume(b'/') {
                value /= self.parse_unary()?;
            } else if self.consume(b'%') {
                value %= self.parse_unary()?;
            } else if self.starts_implicit_product() {
                value *= self.parse_unary()?;
            } else {
                return Some(value);
            }
        }
    }

    fn parse_unary(&mut self) -> Option<f64> {
        if self.consume(b'+') {
            self.parse_unary()
        } else if self.consume(b'-') {
            self.parse_unary().map(|value| -value)
        } else {
            self.parse_power()
        }
    }

    fn parse_power(&mut self) -> Option<f64> {
        let value = self.parse_postfix()?;
        if self.consume(b'^') {
            Some(value.powf(self.parse_unary()?))
        } else {
            Some(value)
        }
    }

    fn parse_postfix(&mut self) -> Option<f64> {
        let mut value = self.parse_primary()?;
        while self.consume(b'!') {
            value = factorial(value)?;
        }
        Some(value)
    }

    fn parse_primary(&mut self) -> Option<f64> {
        self.skip_whitespace();
        if self.consume(b'(') {
            let value = self.parse_sum()?;
            return self.consume(b')').then_some(value);
        }
        if self.peek()?.is_ascii_digit() || self.peek()? == b'.' {
            return self.parse_number();
        }
        let name = self.parse_identifier()?.to_ascii_lowercase();
        self.skip_whitespace();
        if self.consume(b'(') {
            let mut arguments = Vec::new();
            if !self.consume(b')') {
                loop {
                    arguments.push(self.parse_sum()?);
                    if self.consume(b')') {
                        break;
                    }
                    if !self.consume(b',') {
                        return None;
                    }
                }
            }
            evaluate_function(&name, &arguments)
        } else {
            match name.as_str() {
                "pi" => Some(std::f64::consts::PI),
                "tau" => Some(std::f64::consts::TAU),
                "e" => Some(std::f64::consts::E),
                "phi" => Some((1.0 + 5.0_f64.sqrt()) / 2.0),
                _ => None,
            }
        }
    }

    fn parse_number(&mut self) -> Option<f64> {
        self.skip_whitespace();
        let start = self.position;
        let mut decimal_seen = false;
        while let Some(byte) = self.input.get(self.position).copied() {
            if byte.is_ascii_digit() {
                self.position += 1;
            } else if byte == b'.' && !decimal_seen {
                decimal_seen = true;
                self.position += 1;
            } else {
                break;
            }
        }
        if matches!(self.input.get(self.position), Some(b'e' | b'E')) {
            let exponent = self.position;
            self.position += 1;
            if matches!(self.input.get(self.position), Some(b'+' | b'-')) {
                self.position += 1;
            }
            let digits = self.position;
            while self
                .input
                .get(self.position)
                .is_some_and(u8::is_ascii_digit)
            {
                self.position += 1;
            }
            if digits == self.position {
                self.position = exponent;
            }
        }
        std::str::from_utf8(&self.input[start..self.position])
            .ok()?
            .parse()
            .ok()
    }

    fn parse_identifier(&mut self) -> Option<String> {
        self.skip_whitespace();
        let start = self.position;
        while self.input.get(self.position).is_some_and(|byte| {
            byte.is_ascii_alphanumeric() || *byte == b'_'
        }) {
            self.position += 1;
        }
        (self.position > start).then(|| {
            String::from_utf8_lossy(&self.input[start..self.position]).into_owned()
        })
    }

    fn starts_implicit_product(&mut self) -> bool {
        self.skip_whitespace();
        self.input
            .get(self.position)
            .is_some_and(|byte| *byte == b'(' || byte.is_ascii_alphabetic())
    }

    fn consume(&mut self, expected: u8) -> bool {
        self.skip_whitespace();
        if self.input.get(self.position) == Some(&expected) {
            self.position += 1;
            true
        } else {
            false
        }
    }

    fn peek(&mut self) -> Option<u8> {
        self.skip_whitespace();
        self.input.get(self.position).copied()
    }

    fn skip_whitespace(&mut self) {
        while self
            .input
            .get(self.position)
            .is_some_and(u8::is_ascii_whitespace)
        {
            self.position += 1;
        }
    }
}

fn factorial(value: f64) -> Option<f64> {
    if value < 0.0 || value.fract() != 0.0 || value > 170.0 {
        return None;
    }
    Some((2..=value as u64).fold(1.0, |result, factor| result * factor as f64))
}

fn evaluate_function(name: &str, arguments: &[f64]) -> Option<f64> {
    let one = || arguments.first().copied().filter(|_| arguments.len() == 1);
    let two = || (arguments.len() == 2).then(|| (arguments[0], arguments[1]));
    match name {
        "sqrt" => one().map(f64::sqrt),
        "cbrt" => one().map(f64::cbrt),
        "abs" => one().map(f64::abs),
        "sin" => one().map(f64::sin),
        "cos" => one().map(f64::cos),
        "tan" => one().map(f64::tan),
        "asin" => one().map(f64::asin),
        "acos" => one().map(f64::acos),
        "atan" => one().map(f64::atan),
        "sinh" => one().map(f64::sinh),
        "cosh" => one().map(f64::cosh),
        "tanh" => one().map(f64::tanh),
        "asinh" => one().map(f64::asinh),
        "acosh" => one().map(f64::acosh),
        "atanh" => one().map(f64::atanh),
        "sind" => one().map(|value| value.to_radians().sin()),
        "cosd" => one().map(|value| value.to_radians().cos()),
        "tand" => one().map(|value| value.to_radians().tan()),
        "ln" => one().map(f64::ln),
        "log" | "log10" => match arguments {
            [value] => Some(value.log10()),
            [value, base] => Some(value.log(*base)),
            _ => None,
        },
        "log2" => one().map(f64::log2),
        "exp" => one().map(f64::exp),
        "exp2" => one().map(f64::exp2),
        "floor" => one().map(f64::floor),
        "ceil" => one().map(f64::ceil),
        "round" => match arguments {
            [value] => Some(value.round()),
            [value, places] if places.fract() == 0.0 => {
                let scale = 10.0_f64.powf(*places);
                Some((value * scale).round() / scale)
            }
            _ => None,
        },
        "trunc" => one().map(f64::trunc),
        "fract" => one().map(f64::fract),
        "sign" | "signum" => one().map(f64::signum),
        "deg" | "degrees" => one().map(f64::to_degrees),
        "rad" | "radians" => one().map(f64::to_radians),
        "inv" | "reciprocal" => one().map(|value| value.recip()),
        "fact" | "factorial" => factorial(one()?),
        "pow" => two().map(|(value, power)| value.powf(power)),
        "root" => two().map(|(value, root)| value.powf(1.0 / root)),
        "hypot" => two().map(|(left, right)| left.hypot(right)),
        "atan2" => two().map(|(y, x)| y.atan2(x)),
        "min" => arguments.iter().copied().reduce(f64::min),
        "max" => arguments.iter().copied().reduce(f64::max),
        "ncr" => two().and_then(|(n, r)| combinations(n, r)),
        "npr" => two().and_then(|(n, r)| permutations(n, r)),
        _ => None,
    }
}

fn permutations(n: f64, r: f64) -> Option<f64> {
    if n < 0.0 || r < 0.0 || n.fract() != 0.0 || r.fract() != 0.0 || r > n || n > 170.0 {
        return None;
    }
    Some(((n - r + 1.0) as u64..=n as u64).fold(1.0, |value, item| value * item as f64))
}

fn combinations(n: f64, r: f64) -> Option<f64> {
    let r = r.min(n - r);
    let permutations = permutations(n, r)?;
    Some(permutations / factorial(r)?)
}

impl App for OverbarApp {
    fn update(&mut self, ctx: &Context, _frame: &mut eframe::Frame) {
        if self.startup_search_warmup_stage == 0 {
            self.search_active = true;
            self.search_panel_closing = false;
            self.search_panel_animation_started = Instant::now();
            self.search_focus_pending = true;
            self.search_focus_attempts = 0;
            self.startup_search_warmup_stage = 1;
            self.startup_search_warmup_started = Instant::now();
            ctx.request_repaint();
        } else if self.startup_search_warmup_stage == 1
            && self.startup_search_warmup_started.elapsed() >= Duration::from_millis(120)
        {
            self.search_active = false;
            self.search_panel_closing = true;
            self.search_panel_animation_started = Instant::now();
            self.search_focus_pending = false;
            self.search_focus_attempts = 0;
            set_search_keyboard_focus(false, false);
            self.startup_search_warmup_stage = 2;
            ctx.request_repaint();
        }

        while let Ok(result) = self.startup_task_updates.try_recv() {
            self.startup_task_in_progress = false;
            self.startup_task_status = Some(match result {
                Ok(path) => (
                    true,
                    format!("Startup task now points to {}", path.display()),
                ),
                Err(error) => (false, error),
            });
        }
        while let Ok(event) = self.update_events.try_recv() {
            match event {
                UpdateEvent::CheckFinished(Ok(update)) => {
                    if let Some(update) = &update {
                        record_startup_event(&format!(
                            "update {} is available",
                            update.version
                        ));
                    }
                    let changed = match (&self.available_update, &update) {
                        (Some(previous), Some(next)) => previous.version != next.version,
                        (None, Some(_)) | (Some(_), None) => true,
                        (None, None) => false,
                    };
                    if changed {
                        self.update_error = None;
                        self.update_error_copied_at = None;
                        self.update_notice_seen_in_menu = false;
                        self.update_notice = if self.apps_panel_open {
                            None
                        } else {
                            update.as_ref().map(|_| UpdateNotice::Available)
                        };
                    }
                    self.available_update = update;
                }
                UpdateEvent::CheckFinished(Err(error)) => {
                    // A failed background check should never interrupt the bar.
                    record_startup_event(&format!("update check failed: {error}"));
                }
                UpdateEvent::ReadyToRestart => {
                    self.runtime_running.store(false, Ordering::Release);
                    ctx.send_viewport_cmd(ViewportCommand::Close);
                }
                UpdateEvent::InstallFailed(error) => {
                    self.update_in_progress = false;
                    self.update_error = Some(error);
                    self.update_error_copied_at = None;
                    self.update_notice = if self.apps_panel_open {
                        None
                    } else {
                        Some(UpdateNotice::Failed)
                    };
                    self.update_notice_seen_in_menu = false;
                }
            }
            ctx.request_repaint();
        }
        // eframe sizes are in DPI-independent points; the monitor width supplied here is too.
        let monitor_size = ctx.input(|input| input.viewport().monitor_size);
        if let Some(monitor_size) = monitor_size {
            let requested_size = Vec2::new(monitor_size.x, BAR_HEIGHT);
            if self.last_bar_monitor_size.is_none_or(|size| {
                (size.x - requested_size.x).abs() > 0.5
                    || (size.y - requested_size.y).abs() > 0.5
            }) {
                ctx.send_viewport_cmd(ViewportCommand::InnerSize(requested_size));
                self.last_bar_monitor_size = Some(requested_size);
                self.last_bar_position_y = None;
            }
        }
        let bar_slide_elapsed = self.bar_slide_started.elapsed().as_secs_f32();
        let bar_slide_progress =
            ease_out_cubic((bar_slide_elapsed / BAR_SLIDE_SECONDS).clamp(0.0, 1.0));
        let bar_slide_current =
            self.bar_slide_from + (self.bar_slide_to - self.bar_slide_from) * bar_slide_progress;
        let bar_position_y = -BAR_HEIGHT * bar_slide_current;
        if self
            .last_bar_position_y
            .is_none_or(|y| (y - bar_position_y).abs() > 0.5)
        {
            ctx.send_viewport_cmd(ViewportCommand::OuterPosition([0.0, bar_position_y].into()));
            self.last_bar_position_y = Some(bar_position_y);
        }
        if bar_slide_progress < 1.0 {
            ctx.request_repaint();
        }

        while let Ok(update) = self.window_manager_updates.try_recv() {
            match update {
                WindowManagerUpdate::Workspaces(workspaces) => {
                    let previous_active = self
                        .workspaces
                        .items
                        .get(self.workspaces.active)
                        .map(|workspace| workspace.name.as_str());
                    let next_active = workspaces
                        .items
                        .get(workspaces.active)
                        .map(|workspace| workspace.name.as_str());
                    if self.search_active && previous_active != next_active {
                        self.search_focus_pending = true;
                        self.search_focus_attempts = 0;
                    }
                    self.workspaces = workspaces;
                    refresh_windows_bar_blur();
                    ctx.request_repaint();
                }
                WindowManagerUpdate::TilingDirection(direction) if direction != self.direction => {
                    let now = Instant::now();
                    let elapsed = now
                        .duration_since(self.direction_angle_started)
                        .as_secs_f32()
                        / DIRECTION_TURN_SECONDS;
                    let progress = smootherstep(elapsed.clamp(0.0, 1.0));
                    let current = self.direction_angle_from
                        + (self.direction_angle_to - self.direction_angle_from) * progress;
                    self.direction = direction;
                    self.direction_angle_from = current;
                    self.direction_angle_to = match direction {
                        TilingDirection::Horizontal => 0.0,
                        TilingDirection::Vertical => std::f32::consts::FRAC_PI_2,
                    };
                    self.direction_angle_started = now;
                }
                WindowManagerUpdate::TilingDirection(_) => {}
                WindowManagerUpdate::Floating(floating) => {
                    self.focused_floating = floating;
                    ctx.request_repaint();
                }
                WindowManagerUpdate::ResizeMode(active) => {
                    self.resize_mode_active = active;
                    ctx.request_repaint();
                }
                WindowManagerUpdate::LayoutChanged => {
                    refresh_windows_bar_blur();
                    ctx.request_repaint();
                }
                WindowManagerUpdate::ConfigChanged(config) => {
                    self.wm_config = config;
                    save_wm_config(&self.wm_config);
                }
                WindowManagerUpdate::BarVisibility(hidden) => {
                    if self.bar_auto_hidden != hidden {
                        let elapsed = self.bar_slide_started.elapsed().as_secs_f32();
                        let progress =
                            ease_out_cubic((elapsed / BAR_SLIDE_SECONDS).clamp(0.0, 1.0));
                        let current = self.bar_slide_from
                            + (self.bar_slide_to - self.bar_slide_from) * progress;
                        self.bar_slide_from = current;
                        self.bar_slide_to = if hidden { 1.0 } else { 0.0 };
                        self.bar_slide_started = Instant::now();
                        self.bar_auto_hidden = hidden;
                    }
                    ctx.request_repaint();
                }
            }
        }
        while let Ok(title) = self.title_updates.try_recv() {
            self.active_title = title;
        }
        while self.search_shortcuts.try_recv().is_ok() {
            self.activate_search(ctx);
        }
        while let Ok(results) = self.search_updates.try_recv() {
            if results.query == self.search_query {
                if results.query.is_empty() {
                    self.search_home = results.clone();
                } else {
                    self.search_cached_queries
                        .insert(results.query.trim().to_ascii_lowercase(), results.clone());
                }
                self.search_results = results;
                let count = self.search_result_count();
                self.search_selected = self.search_selected.min(count.saturating_sub(1));
            }
        }
        while let Ok((path, image)) = self.search_icon_updates.try_recv() {
            self.search_icon_pending.remove(&path);
            if let Some(image) = image {
                let texture = ctx.load_texture(
                    format!("search-icon:{}", path.display()),
                    image,
                    TextureOptions::LINEAR,
                );
                self.search_icons.insert(path, texture);
            } else {
                self.search_icon_failed.insert(path);
            }
        }

        while let Ok(temperature) = self.temperature_updates.try_recv() {
            self.cpu_temperature = temperature;
        }
        while let Ok(audio) = self.audio_updates.try_recv() {
            // Keep the drag optimistic while the pointer is down; otherwise follow
            // external volume changes from media keys and Windows controls.
            if !ctx.input(|input| input.pointer.any_down()) {
                self.volume = audio.volume;
            }
            self.volume_muted = audio.muted;
        }
        while let Ok(mut media) = self.media_updates.try_recv() {
            if let Some(next) = media.as_ref()
                && self.media.as_ref().map(|current| current.playing) != Some(next.playing)
            {
                self.animate_media_icon_to(next.playing);
            }
            let raw_position = media.as_ref().map(|state| state.position_seconds);
            if let (Some(previous), Some(next)) = (self.media.as_ref(), media.as_mut())
                && previous.playing
                && next.playing
                && self
                    .media_raw_position
                    .is_some_and(|position| (next.position_seconds - position).abs() < 0.01)
            {
                // Some providers publish timeline anchors only once per second.
                // Preserve interpolation between equal anchors so frequent state
                // polling cannot make the progress line appear stationary.
                next.position_seconds = (previous.position_seconds
                    + self.media_updated_at.elapsed().as_secs_f64())
                    .min(next.duration_seconds.max(0.0));
            }
            self.media = media;
            self.media_raw_position = raw_position;
            self.media_updated_at = Instant::now();
            ctx.request_repaint();
        }

        if self.last_metrics_refresh.elapsed() >= Duration::from_secs(1) {
            self.refresh_metrics();
            self.last_metrics_refresh = Instant::now();
        }

        if self.search_panel_closing
            && self.search_panel_animation_started.elapsed()
                >= Duration::from_secs_f32(SEARCH_PANEL_CLOSE_SECONDS)
        {
            self.search_panel_closing = false;
            self.search_query.clear();
            self.search_results = SearchResults::default();
        }

        let empty_workspace = self.active_workspace_is_empty();
        if self.search_active
            && !self.search_focus_pending
            && !search_keyboard_focus_is_active()
        {
            self.search_focus_pending = true;
        }
        if empty_workspace != self.search_last_empty {
            self.search_last_empty = empty_workspace;
            self.search_text_transition_started = Instant::now();
        }
        let search_text_progress = ease_out_cubic(
            (self.search_text_transition_started.elapsed().as_secs_f32() / 0.18)
                .clamp(0.0, 1.0),
        );
        let display_title = ellipsize_title(&self.active_title, 36);
        CentralPanel::default()
            .frame(
                Frame::new()
                    .fill(BAR_BACKGROUND)
                    .inner_margin(Margin::ZERO),
            )
            .show(ctx, |ui| {
                let rect = ui.max_rect();
                let bar_rect = eframe::egui::Rect::from_min_size(
                    rect.min,
                    Vec2::new(rect.width(), BAR_HEIGHT),
                );

                ui.scope_builder(
                    UiBuilder::new()
                        .max_rect(eframe::egui::Rect::from_min_max(
                            bar_rect.min,
                            eframe::egui::pos2(
                                (bar_rect.center().x - 130.0).max(300.0),
                                bar_rect.max.y,
                            ),
                        ))
                        .layout(Layout::left_to_right(Align::Center)),
                    |ui| self.draw_left(ui),
                );

                let title_rect = eframe::egui::Rect::from_center_size(
                    bar_rect.center(),
                    Vec2::new(430.0, BAR_HEIGHT),
                );
                self.search_trigger_rect = title_rect;
                if self.search_active {
                    let editor_height = ui
                        .painter()
                        .layout_no_wrap(
                            "Ag".to_owned(),
                            FontId::monospace(BAR_FONT_SIZE),
                            TEXT_PRIMARY,
                        )
                        .size()
                        .y;
                    let editor_rect = eframe::egui::Rect::from_center_size(
                        title_rect.center(),
                        Vec2::new(title_rect.width() - 36.0, editor_height),
                    );
                    let response = ui
                        .scope(|ui| {
                            ui.visuals_mut().text_cursor.stroke.color = self.accent_color;
                            ui.visuals_mut().selection.bg_fill =
                                Color32::from_rgba_unmultiplied(
                                    self.accent_color.r(),
                                    self.accent_color.g(),
                                    self.accent_color.b(),
                                    80,
                                );
                            ui.put(
                                editor_rect,
                                TextEdit::singleline(&mut self.search_query)
                                    .id(ui.id().with("overbar-search-editor"))
                                    .font(FontId::monospace(BAR_FONT_SIZE))
                                    .text_color(TEXT_PRIMARY)
                                    .hint_text(
                                        RichText::new("Type here to search...")
                                            .font(FontId::monospace(BAR_FONT_SIZE))
                                            .color(STAT_LABEL),
                                    )
                                    .horizontal_align(Align::Center)
                                    .margin(Margin::ZERO)
                                    .frame(false)
                                    .desired_width(editor_rect.width()),
                            )
                        })
                        .inner;
                    let widget_focused = response.has_focus();
                    if self.search_focus_pending || !widget_focused {
                        response.request_focus();
                        if !widget_focused {
                            ctx.request_repaint_after(Duration::from_millis(16));
                        }
                    }
                    if self.search_focus_pending {
                        self.search_focus_attempts = self.search_focus_attempts.saturating_add(1);
                        let native_focused = set_search_keyboard_focus(true, false);
                        let fully_focused = native_focused && response.has_focus();
                        self.search_focus_pending = !fully_focused;
                        if self.search_focus_pending {
                            ctx.request_repaint_after(Duration::from_millis(16));
                        } else {
                            self.search_focus_attempts = 0;
                        }
                    }
                    if response.changed() {
                        self.search_query_changed();
                    }
                } else if self.search_panel_closing {
                    let (text, color) = if self.search_query.is_empty() {
                        ("Type here to search...", STAT_LABEL)
                    } else {
                        (self.search_query.as_str(), TEXT_PRIMARY)
                    };
                    ui.painter().text(
                        title_rect.center(),
                        eframe::egui::Align2::CENTER_CENTER,
                        text,
                        FontId::monospace(BAR_FONT_SIZE),
                        color,
                    );
                } else {
                    let response = ui
                        .interact(title_rect, ui.id().with("focused-window-title"), Sense::click())
                        .on_hover_cursor(CursorIcon::PointingHand);
                    let hover_hint = ui.ctx().animate_bool_with_time(
                        ui.id().with("focused-window-search-hover"),
                        response.hovered(),
                        0.14,
                    );
                    let shell_search_fallback = self.active_title == "Type here to search...";
                    let hint_mix = if empty_workspace || shell_search_fallback {
                        1.0
                    } else {
                        hover_hint
                    };
                    if hint_mix < 1.0 {
                        let title_color = TEXT_PRIMARY
                            .gamma_multiply((1.0 - hint_mix) * search_text_progress);
                        for offset in [-0.25_f32, 0.25] {
                            ui.painter().text(
                                title_rect.center() + Vec2::new(offset, 0.0),
                                eframe::egui::Align2::CENTER_CENTER,
                                &display_title,
                                FontId::monospace(BAR_FONT_SIZE),
                                title_color,
                            );
                        }
                    }
                    if hint_mix > 0.0 {
                        ui.painter().text(
                            title_rect.center(),
                            eframe::egui::Align2::CENTER_CENTER,
                            "Type here to search...",
                            FontId::monospace(BAR_FONT_SIZE),
                            STAT_LABEL.gamma_multiply(hint_mix * search_text_progress),
                        );
                    }
                    if response.clicked() {
                        self.activate_search(ctx);
                    }
                }

                ui.scope_builder(
                    UiBuilder::new()
                        .max_rect(eframe::egui::Rect::from_min_max(
                            eframe::egui::pos2(
                                (bar_rect.center().x + 130.0).min(bar_rect.max.x),
                                bar_rect.min.y,
                            ),
                            bar_rect.max,
                        ))
                        .layout(Layout::right_to_left(Align::Center)),
                    |ui| self.draw_right(ui),
                );

                let monitor_size = monitor_size.unwrap_or(Vec2::new(bar_rect.width(), 720.0));
                let monitor_width = monitor_size.x;
                self.draw_panel(ctx, monitor_width);
                self.draw_power_panel(ctx, monitor_size);
                self.draw_apps_panel(ctx, monitor_width);
                self.draw_wm_settings_panel(ctx);
                self.draw_search_panel(ctx, monitor_width);
            });

        // A newly-created or elevated application can enter the topmost band.
        // When the full-screen power overlay is visible, temporarily move the
        // bar out of that band so the scrim can cover it cleanly.
        set_windows_overlay_topmost(
            "Overbar",
            !self.power_panel_open && !self.power_panel_closing,
        );

        let escape_pressed = ctx.input(|input| input.key_pressed(eframe::egui::Key::Escape));
        if self.panel_open
            && (escape_pressed
                || overlay_dismiss_requested(
                    "Overbar System Panel",
                    self.stats_pill_rect,
                    ctx.pixels_per_point(),
                ))
        {
            self.panel_open = false;
            ctx.request_repaint();
        }
        if self.apps_panel_open
            && !self.wm_settings_open
            && (escape_pressed
                || overlay_dismiss_requested(
                    "Overbar Apps Panel",
                    self.apps_icon_rect,
                    ctx.pixels_per_point(),
                ))
        {
            self.apps_panel_open = false;
            ctx.request_repaint();
        }
        if self.power_panel_open
            && self.scheduled_power_action.is_none()
            && (escape_pressed
                || overlay_dismiss_requested(
                    "Overbar Power Menu",
                    self.power_button_rect,
                    ctx.pixels_per_point(),
                ))
        {
            self.pending_power_action = None;
            self.begin_power_panel_close();
            ctx.request_repaint();
        }
        if self.wm_settings_open
            && (escape_pressed
                || overlay_dismiss_requested(
                    "Overbar WM Settings",
                    eframe::egui::Rect::from_min_size(
                        eframe::egui::pos2(-10_000.0, -10_000.0),
                        Vec2::ZERO,
                    ),
                    ctx.pixels_per_point(),
                ))
        {
            self.wm_settings_open = false;
            self.wm_settings_closing = false;
            self.apps_panel_open = false;
            reset_windows_wm_settings_overlay();
            ctx.request_repaint();
        }
        if self.search_active
            && overlay_dismiss_requested(
                "Overbar Search Panel",
                self.search_trigger_rect,
                ctx.pixels_per_point(),
            )
        {
            self.finish_search(ctx, false);
        }

        if self.apps_panel_open {
            if self.update_notice.is_some() {
                self.update_notice_seen_in_menu = true;
            }
            if self.completed_update.is_some() {
                self.completed_update_seen_in_menu = true;
            }
        } else {
            let mut notification_changed = false;
            if self.completed_update_seen_in_menu {
                self.completed_update_seen_in_menu = false;
                self.completed_update = None;
                clear_completed_update_marker();
                if self.update_notice == Some(UpdateNotice::Complete) {
                    self.update_notice = None;
                    self.update_notice_seen_in_menu = false;
                }
                notification_changed = true;
            }
            if self.update_notice_seen_in_menu {
                // Keep a badge visible for the entire first visit, then mark
                // that independent update/failure notification as read.
                self.update_notice_seen_in_menu = false;
                self.update_notice = None;
                notification_changed = true;
            }
            if notification_changed {
                ctx.request_repaint();
            }
        }

        ctx.request_repaint_after(if self.panel_open
            || self.apps_panel_open
            || self.power_panel_open
            || self.power_panel_closing
            || self.wm_settings_open
            || self.search_active
            || self.search_panel_closing
        {
            Duration::from_millis(16)
        } else {
            Duration::from_secs(1)
        });
    }

    fn clear_color(&self, _visuals: &eframe::egui::Visuals) -> [f32; 4] {
        [0.0, 0.0, 0.0, 0.0]
    }
}

impl Drop for OverbarApp {
    fn drop(&mut self) {
        self.runtime_running.store(false, Ordering::Release);
    }
}

#[cfg(target_os = "windows")]
fn continue_in_elevated_process() -> bool {
    use std::os::windows::ffi::OsStrExt;
    use windows::{
        Win32::{
            Foundation::{CloseHandle, HANDLE},
            Security::{GetTokenInformation, TOKEN_ELEVATION, TOKEN_QUERY, TokenElevation},
            System::Threading::{
                GetCurrentProcess, INFINITE, OpenProcessToken, WaitForSingleObject,
            },
            UI::{
                Shell::{
                    SEE_MASK_NOCLOSEPROCESS, SHELLEXECUTEINFOW, ShellExecuteExW,
                },
                WindowsAndMessaging::SW_SHOWNORMAL,
            },
        },
        core::PCWSTR,
    };

    let mut token = HANDLE::default();
    let elevated = unsafe {
        if OpenProcessToken(GetCurrentProcess(), TOKEN_QUERY, &mut token).is_err() {
            false
        } else {
            let mut elevation = TOKEN_ELEVATION::default();
            let mut returned = 0_u32;
            let result = GetTokenInformation(
                token,
                TokenElevation,
                Some((&mut elevation as *mut TOKEN_ELEVATION).cast()),
                std::mem::size_of::<TOKEN_ELEVATION>() as u32,
                &mut returned,
            )
            .is_ok();
            let _ = CloseHandle(token);
            result && elevation.TokenIsElevated != 0
        }
    };
    if elevated
        || env::args_os().any(|argument| argument == "--overbar-elevated")
    {
        return true;
    }

    let Ok(executable) = env::current_exe() else {
        return true;
    };
    let executable = executable
        .as_os_str()
        .encode_wide()
        .chain(std::iter::once(0))
        .collect::<Vec<_>>();
    let parameters = "--overbar-elevated"
        .encode_utf16()
        .chain(std::iter::once(0))
        .collect::<Vec<_>>();
    let working_directory = env::current_exe()
        .ok()
        .and_then(|path| path.parent().map(Path::to_path_buf))
        .map(|path| {
            path.as_os_str()
                .encode_wide()
                .chain(std::iter::once(0))
                .collect::<Vec<_>>()
        });
    let mut launch = SHELLEXECUTEINFOW {
        cbSize: std::mem::size_of::<SHELLEXECUTEINFOW>() as u32,
        fMask: SEE_MASK_NOCLOSEPROCESS,
        lpVerb: windows::core::w!("runas"),
        lpFile: PCWSTR(executable.as_ptr()),
        lpParameters: PCWSTR(parameters.as_ptr()),
        lpDirectory: working_directory
            .as_ref()
            .map_or(PCWSTR::null(), |directory| PCWSTR(directory.as_ptr())),
        nShow: SW_SHOWNORMAL.0,
        ..Default::default()
    };
    if unsafe { ShellExecuteExW(&mut launch) }.is_err() {
        // If elevation was declined or unavailable, keep this instance usable.
        return true;
    }
    if !launch.hProcess.is_invalid() {
        unsafe {
            // Keep `cargo run` attached to Overbar instead of letting Cargo tear
            // down the detached elevated child when the bootstrapper exits.
            let _ = WaitForSingleObject(launch.hProcess, INFINITE);
            let _ = CloseHandle(launch.hProcess);
        }
    }
    false
}

#[cfg(not(target_os = "windows"))]
fn continue_in_elevated_process() -> bool {
    true
}

fn record_startup_event(message: &str) {
    let Some(base) = env::var_os("LOCALAPPDATA").or_else(|| env::var_os("APPDATA")) else {
        return;
    };
    let directory = PathBuf::from(base).join("Overbar");
    if fs::create_dir_all(&directory).is_err() {
        return;
    }
    let Ok(mut log) = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(directory.join("startup.log"))
    else {
        return;
    };
    let _ = writeln!(
        log,
        "{} {message}",
        Local::now().format("%Y-%m-%d %H:%M:%S")
    );
}

fn main() -> eframe::Result {
    if !continue_in_elevated_process() {
        return Ok(());
    }
    record_startup_event("starting Overbar UI");
    let native_options = NativeOptions {
        viewport: eframe::egui::ViewportBuilder::default()
            .with_title("Overbar")
            .with_inner_size([1920.0, BAR_HEIGHT])
            .with_min_inner_size([320.0, BAR_HEIGHT])
            .with_max_inner_size([10000.0, BAR_HEIGHT])
            .with_position([0.0, 0.0])
            .with_transparent(true)
            .with_decorations(false)
            .with_resizable(false)
            .with_taskbar(false)
            .with_active(false)
            .with_window_level(WindowLevel::AlwaysOnTop),
        ..Default::default()
    };

    let result = eframe::run_native(
        "Overbar",
        native_options,
        Box::new(|cc| Ok(Box::new(OverbarApp::new(cc)))),
    );
    match &result {
        Ok(()) => record_startup_event("Overbar UI exited normally"),
        Err(error) => record_startup_event(&format!("Overbar UI failed: {error}")),
    }
    result
}

#[cfg(target_os = "windows")]
fn spawn_audio_worker(
    ctx: Context,
    running: Arc<AtomicBool>,
) -> (Sender<AudioCommand>, Receiver<AudioState>) {
    use windows::Win32::{
        Foundation::BOOL,
        Media::Audio::{
            Endpoints::IAudioEndpointVolume, IMMDeviceEnumerator, MMDeviceEnumerator, eMultimedia,
            eRender,
        },
        System::Com::{
            CLSCTX_ALL, COINIT_MULTITHREADED, CoCreateInstance, CoInitializeEx, CoUninitialize,
        },
    };

    let (command_sender, command_receiver) = mpsc::channel();
    let (state_sender, state_receiver) = mpsc::channel();
    let _ = thread::Builder::new()
        .name("windows-volume-monitor".into())
        .spawn(move || unsafe {
            if CoInitializeEx(None, COINIT_MULTITHREADED).is_err() {
                return;
            }

            let endpoint = (|| -> windows::core::Result<IAudioEndpointVolume> {
                let enumerator: IMMDeviceEnumerator =
                    CoCreateInstance(&MMDeviceEnumerator, None, CLSCTX_ALL)?;
                let device = enumerator.GetDefaultAudioEndpoint(eRender, eMultimedia)?;
                device.Activate(CLSCTX_ALL, None)
            })();

            let Ok(endpoint) = endpoint else {
                CoUninitialize();
                return;
            };

            while running.load(Ordering::Acquire) {
                match command_receiver.recv_timeout(Duration::from_millis(50)) {
                    Ok(AudioCommand::SetVolume(volume)) => {
                        let _ = endpoint.SetMasterVolumeLevelScalar(
                            volume.clamp(0.0, 1.0),
                            std::ptr::null(),
                        );
                        let _ = endpoint.SetMute(BOOL(0), std::ptr::null());
                        while let Ok(AudioCommand::SetVolume(volume)) = command_receiver.try_recv() {
                            let _ = endpoint.SetMasterVolumeLevelScalar(
                                volume.clamp(0.0, 1.0),
                                std::ptr::null(),
                            );
                        }
                    }
                    Err(mpsc::RecvTimeoutError::Timeout) => {}
                    Err(mpsc::RecvTimeoutError::Disconnected) => break,
                }

                let state = endpoint
                    .GetMasterVolumeLevelScalar()
                    .and_then(|volume| {
                        endpoint.GetMute().map(|muted| AudioState {
                            volume: volume.clamp(0.0, 1.0),
                            muted: muted.as_bool(),
                        })
                    });
                if let Ok(state) = state {
                    if state_sender.send(state).is_err() {
                        break;
                    }
                    ctx.request_repaint();
                }
            }

            CoUninitialize();
        });

    (command_sender, state_receiver)
}

#[cfg(not(target_os = "windows"))]
fn spawn_audio_worker(
    _ctx: Context,
    _running: Arc<AtomicBool>,
) -> (Sender<AudioCommand>, Receiver<AudioState>) {
    let (command_sender, _command_receiver) = mpsc::channel();
    let (_state_sender, state_receiver) = mpsc::channel();
    (command_sender, state_receiver)
}

#[cfg(target_os = "windows")]
fn spawn_media_worker(
    ctx: Context,
    running: Arc<AtomicBool>,
) -> (Sender<MediaCommand>, Receiver<Option<MediaState>>) {
    use windows::{
        Media::Control::{
            GlobalSystemMediaTransportControlsSessionManager,
            GlobalSystemMediaTransportControlsSessionPlaybackStatus,
        },
        Win32::System::WinRT::{RO_INIT_MULTITHREADED, RoInitialize, RoUninitialize},
    };

    let (command_sender, command_receiver) = mpsc::channel::<MediaCommand>();
    let (state_sender, state_receiver) = mpsc::channel::<Option<MediaState>>();
    let _ = thread::Builder::new()
        .name("windows-media-session-monitor".into())
        .spawn(move || unsafe {
            if RoInitialize(RO_INIT_MULTITHREADED).is_err() {
                return;
            }
            let manager = GlobalSystemMediaTransportControlsSessionManager::RequestAsync()
                .and_then(|operation| operation.get());
            let Ok(manager) = manager else {
                RoUninitialize();
                return;
            };

            let mut metadata_source = String::new();
            let mut metadata_title = String::new();
            let mut metadata_artist = String::new();
            let mut metadata_refreshed = Instant::now() - Duration::from_secs(10);
            let mut was_visible = false;

            while running.load(Ordering::Acquire) {
                match command_receiver.recv_timeout(Duration::from_millis(75)) {
                    Ok(MediaCommand::TogglePlayPause) => {
                        if let Ok(session) = manager.GetCurrentSession()
                            && let Ok(operation) = session.TryTogglePlayPauseAsync()
                        {
                            let _ = operation.get();
                        }
                    }
                    Err(mpsc::RecvTimeoutError::Timeout) => {}
                    Err(mpsc::RecvTimeoutError::Disconnected) => break,
                }

                let state = (|| -> windows::core::Result<Option<MediaState>> {
                    let session = manager.GetCurrentSession()?;
                    let playback = session.GetPlaybackInfo()?;
                    let status = playback.PlaybackStatus()?;
                    if status != GlobalSystemMediaTransportControlsSessionPlaybackStatus::Playing
                        && status
                            != GlobalSystemMediaTransportControlsSessionPlaybackStatus::Paused
                    {
                        return Ok(None);
                    }

                    let source = session.SourceAppUserModelId()?.to_string();
                    if source != metadata_source
                        || metadata_refreshed.elapsed() >= Duration::from_secs(1)
                    {
                        if let Ok(properties) = session
                            .TryGetMediaPropertiesAsync()
                            .and_then(|operation| operation.get())
                        {
                            metadata_title = properties.Title()?.to_string();
                            metadata_artist = properties.Artist()?.to_string();
                            metadata_source = source.clone();
                            metadata_refreshed = Instant::now();
                        }
                    }
                    if metadata_title.trim().is_empty() {
                        metadata_title = source
                            .rsplit(['!', '.'])
                            .find(|part| !part.trim().is_empty())
                            .unwrap_or("Media")
                            .to_owned();
                    }

                    let timeline = session.GetTimelineProperties()?;
                    let start = timeline.StartTime()?.Duration as f64 / 10_000_000.0;
                    let end = timeline.EndTime()?.Duration as f64 / 10_000_000.0;
                    let position = timeline.Position()?.Duration as f64 / 10_000_000.0;
                    Ok(Some(MediaState {
                        title: metadata_title.clone(),
                        artist: metadata_artist.clone(),
                        playing: status
                            == GlobalSystemMediaTransportControlsSessionPlaybackStatus::Playing,
                        position_seconds: (position - start).max(0.0),
                        duration_seconds: (end - start).max(0.0),
                    }))
                })()
                .unwrap_or(None);

                if state.is_some() || was_visible {
                    was_visible = state.is_some();
                    if state_sender.send(state).is_err() {
                        break;
                    }
                    ctx.request_repaint();
                }
            }
            RoUninitialize();
        });

    (command_sender, state_receiver)
}

#[cfg(not(target_os = "windows"))]
fn spawn_media_worker(
    _ctx: Context,
    _running: Arc<AtomicBool>,
) -> (Sender<MediaCommand>, Receiver<Option<MediaState>>) {
    let (command_sender, _command_receiver) = mpsc::channel();
    let (_state_sender, state_receiver) = mpsc::channel();
    (command_sender, state_receiver)
}

fn spawn_temperature_worker(
    ctx: Context,
    running: Arc<AtomicBool>,
) -> Receiver<Option<f32>> {
    let (sender, receiver) = mpsc::channel();
    let _ = thread::Builder::new()
        .name("cpu-temperature-monitor".into())
        .spawn(move || {
            // Windows obtains this through WMI, which can occasionally block.
            // Keep all sensor access away from the render thread.
            let mut components = Components::new_with_refreshed_list();
            let mut retry_empty_list_in = 0_u8;

            while running.load(Ordering::Acquire) {
                if components.list().is_empty() {
                    if retry_empty_list_in == 0 {
                        components.refresh_list();
                        retry_empty_list_in = 30;
                    } else {
                        retry_empty_list_in -= 1;
                    }
                } else {
                    components.refresh();
                }

                let temperature = components
                    .list()
                    .iter()
                    .map(|component| component.temperature())
                    .filter(|temperature| {
                        temperature.is_finite() && (0.0..=130.0).contains(temperature)
                    })
                    .max_by(f32::total_cmp);

                if sender.send(temperature).is_err() {
                    return;
                }
                ctx.request_repaint();

                // Sleep in short slices so shutdown never waits a full refresh interval.
                for _ in 0..10 {
                    if !running.load(Ordering::Acquire) {
                        return;
                    }
                    thread::sleep(Duration::from_millis(100));
                }
            }
        });
    receiver
}

fn spawn_search_worker(ctx: Context) -> (Sender<SearchWorkerRequest>, Receiver<SearchResults>) {
    let (request_sender, request_receiver) = mpsc::channel::<SearchWorkerRequest>();
    let (result_sender, result_receiver) = mpsc::channel::<SearchResults>();
    let (cache_sender, cache_receiver) = mpsc::sync_channel::<StoredSearchIndex>(1);
    let (preferences_sender, preferences_receiver) =
        mpsc::channel::<StoredSearchPreferences>();
    let _ = thread::Builder::new()
        .name("overbar-search-cache".into())
        .spawn(move || {
            while let Ok(index) = cache_receiver.recv() {
                save_search_index(&index);
            }
        });
    let _ = thread::Builder::new()
        .name("overbar-search-preferences".into())
        .spawn(move || {
            while let Ok(preferences) = preferences_receiver.recv() {
                save_search_preferences(&preferences);
            }
        });
    let _ = thread::Builder::new()
        .name("overbar-search-index".into())
        .spawn(move || {
            let mut preferences = load_search_preferences();
            let cached = load_search_index().unwrap_or(StoredSearchIndex {
                version: SEARCH_INDEX_VERSION,
                apps: Vec::new(),
                files: Vec::new(),
            });
            let mut apps = cached.apps;
            let mut files = cached.files;
            let start_apps = discover_start_menu_apps();
            merge_search_entries(&mut apps, start_apps.iter().cloned());
            let mut pinned_apps = preferences.pins.clone();
            let mut live_app_paths = apps
                .iter()
                .map(|app| app.path.clone())
                .collect::<HashSet<_>>();
            let mut live_file_paths = files
                .iter()
                .map(|file| file.path.clone())
                .collect::<HashSet<_>>();

            let mut scanned_apps = start_apps;
            let mut scanned_files = Vec::new();
            let mut scanned_app_paths = scanned_apps
                .iter()
                .map(|app| app.path.clone())
                .collect::<HashSet<_>>();
            let mut scanned_file_paths = HashSet::new();
            let mut directories = search_file_roots();
            let mut indexed_directories = directories.iter().cloned().collect::<HashSet<_>>();
            let mut scan_active = true;
            let mut refresh_at = Instant::now() + SEARCH_INDEX_REFRESH_INTERVAL;
            let mut checkpoint_at = Instant::now() + SEARCH_INDEX_CHECKPOINT_INTERVAL;
            let mut query = String::new();
            let mut query_cache = preferences.cached_queries.clone();
            let mut indexed_at_last_publish = 0_usize;

            loop {
                let mut query_changed = false;
                loop {
                    match request_receiver.try_recv() {
                        Ok(SearchWorkerRequest::Query(next_query)) => {
                            query = next_query;
                            query_changed = true;
                        }
                        Ok(SearchWorkerRequest::RecordSelection {
                            query: selected_query,
                            entry,
                        }) => {
                            record_search_selection(
                                &selected_query,
                                entry,
                                &mut preferences,
                                &mut query_cache,
                            );
                            let _ = preferences_sender.send(preferences.clone());
                        }
                        Ok(SearchWorkerRequest::RecordCommandSelection {
                            query: selected_query,
                            process_name,
                        }) => {
                            record_command_selection(
                                &selected_query,
                                process_name,
                                &mut preferences,
                            );
                            let _ = preferences_sender.send(preferences.clone());
                        }
                        Ok(SearchWorkerRequest::TogglePin(entry)) => {
                            toggle_search_pin(entry, &mut preferences, &mut query_cache);
                            pinned_apps = preferences.pins.clone();
                            query_changed = true;
                        }
                        Err(mpsc::TryRecvError::Empty) => break,
                        Err(mpsc::TryRecvError::Disconnected) => return,
                    }
                }
                if query_changed {
                    if result_sender
                        .send(cached_search_catalog(
                            &query,
                            &apps,
                            &pinned_apps,
                            &files,
                            &mut query_cache,
                            &mut preferences,
                        ))
                        .is_err()
                    {
                        return;
                    }
                    ctx.request_repaint();
                    let _ = preferences_sender.send(preferences.clone());
                }

                if scan_active && let Some(directory) = directories.pop() {
                    let Ok(entries) = fs::read_dir(directory) else {
                        continue;
                    };
                    let mut entries = entries.flatten().collect::<Vec<_>>();
                    // The traversal stack pops from the end, so descending insertion
                    // makes shallower alphabetic folders (for example Applications)
                    // get indexed before unrelated deep trees.
                    entries.sort_by(|left, right| {
                        right
                            .file_name()
                            .to_string_lossy()
                            .to_ascii_lowercase()
                            .cmp(&left.file_name().to_string_lossy().to_ascii_lowercase())
                    });
                    let mut apps_changed = false;
                    for (entry_index, entry) in entries.into_iter().enumerate() {
                        if search_entry_is_hidden(&entry) {
                            continue;
                        }
                        let path = entry.path();
                        if path.is_dir() {
                            let name = entry.file_name().to_string_lossy().to_ascii_lowercase();
                            if !matches!(
                                name.as_str(),
                                "appdata"
                                    | ".git"
                                    | "node_modules"
                                    | "target"
                                    | "$recycle.bin"
                                    | "windows"
                                    | "recovery"
                                    | "system volume information"
                            )
                            {
                                if indexed_directories.insert(path.clone()) {
                                    directories.push(path);
                                }
                            }
                        } else if path.is_file() {
                            let is_app = path
                                .extension()
                                .and_then(|extension| extension.to_str())
                                .is_some_and(|extension| {
                                    extension.eq_ignore_ascii_case("exe")
                                        || extension.eq_ignore_ascii_case("lnk")
                                });
                            if is_app && scanned_app_paths.insert(path.clone())
                            {
                                let app = SearchEntry::new(
                                    path
                                        .file_stem()
                                        .unwrap_or_default()
                                        .to_string_lossy()
                                        .into_owned(),
                                    path.clone(),
                                );
                                scanned_apps.push(app.clone());
                                if live_app_paths.insert(path.clone()) {
                                    invalidate_search_cache_for_entry(
                                        &mut query_cache,
                                        &mut preferences.cached_queries,
                                        &app,
                                    );
                                    apps.push(app);
                                    apps_changed = true;
                                }
                            }
                            if !is_app {
                                let file = SearchEntry::new(
                                    entry.file_name().to_string_lossy().into_owned(),
                                    path.clone(),
                                );
                                if scanned_file_paths.insert(path.clone()) {
                                    scanned_files.push(file.clone());
                                }
                                if live_file_paths.insert(path) {
                                    invalidate_search_cache_for_entry(
                                        &mut query_cache,
                                        &mut preferences.cached_queries,
                                        &file,
                                    );
                                    files.push(file);
                                }
                            }
                        }
                        // Very large folders must not delay a newly typed query until the
                        // entire directory has been enumerated.
                        if entry_index % 128 == 0 {
                            let mut latest_query = None;
                            loop {
                                match request_receiver.try_recv() {
                                    Ok(SearchWorkerRequest::Query(next_query)) => {
                                        latest_query = Some(next_query)
                                    }
                                    Ok(SearchWorkerRequest::RecordSelection {
                                        query: selected_query,
                                        entry,
                                    }) => {
                                        record_search_selection(
                                            &selected_query,
                                            entry,
                                            &mut preferences,
                                            &mut query_cache,
                                        );
                                        let _ = preferences_sender.send(preferences.clone());
                                    }
                                    Ok(SearchWorkerRequest::RecordCommandSelection {
                                        query: selected_query,
                                        process_name,
                                    }) => {
                                        record_command_selection(
                                            &selected_query,
                                            process_name,
                                            &mut preferences,
                                        );
                                        let _ = preferences_sender.send(preferences.clone());
                                    }
                                    Ok(SearchWorkerRequest::TogglePin(entry)) => {
                                        toggle_search_pin(
                                            entry,
                                            &mut preferences,
                                            &mut query_cache,
                                        );
                                        pinned_apps = preferences.pins.clone();
                                        latest_query = Some(query.clone());
                                    }
                                    Err(mpsc::TryRecvError::Empty) => break,
                                    Err(mpsc::TryRecvError::Disconnected) => return,
                                }
                            }
                            if let Some(next_query) = latest_query {
                                query = next_query;
                                if result_sender
                                    .send(cached_search_catalog(
                                        &query,
                                        &apps,
                                        &pinned_apps,
                                        &files,
                                        &mut query_cache,
                                        &mut preferences,
                                    ))
                                    .is_err()
                                {
                                    return;
                                }
                                ctx.request_repaint();
                                let _ = preferences_sender.send(preferences.clone());
                            }
                        }
                    }
                    thread::yield_now();
                    if !query.trim().is_empty()
                        && (apps_changed
                            || files.len().saturating_sub(indexed_at_last_publish) >= 400)
                    {
                        indexed_at_last_publish = files.len();
                        if result_sender
                            .send(cached_search_catalog(
                                &query,
                                &apps,
                                &pinned_apps,
                                &files,
                                &mut query_cache,
                                &mut preferences,
                            ))
                            .is_err()
                        {
                            return;
                        }
                        ctx.request_repaint();
                    }
                    if Instant::now() >= checkpoint_at {
                        let _ = cache_sender.try_send(StoredSearchIndex {
                            version: SEARCH_INDEX_VERSION,
                            apps: apps.clone(),
                            files: files.clone(),
                        });
                        checkpoint_at = Instant::now() + SEARCH_INDEX_CHECKPOINT_INTERVAL;
                    }
                } else if scan_active {
                    // Swap atomically to the freshly reconciled catalog. This drops
                    // deleted and renamed entries while searches kept using the prior
                    // complete index throughout the scan.
                    apps = std::mem::take(&mut scanned_apps);
                    files = std::mem::take(&mut scanned_files);
                    pinned_apps = preferences.pins.clone();
                    live_app_paths = apps.iter().map(|app| app.path.clone()).collect();
                    live_file_paths = files.iter().map(|file| file.path.clone()).collect();
                    reconcile_search_caches(
                        &mut query_cache,
                        &mut preferences.cached_queries,
                        &live_app_paths,
                        &live_file_paths,
                    );
                    let _ = cache_sender.try_send(StoredSearchIndex {
                        version: SEARCH_INDEX_VERSION,
                        apps: apps.clone(),
                        files: files.clone(),
                    });
                    let _ = preferences_sender.send(preferences.clone());
                    scan_active = false;
                    refresh_at = Instant::now() + SEARCH_INDEX_REFRESH_INTERVAL;
                    checkpoint_at = Instant::now() + SEARCH_INDEX_CHECKPOINT_INTERVAL;
                    indexed_at_last_publish = files.len();
                    if result_sender
                        .send(cached_search_catalog(
                            &query,
                            &apps,
                            &pinned_apps,
                            &files,
                            &mut query_cache,
                            &mut preferences,
                        ))
                        .is_err()
                    {
                        return;
                    }
                    ctx.request_repaint();
                } else {
                    let remaining = refresh_at.saturating_duration_since(Instant::now());
                    match request_receiver.recv_timeout(remaining) {
                        Ok(SearchWorkerRequest::Query(next_query)) => {
                            query = next_query;
                            if result_sender
                                .send(cached_search_catalog(
                                    &query,
                                    &apps,
                                    &pinned_apps,
                                    &files,
                                    &mut query_cache,
                                    &mut preferences,
                                ))
                                .is_err()
                            {
                                return;
                            }
                            ctx.request_repaint();
                            let _ = preferences_sender.send(preferences.clone());
                        }
                        Ok(SearchWorkerRequest::RecordSelection {
                            query: selected_query,
                            entry,
                        }) => {
                            record_search_selection(
                                &selected_query,
                                entry,
                                &mut preferences,
                                &mut query_cache,
                            );
                            let _ = preferences_sender.send(preferences.clone());
                        }
                        Ok(SearchWorkerRequest::RecordCommandSelection {
                            query: selected_query,
                            process_name,
                        }) => {
                            record_command_selection(
                                &selected_query,
                                process_name,
                                &mut preferences,
                            );
                            let _ = preferences_sender.send(preferences.clone());
                        }
                        Ok(SearchWorkerRequest::TogglePin(entry)) => {
                            toggle_search_pin(entry, &mut preferences, &mut query_cache);
                            pinned_apps = preferences.pins.clone();
                            if result_sender
                                .send(cached_search_catalog(
                                    &query,
                                    &apps,
                                    &pinned_apps,
                                    &files,
                                    &mut query_cache,
                                    &mut preferences,
                                ))
                                .is_err()
                            {
                                return;
                            }
                            ctx.request_repaint();
                            let _ = preferences_sender.send(preferences.clone());
                        }
                        Err(mpsc::RecvTimeoutError::Timeout) => {
                            let refreshed_start_apps = discover_start_menu_apps();
                            scanned_app_paths = refreshed_start_apps
                                .iter()
                                .map(|app| app.path.clone())
                                .collect();
                            scanned_apps = refreshed_start_apps;
                            scanned_files.clear();
                            scanned_file_paths.clear();
                            directories = search_file_roots();
                            indexed_directories =
                                directories.iter().cloned().collect::<HashSet<_>>();
                            scan_active = true;
                        }
                        Err(mpsc::RecvTimeoutError::Disconnected) => return,
                    }
                }
            }
        });
    (request_sender, result_receiver)
}

fn merge_search_entries(
    destination: &mut Vec<SearchEntry>,
    entries: impl IntoIterator<Item = SearchEntry>,
) {
    let mut paths = destination
        .iter()
        .map(|entry| entry.path.clone())
        .collect::<HashSet<_>>();
    destination.extend(entries.into_iter().filter(|entry| paths.insert(entry.path.clone())));
}

fn search_index_path() -> Option<PathBuf> {
    #[cfg(target_os = "windows")]
    let base = env::var_os("LOCALAPPDATA");
    #[cfg(not(target_os = "windows"))]
    let base = env::var_os("XDG_CACHE_HOME").or_else(|| env::var_os("HOME"));

    base.map(PathBuf::from)
        .map(|path| path.join("Overbar").join("search-index-v1.json"))
}

fn load_search_index() -> Option<StoredSearchIndex> {
    let path = search_index_path()?;
    let reader = BufReader::new(fs::File::open(path).ok()?);
    let mut index = serde_json::from_reader::<_, StoredSearchIndex>(reader).ok()?;
    if !(2..=SEARCH_INDEX_VERSION).contains(&index.version) {
        return None;
    }
    for entry in index.apps.iter_mut().chain(index.files.iter_mut()) {
        if entry.name_lower.is_empty() {
            entry.name_lower = entry.name.to_ascii_lowercase();
        }
        if entry.path_lower.is_empty() {
            entry.path_lower = entry.path.to_string_lossy().to_ascii_lowercase();
        }
    }
    index.version = SEARCH_INDEX_VERSION;
    Some(index)
}

fn save_search_index(index: &StoredSearchIndex) {
    let Some(path) = search_index_path() else {
        return;
    };
    let Some(parent) = path.parent() else {
        return;
    };
    if fs::create_dir_all(parent).is_err() {
        return;
    }
    let temporary = parent.join(format!("search-index-{}.tmp", std::process::id()));
    let Ok(file) = fs::File::create(&temporary) else {
        return;
    };
    if serde_json::to_writer(BufWriter::new(file), index).is_err() {
        let _ = fs::remove_file(temporary);
        return;
    }
    if path.exists() {
        let _ = fs::remove_file(&path);
    }
    if fs::rename(&temporary, &path).is_err() {
        let _ = fs::remove_file(temporary);
    }
}

fn search_preferences_path() -> Option<PathBuf> {
    #[cfg(target_os = "windows")]
    let base = env::var_os("LOCALAPPDATA");
    #[cfg(not(target_os = "windows"))]
    let base = env::var_os("XDG_CACHE_HOME").or_else(|| env::var_os("HOME"));

    base.map(PathBuf::from)
        .map(|path| path.join("Overbar").join("search-preferences-v1.json"))
}

fn wm_config_path() -> Option<PathBuf> {
    env::var_os("LOCALAPPDATA")
        .or_else(|| env::var_os("APPDATA"))
        .map(PathBuf::from)
        .map(|path| path.join("Overbar").join("wm-config.json"))
}

fn completed_update_path() -> Option<PathBuf> {
    env::var_os("LOCALAPPDATA")
        .or_else(|| env::var_os("APPDATA"))
        .map(PathBuf::from)
        .map(|path| path.join("Overbar").join("update-complete.json"))
}

fn load_completed_update() -> Option<CompletedUpdate> {
    let path = completed_update_path()?;
    let completed = serde_json::from_reader::<_, CompletedUpdate>(BufReader::new(
        fs::File::open(path).ok()?,
    ))
    .ok()?;
    if completed.version.trim().is_empty()
        || !completed
            .version
            .trim()
            .trim_start_matches(['v', 'V'])
            .eq_ignore_ascii_case(env!("CARGO_PKG_VERSION"))
        || !completed
            .release_url
            .starts_with("https://github.com/Respite09/Overbar/releases/")
    {
        return None;
    }
    Some(completed)
}

fn clear_completed_update_marker() {
    if let Some(path) = completed_update_path() {
        let _ = fs::remove_file(path);
    }
}

fn load_wm_config() -> WmConfig {
    let Some(path) = wm_config_path() else { return WmConfig::default(); };
    let mut config: WmConfig = fs::File::open(path)
        .ok()
        .and_then(|file| serde_json::from_reader(BufReader::new(file)).ok())
        .unwrap_or_default();
    for (name, binding) in default_wm_keybindings() {
        config.keybindings.entry(name).or_insert(binding);
    }
    config.window_gap = config.window_gap.clamp(0, 64);
    config.media_name_width = config.media_name_width.clamp(80.0, 500.0);
    config
}

fn save_wm_config(config: &WmConfig) {
    let Some(path) = wm_config_path() else { return; };
    let Some(parent) = path.parent() else { return; };
    if fs::create_dir_all(parent).is_err() { return; }
    let temporary = parent.join(format!("wm-config-{}.tmp", std::process::id()));
    let Ok(file) = fs::File::create(&temporary) else { return; };
    if serde_json::to_writer_pretty(BufWriter::new(file), config).is_ok() {
        let _ = fs::rename(temporary, path);
    } else {
        let _ = fs::remove_file(temporary);
    }
}

fn spawn_update_worker(ctx: Context) -> (Sender<UpdateRequest>, Receiver<UpdateEvent>) {
    let (request_sender, request_receiver) = mpsc::channel();
    let (event_sender, event_receiver) = mpsc::channel();
    let _ = thread::Builder::new()
        .name("overbar-updater".into())
        .spawn(move || {
            let publish_check = || {
                let result = check_for_update();
                let sent = event_sender
                    .send(UpdateEvent::CheckFinished(result))
                    .is_ok();
                ctx.request_repaint();
                sent
            };
            if !publish_check() {
                return;
            }
            loop {
                match request_receiver.recv_timeout(UPDATE_CHECK_INTERVAL) {
                    Ok(UpdateRequest::Install(update)) => {
                        let event = match prepare_windows_update(&update) {
                            Ok(()) => UpdateEvent::ReadyToRestart,
                            Err(error) => UpdateEvent::InstallFailed(error),
                        };
                        if event_sender.send(event).is_err() {
                            return;
                        }
                        ctx.request_repaint();
                    }
                    Err(mpsc::RecvTimeoutError::Timeout) => {
                        if !publish_check() {
                            return;
                        }
                    }
                    Err(mpsc::RecvTimeoutError::Disconnected) => return,
                }
            }
        });
    (request_sender, event_receiver)
}

#[cfg(target_os = "windows")]
fn check_for_update() -> Result<Option<AvailableUpdate>, String> {
    let script = format!(
        "$ErrorActionPreference='Stop'; \
         [Console]::OutputEncoding=New-Object System.Text.UTF8Encoding($false); \
         $headers=@{{'User-Agent'='Overbar/{}';'Accept'='application/vnd.github+json';'X-GitHub-Api-Version'='2022-11-28'}}; \
         Invoke-RestMethod -UseBasicParsing -TimeoutSec 15 -Headers $headers -Uri '{}' | ConvertTo-Json -Depth 5 -Compress",
        env!("CARGO_PKG_VERSION"),
        UPDATE_API_URL,
    );
    let mut command = Command::new("powershell.exe");
    command.args(["-NoProfile", "-NonInteractive", "-Command", &script]);
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    hide_child_console(&mut command);
    let output = command
        .output()
        .map_err(|error| format!("Could not start the update check: {error}"))?;
    if !output.status.success() {
        let error = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        return Err(if error.is_empty() {
            format!("GitHub update check returned {}", output.status)
        } else {
            error
        });
    }
    let response = decode_powershell_output(&output.stdout);
    let release: GithubRelease = serde_json::from_str(response.trim_start_matches('\u{feff}'))
        .map_err(|error| format!("GitHub returned an invalid release response: {error}"))?;
    if !release_version_is_newer(&release.tag_name, env!("CARGO_PKG_VERSION")) {
        return Ok(None);
    }
    let asset = release
        .assets
        .iter()
        .find(|asset| asset.name.eq_ignore_ascii_case("overbar.exe"))
        .or_else(|| {
            release.assets.iter().find(|asset| {
                asset.name.to_ascii_lowercase().contains("overbar")
                    && asset.name.to_ascii_lowercase().ends_with(".exe")
            })
        })
        .ok_or_else(|| format!("Release {} has no Overbar executable", release.tag_name))?;
    if !asset
        .browser_download_url
        .starts_with(UPDATE_DOWNLOAD_PREFIX)
    {
        return Err("The release executable has an unexpected download location".to_owned());
    }
    if !release
        .html_url
        .starts_with("https://github.com/Respite09/Overbar/releases/")
    {
        return Err("The release has an unexpected changelog location".to_owned());
    }
    Ok(Some(AvailableUpdate {
        version: release.tag_name.trim_start_matches(['v', 'V']).to_owned(),
        download_url: asset.browser_download_url.clone(),
        size: asset.size,
        digest: asset.digest.clone(),
        release_url: release.html_url,
    }))
}

fn decode_powershell_output(bytes: &[u8]) -> String {
    if bytes.starts_with(&[0xff, 0xfe]) {
        let wide = bytes[2..]
            .chunks_exact(2)
            .map(|pair| u16::from_le_bytes([pair[0], pair[1]]))
            .collect::<Vec<_>>();
        String::from_utf16_lossy(&wide)
    } else if bytes.starts_with(&[0xfe, 0xff]) {
        let wide = bytes[2..]
            .chunks_exact(2)
            .map(|pair| u16::from_be_bytes([pair[0], pair[1]]))
            .collect::<Vec<_>>();
        String::from_utf16_lossy(&wide)
    } else {
        String::from_utf8_lossy(bytes).into_owned()
    }
}

#[cfg(not(target_os = "windows"))]
fn check_for_update() -> Result<Option<AvailableUpdate>, String> {
    Ok(None)
}

fn release_version_is_newer(latest: &str, current: &str) -> bool {
    fn parts(version: &str) -> Option<(Vec<u64>, bool)> {
        let without_build = version
            .trim()
            .trim_start_matches(['v', 'V'])
            .split('+')
            .next()?;
        let (core, prerelease) = without_build
            .split_once('-')
            .map_or((without_build, false), |(core, _)| (core, true));
        let values = core
            .split('.')
            .map(str::parse::<u64>)
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        (!values.is_empty()).then_some((values, prerelease))
    }
    let (Some((latest, latest_prerelease)), Some((current, current_prerelease))) =
        (parts(latest), parts(current))
    else {
        return false;
    };
    let count = latest.len().max(current.len());
    (0..count)
        .map(|index| {
            (
                latest.get(index).copied().unwrap_or(0),
                current.get(index).copied().unwrap_or(0),
            )
        })
        .find(|(latest, current)| latest != current)
        .map_or(current_prerelease && !latest_prerelease, |(latest, current)| {
            latest > current
        })
}

#[cfg(target_os = "windows")]
fn prepare_windows_update(update: &AvailableUpdate) -> Result<(), String> {
    let current = env::current_exe()
        .map_err(|error| format!("Could not locate the running executable: {error}"))?;
    let current = windows_powershell_path(&fs::canonicalize(&current).unwrap_or(current));
    let directory = current
        .parent()
        .ok_or_else(|| "The Overbar executable has no parent directory".to_owned())?;
    let process_id = std::process::id();
    let downloaded = directory.join(format!(".overbar-update-{process_id}.exe"));
    let helper = directory.join(format!(".overbar-updater-{process_id}.ps1"));
    if downloaded.exists() {
        fs::remove_file(&downloaded)
            .map_err(|error| format!("Could not clear the previous update: {error}"))?;
    }

    let download_script = concat!(
        "$ErrorActionPreference='Stop'; ",
        "$ProgressPreference='SilentlyContinue'; ",
        "[Net.ServicePointManager]::SecurityProtocol=[Net.SecurityProtocolType]::Tls12; ",
        "$headers=@{'User-Agent'='Overbar-Updater';'Accept'='application/octet-stream'}; ",
        "$destination=[Management.Automation.WildcardPattern]::Escape($env:OVERBAR_UPDATE_DESTINATION); ",
        "Invoke-WebRequest -UseBasicParsing -TimeoutSec 120 -Headers $headers -Uri $env:OVERBAR_UPDATE_URL -OutFile $destination"
    );
    let mut download = Command::new("powershell.exe");
    download.args(["-NoProfile", "-NonInteractive", "-Command", download_script]);
    download.env("OVERBAR_UPDATE_URL", &update.download_url);
    download.env("OVERBAR_UPDATE_DESTINATION", &downloaded);
    download.stdout(Stdio::null()).stderr(Stdio::piped());
    hide_child_console(&mut download);
    let output = download
        .output()
        .map_err(|error| format!("Could not start the update download: {error}"))?;
    if !output.status.success() {
        let _ = fs::remove_file(&downloaded);
        let error = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        return Err(if error.is_empty() {
            format!("The update download returned {}", output.status)
        } else {
            error
        });
    }
    let metadata = fs::metadata(&downloaded)
        .map_err(|error| format!("Could not inspect the downloaded update: {error}"))?;
    if update.size > 0 && metadata.len() != update.size {
        let _ = fs::remove_file(&downloaded);
        return Err(format!(
            "The update download was incomplete ({} of {} bytes)",
            metadata.len(),
            update.size,
        ));
    }
    let mut signature = [0_u8; 2];
    fs::File::open(&downloaded)
        .and_then(|mut file| file.read_exact(&mut signature))
        .map_err(|error| format!("Could not validate the downloaded update: {error}"))?;
    if signature != *b"MZ" {
        let _ = fs::remove_file(&downloaded);
        return Err("The downloaded release is not a Windows executable".to_owned());
    }
    if let Some(expected) = update
        .digest
        .as_deref()
        .and_then(|digest| digest.strip_prefix("sha256:"))
    {
        verify_windows_sha256(&downloaded, expected)?;
    }

    let helper_script = r#"$configPath = [System.IO.Path]::ChangeExtension($PSCommandPath, 'json')
$config = Get-Content -LiteralPath $configPath -Raw | ConvertFrom-Json
[int]$ProcessId = $config.process_id
[string]$Current = $config.current
[string]$Downloaded = $config.downloaded
[int]$RefreshStartupTask = $config.refresh_startup_task
[string]$CompletedVersion = $config.completed_version
[string]$ReleaseUrl = $config.release_url
[string]$TaskName = $config.task_name
$ErrorActionPreference = 'Stop'
$logDirectory = Join-Path $env:LOCALAPPDATA 'Overbar'
$logPath = Join-Path $logDirectory 'update.log'
$completionPath = Join-Path $logDirectory 'update-complete.json'
New-Item -ItemType Directory -Path $logDirectory -Force | Out-Null
function Write-UpdateLog([string]$Message) {
    Add-Content -LiteralPath $logPath -Value "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') $Message"
}
$backup = "$Current.old-$ProcessId"
$replaced = $false
try {
    Wait-Process -Id $ProcessId -Timeout 60 -ErrorAction SilentlyContinue
    for ($attempt = 0; $attempt -lt 50; $attempt++) {
        try {
            if (Test-Path -LiteralPath $backup) { Remove-Item -LiteralPath $backup -Force }
            try {
                [System.IO.File]::Replace($Downloaded, $Current, $backup, $true)
            } catch {
                Move-Item -LiteralPath $Current -Destination $backup -Force
                try {
                    Move-Item -LiteralPath $Downloaded -Destination $Current -Force
                } catch {
                    if ((Test-Path -LiteralPath $backup) -and -not (Test-Path -LiteralPath $Current)) {
                        Move-Item -LiteralPath $backup -Destination $Current -Force
                    }
                    throw
                }
            }
            $replaced = $true
            break
        } catch {
            Start-Sleep -Milliseconds 200
        }
    }
    if (-not $replaced) { throw 'Timed out while replacing the running executable.' }
    if ($RefreshStartupTask -eq 1) {
        $taskAction = '"' + $Current + '" --overbar-elevated'
        & schtasks.exe /Create /TN 'Overbar Startup' /TR $taskAction /SC ONLOGON /RL HIGHEST /IT /F | Out-Null
        if ($LASTEXITCODE -ne 0) { Write-UpdateLog 'Warning: the startup task could not be refreshed.' }
    }
    $completion = [ordered]@{ version = $CompletedVersion; release_url = $ReleaseUrl } | ConvertTo-Json -Compress
    [System.IO.File]::WriteAllText($completionPath, $completion, (New-Object System.Text.UTF8Encoding($false)))
    $launched = Start-Process -FilePath $Current -ArgumentList '--overbar-elevated' -WorkingDirectory (Split-Path -Parent $Current) -PassThru
    if ($launched.WaitForExit(750)) {
        throw "Updated Overbar exited immediately with code $($launched.ExitCode)."
    }
    if (Test-Path -LiteralPath $backup) { Remove-Item -LiteralPath $backup -Force }
    Write-UpdateLog 'Update installed and Overbar restarted.'
} catch {
    Write-UpdateLog "Update failed: $($_.Exception.Message)"
    if (Test-Path -LiteralPath $completionPath) {
        Remove-Item -LiteralPath $completionPath -Force -ErrorAction SilentlyContinue
    }
    if ($replaced -and (Test-Path -LiteralPath $backup)) {
        try {
            if (Test-Path -LiteralPath $Current) { Remove-Item -LiteralPath $Current -Force }
            Move-Item -LiteralPath $backup -Destination $Current -Force
        } catch {
            Write-UpdateLog "Rollback failed: $($_.Exception.Message)"
        }
    }
    if (Test-Path -LiteralPath $Current) {
        Start-Process -FilePath $Current -ArgumentList '--overbar-elevated' -WorkingDirectory (Split-Path -Parent $Current) -ErrorAction SilentlyContinue
    }
} finally {
    if (Test-Path -LiteralPath $Downloaded) { Remove-Item -LiteralPath $Downloaded -Force -ErrorAction SilentlyContinue }
    if (Test-Path -LiteralPath $configPath) { Remove-Item -LiteralPath $configPath -Force -ErrorAction SilentlyContinue }
    if ($TaskName) { & schtasks.exe /Delete /TN $TaskName /F 2>$null | Out-Null }
    Remove-Item -LiteralPath $PSCommandPath -Force -ErrorAction SilentlyContinue
}
"#;
    fs::write(&helper, helper_script)
        .map_err(|error| format!("Could not create the update helper: {error}"))?;
    let refresh_startup_task = windows_startup_task_exists();
    let task_name = format!("Overbar Update {process_id}");
    let config_path = helper.with_extension("json");
    let config = serde_json::json!({
        "process_id": process_id,
        "current": current,
        "downloaded": downloaded,
        "refresh_startup_task": i32::from(refresh_startup_task),
        "completed_version": update.version,
        "release_url": update.release_url,
        "task_name": task_name,
    });
    let config_bytes = serde_json::to_vec(&config)
        .map_err(|error| format!("Could not prepare the update handoff: {error}"))?;
    fs::write(&config_path, config_bytes)
        .map_err(|error| format!("Could not create the update handoff: {error}"))?;

    let task_action = format!(
        "powershell.exe -NoProfile -NonInteractive -WindowStyle Hidden -ExecutionPolicy Bypass -File \"{}\"",
        helper.display()
    );
    let run_schtasks = |arguments: &[&str]| -> Result<Output, String> {
        let mut command = Command::new("schtasks.exe");
        command.args(arguments);
        command.stdout(Stdio::piped()).stderr(Stdio::piped());
        hide_child_console(&mut command);
        command
            .output()
            .map_err(|error| format!("Could not start Task Scheduler: {error}"))
    };
    let create = run_schtasks(&[
        "/Create",
        "/TN",
        &task_name,
        "/TR",
        &task_action,
        "/SC",
        "ONCE",
        "/SD",
        "12/31/2099",
        "/ST",
        "23:59",
        "/RL",
        "HIGHEST",
        "/IT",
        "/F",
    ])?;
    if !create.status.success() {
        let _ = fs::remove_file(&config_path);
        let _ = fs::remove_file(&helper);
        let error = decode_powershell_output(&create.stderr).trim().to_owned();
        return Err(if error.is_empty() {
            format!("Could not create the update task ({})", create.status)
        } else {
            format!("Could not create the update task: {error}")
        });
    }
    let run = run_schtasks(&["/Run", "/TN", &task_name])?;
    if !run.status.success() {
        let _ = run_schtasks(&["/Delete", "/TN", &task_name, "/F"]);
        let _ = fs::remove_file(&config_path);
        let _ = fs::remove_file(&helper);
        let error = decode_powershell_output(&run.stderr).trim().to_owned();
        return Err(if error.is_empty() {
            format!("Could not run the update task ({})", run.status)
        } else {
            format!("Could not run the update task: {error}")
        });
    }
    Ok(())
}

#[cfg(target_os = "windows")]
fn windows_powershell_path(path: &Path) -> PathBuf {
    let path = path.to_string_lossy();
    if let Some(path) = path.strip_prefix("\\\\?\\UNC\\") {
        PathBuf::from(format!("\\\\{path}"))
    } else if let Some(path) = path.strip_prefix("\\\\?\\") {
        PathBuf::from(path)
    } else {
        PathBuf::from(path.as_ref())
    }
}

#[cfg(not(target_os = "windows"))]
fn prepare_windows_update(_update: &AvailableUpdate) -> Result<(), String> {
    Err("Automatic updates are only available on Windows".to_owned())
}

#[cfg(target_os = "windows")]
fn verify_windows_sha256(path: &Path, expected: &str) -> Result<(), String> {
    let mut command = Command::new("certutil.exe");
    command.args(["-hashfile", &path.to_string_lossy(), "SHA256"]);
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    hide_child_console(&mut command);
    let output = command
        .output()
        .map_err(|error| format!("Could not verify the update checksum: {error}"))?;
    let actual = String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(|line| line.chars().filter(|character| !character.is_whitespace()).collect::<String>())
        .find(|line| line.len() == 64 && line.chars().all(|character| character.is_ascii_hexdigit()))
        .ok_or_else(|| "Windows could not calculate the update checksum".to_owned())?;
    if actual.eq_ignore_ascii_case(expected) {
        Ok(())
    } else {
        let _ = fs::remove_file(path);
        Err("The downloaded update failed its SHA-256 verification".to_owned())
    }
}

#[cfg(target_os = "windows")]
fn windows_startup_task_exists() -> bool {
    let mut command = Command::new("schtasks.exe");
    command.args(["/Query", "/TN", "Overbar Startup"]);
    command.stdout(Stdio::null()).stderr(Stdio::null());
    hide_child_console(&mut command);
    command.status().is_ok_and(|status| status.success())
}

fn spawn_startup_task_worker(
    ctx: Context,
) -> (Sender<()>, Receiver<Result<PathBuf, String>>) {
    let (request_sender, request_receiver) = mpsc::channel();
    let (result_sender, result_receiver) = mpsc::channel();
    let _ = thread::Builder::new()
        .name("overbar-startup-task".into())
        .spawn(move || {
            while request_receiver.recv().is_ok() {
                #[cfg(target_os = "windows")]
                let result = recreate_windows_startup_task();
                #[cfg(not(target_os = "windows"))]
                let result = Err("Scheduled Tasks are only available on Windows".to_owned());
                if result_sender.send(result).is_err() {
                    return;
                }
                ctx.request_repaint();
            }
        });
    (request_sender, result_receiver)
}

#[cfg(target_os = "windows")]
fn recreate_windows_startup_task() -> Result<PathBuf, String> {
    const TASK_NAME: &str = "Overbar Startup";
    let executable = env::current_exe()
        .map_err(|error| format!("Could not locate Overbar: {error}"))?;
    let executable = fs::canonicalize(&executable).unwrap_or(executable);

    let mut delete = Command::new("schtasks.exe");
    delete.args(["/Delete", "/TN", TASK_NAME, "/F"]);
    delete.stdout(Stdio::null()).stderr(Stdio::null());
    hide_child_console(&mut delete);
    // A missing task is expected on the first click, so deletion failure is safe.
    let _ = delete.status();

    let task_action = format!("\"{}\" --overbar-elevated", executable.display());
    let mut create = Command::new("schtasks.exe");
    create.args([
        "/Create",
        "/TN",
        TASK_NAME,
        "/TR",
        &task_action,
        "/SC",
        "ONLOGON",
        "/RL",
        "HIGHEST",
        "/IT",
        "/F",
    ]);
    create.stdout(Stdio::piped()).stderr(Stdio::piped());
    hide_child_console(&mut create);
    let output = create
        .output()
        .map_err(|error| format!("Could not start Task Scheduler: {error}"))?;
    if output.status.success() {
        Ok(executable)
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        let stdout = String::from_utf8_lossy(&output.stdout).trim().to_owned();
        Err(if !stderr.is_empty() {
            stderr
        } else if !stdout.is_empty() {
            stdout
        } else {
            format!("Task Scheduler returned {}", output.status)
        })
    }
}

fn load_search_preferences() -> StoredSearchPreferences {
    let Some(path) = search_preferences_path() else {
        return StoredSearchPreferences {
            version: SEARCH_PREFERENCES_VERSION,
            ..Default::default()
        };
    };
    let preferences = fs::File::open(path)
        .ok()
        .and_then(|file| {
            serde_json::from_reader::<_, StoredSearchPreferences>(BufReader::new(file)).ok()
        })
        .filter(|preferences| (1..=SEARCH_PREFERENCES_VERSION).contains(&preferences.version));
    let mut preferences = preferences.unwrap_or(StoredSearchPreferences {
        version: SEARCH_PREFERENCES_VERSION,
        ..Default::default()
    });
    preferences.version = SEARCH_PREFERENCES_VERSION;
    preferences
}

fn save_search_preferences(preferences: &StoredSearchPreferences) {
    let Some(path) = search_preferences_path() else {
        return;
    };
    let Some(parent) = path.parent() else {
        return;
    };
    if fs::create_dir_all(parent).is_err() {
        return;
    }
    let temporary = parent.join(format!("search-preferences-{}.tmp", std::process::id()));
    let Ok(file) = fs::File::create(&temporary) else {
        return;
    };
    if serde_json::to_writer(BufWriter::new(file), preferences).is_err() {
        let _ = fs::remove_file(temporary);
        return;
    }
    if path.exists() {
        let _ = fs::remove_file(&path);
    }
    if fs::rename(&temporary, &path).is_err() {
        let _ = fs::remove_file(temporary);
    }
}

#[cfg(target_os = "windows")]
fn search_file_roots() -> Vec<PathBuf> {
    use windows::Win32::Storage::FileSystem::GetLogicalDrives;

    let drive_mask = unsafe { GetLogicalDrives() };
    let mut roots = (0..26)
        .filter(|index| drive_mask & (1_u32 << index) != 0)
        .map(|index| PathBuf::from(format!("{}:\\", (b'A' + index as u8) as char)))
        .collect::<Vec<_>>();
    // This is deliberately the general user profile, not a special-cased app
    // directory. Since the scanner uses a stack, appending it indexes user files
    // before crawling whole drives.
    if let Some(home) = env::var_os("USERPROFILE") {
        roots.push(PathBuf::from(home));
    }
    roots
}

#[cfg(target_os = "windows")]
fn search_entry_is_hidden(entry: &fs::DirEntry) -> bool {
    use std::os::windows::fs::MetadataExt;

    const FILE_ATTRIBUTE_HIDDEN: u32 = 0x2;
    entry
        .metadata()
        .map(|metadata| metadata.file_attributes() & FILE_ATTRIBUTE_HIDDEN != 0)
        .unwrap_or(true)
}

#[cfg(not(target_os = "windows"))]
fn search_entry_is_hidden(entry: &fs::DirEntry) -> bool {
    entry.file_name().to_string_lossy().starts_with('.')
}

#[cfg(not(target_os = "windows"))]
fn search_file_roots() -> Vec<PathBuf> {
    env::var_os("HOME")
        .map(PathBuf::from)
        .into_iter()
        .collect()
}

fn spawn_search_icon_worker(
    ctx: Context,
) -> (
    Sender<PathBuf>,
    Receiver<(PathBuf, Option<ColorImage>)>,
) {
    let (request_sender, request_receiver) = mpsc::channel::<PathBuf>();
    let (result_sender, result_receiver) = mpsc::channel();
    let _ = thread::Builder::new()
        .name("overbar-search-icons".into())
        .spawn(move || {
            while let Ok(path) = request_receiver.recv() {
                let image = load_cached_search_icon(&path).or_else(|| {
                    let image = shell_icon_image(&path, 24)?;
                    save_cached_search_icon(&path, &image);
                    Some(image)
                });
                if result_sender.send((path, image)).is_err() {
                    return;
                }
                ctx.request_repaint();
            }
        });
    (request_sender, result_receiver)
}

fn search_icon_cache_path(path: &Path) -> Option<PathBuf> {
    use std::collections::hash_map::DefaultHasher;

    let mut hasher = DefaultHasher::new();
    path.to_string_lossy().to_ascii_lowercase().hash(&mut hasher);
    if let Ok(metadata) = fs::metadata(path) {
        metadata.len().hash(&mut hasher);
        if let Ok(modified) = metadata.modified()
            && let Ok(duration) = modified.duration_since(std::time::UNIX_EPOCH)
        {
            duration.as_nanos().hash(&mut hasher);
        }
    }
    let base = env::var_os("LOCALAPPDATA")?;
    Some(
        PathBuf::from(base)
            .join("Overbar")
            .join("icons")
            .join(format!("{:016x}.rgba", hasher.finish())),
    )
}

fn load_cached_search_icon(path: &Path) -> Option<ColorImage> {
    let bytes = fs::read(search_icon_cache_path(path)?).ok()?;
    if bytes.len() < 8 {
        return None;
    }
    let width = u32::from_le_bytes(bytes[0..4].try_into().ok()?) as usize;
    let height = u32::from_le_bytes(bytes[4..8].try_into().ok()?) as usize;
    let rgba = &bytes[8..];
    (width > 0 && height > 0 && rgba.len() == width * height * 4)
        .then(|| ColorImage::from_rgba_unmultiplied([width, height], rgba))
}

fn save_cached_search_icon(path: &Path, image: &ColorImage) {
    let Some(cache_path) = search_icon_cache_path(path) else {
        return;
    };
    let Some(parent) = cache_path.parent() else {
        return;
    };
    if fs::create_dir_all(parent).is_err() {
        return;
    }
    let mut bytes = Vec::with_capacity(8 + image.pixels.len() * 4);
    bytes.extend_from_slice(&(image.size[0] as u32).to_le_bytes());
    bytes.extend_from_slice(&(image.size[1] as u32).to_le_bytes());
    for pixel in &image.pixels {
        bytes.extend_from_slice(&pixel.to_array());
    }
    let _ = fs::write(cache_path, bytes);
}

fn discover_start_menu_apps() -> Vec<SearchEntry> {
    let mut directories = Vec::new();
    if let Some(program_data) = env::var_os("PROGRAMDATA") {
        directories.push(
            PathBuf::from(program_data)
                .join("Microsoft")
                .join("Windows")
                .join("Start Menu")
                .join("Programs"),
        );
    }
    if let Some(app_data) = env::var_os("APPDATA") {
        directories.push(
            PathBuf::from(app_data)
                .join("Microsoft")
                .join("Windows")
                .join("Start Menu")
                .join("Programs"),
        );
    }

    let mut apps = Vec::new();
    while let Some(directory) = directories.pop() {
        let Ok(entries) = fs::read_dir(directory) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                directories.push(path);
                continue;
            }
            let extension = path
                .extension()
                .and_then(|value| value.to_str())
                .unwrap_or_default();
            if !matches!(extension.to_ascii_lowercase().as_str(), "lnk" | "url" | "exe") {
                continue;
            }
            apps.push(SearchEntry::new(
                path
                    .file_stem()
                    .unwrap_or_default()
                    .to_string_lossy()
                    .into_owned(),
                path,
            ));
        }
    }
    apps.extend(discover_windows_start_apps());
    apps.extend(discover_windows_builtin_apps());
    apps.sort_by(|left, right| left.name_lower.cmp(&right.name_lower));
    apps.dedup_by(|left, right| left.name.eq_ignore_ascii_case(&right.name));
    apps
}

#[cfg(target_os = "windows")]
fn discover_windows_builtin_apps() -> Vec<SearchEntry> {
    let Some(windows_directory) = env::var_os("WINDIR").map(PathBuf::from) else {
        return Vec::new();
    };
    let system32 = windows_directory.join("System32");
    [
        ("Command Prompt", system32.join("cmd.exe")),
        ("Task Manager", system32.join("Taskmgr.exe")),
        ("File Explorer", windows_directory.join("explorer.exe")),
        ("Registry Editor", windows_directory.join("regedit.exe")),
        ("Notepad", system32.join("notepad.exe")),
        ("Calculator", system32.join("calc.exe")),
        ("Paint", system32.join("mspaint.exe")),
        ("Control Panel", system32.join("control.exe")),
        ("System Configuration", system32.join("msconfig.exe")),
        ("Resource Monitor", system32.join("resmon.exe")),
        ("Remote Desktop Connection", system32.join("mstsc.exe")),
        ("Snipping Tool", system32.join("SnippingTool.exe")),
        ("Services", system32.join("services.msc")),
        ("Device Manager", system32.join("devmgmt.msc")),
        ("Disk Management", system32.join("diskmgmt.msc")),
        ("Event Viewer", system32.join("eventvwr.msc")),
        (
            "Windows PowerShell",
            system32
                .join("WindowsPowerShell")
                .join("v1.0")
                .join("powershell.exe"),
        ),
    ]
    .into_iter()
    .filter(|(_, path)| path.is_file())
    .map(|(name, path)| SearchEntry::new(name.to_owned(), path))
    .collect()
}

#[cfg(not(target_os = "windows"))]
fn discover_windows_builtin_apps() -> Vec<SearchEntry> {
    Vec::new()
}

#[cfg(target_os = "windows")]
fn discover_windows_start_apps() -> Vec<SearchEntry> {
    let mut command = Command::new("powershell.exe");
    command.args([
        "-NoLogo",
        "-NoProfile",
        "-NonInteractive",
        "-Command",
        "@(Get-StartApps) | Select-Object Name,AppID | ConvertTo-Json -Compress",
    ]);
    command.stdout(Stdio::piped()).stderr(Stdio::null());
    hide_child_console(&mut command);
    let Some(output) = command_output_with_timeout(command, Duration::from_secs(4)) else {
        return Vec::new();
    };
    let Ok(value) = serde_json::from_slice::<Value>(&output) else {
        return Vec::new();
    };
    let items = value.as_array().cloned().unwrap_or_else(|| vec![value]);
    items
        .into_iter()
        .filter_map(|item| {
            let name = item.get("Name")?.as_str()?.to_owned();
            let app_id = item.get("AppID")?.as_str()?;
            let direct_path = PathBuf::from(app_id);
            let path = if direct_path.is_absolute() && direct_path.exists() {
                    direct_path
                } else {
                    PathBuf::from(format!("shell:AppsFolder\\{app_id}"))
                };
            Some(SearchEntry::new(name, path))
        })
        .collect()
}

#[cfg(not(target_os = "windows"))]
fn discover_windows_start_apps() -> Vec<SearchEntry> {
    Vec::new()
}

fn command_output_with_timeout(mut command: Command, timeout: Duration) -> Option<Vec<u8>> {
    let mut child = command.spawn().ok()?;
    let mut stdout = child.stdout.take()?;
    let output_reader = thread::spawn(move || {
        let mut output = Vec::new();
        stdout.read_to_end(&mut output).ok().map(|_| output)
    });
    let deadline = Instant::now() + timeout;
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let output = output_reader.join().ok().flatten();
                return status.success().then_some(output).flatten();
            }
            Ok(None) if Instant::now() < deadline => thread::sleep(Duration::from_millis(20)),
            _ => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = output_reader.join();
                return None;
            }
        }
    }
}

fn cached_search_catalog(
    query: &str,
    apps: &[SearchEntry],
    pinned_apps: &[SearchEntry],
    files: &[SearchEntry],
    cache: &mut HashMap<String, SearchResults>,
    preferences: &mut StoredSearchPreferences,
) -> SearchResults {
    let key = query.trim().to_ascii_lowercase();
    if launcher_command(query).is_some() {
        return SearchResults {
            query: query.to_owned(),
            ..Default::default()
        };
    }
    let mut results = if let Some(results) = cache.get(&key) {
        results.clone()
    } else if let Some(results) = preferences.cached_queries.get(&key).cloned() {
        results
    } else if key.is_empty() {
        search_home_results(preferences)
    } else {
        search_catalog(query, apps, pinned_apps, files)
    };
    results.pinned_paths = preferences
        .pins
        .iter()
        .map(|entry| entry.path.clone())
        .collect();
    if !key.is_empty() {
        let pinned = results
            .pinned_paths
            .iter()
            .collect::<HashSet<_>>();
        let app_paths = apps.iter().map(|entry| &entry.path).collect::<HashSet<_>>();
        let mut matching_pins = Vec::new();
        for entry in std::mem::take(&mut results.pins) {
            if pinned.contains(&entry.path) {
                matching_pins.push(entry);
            } else if app_paths.contains(&entry.path) {
                results.apps.push(entry);
            } else {
                results.files.push(entry);
            }
        }
        results.apps.retain(|entry| {
            if pinned.contains(&entry.path) {
                matching_pins.push(entry.clone());
                false
            } else {
                true
            }
        });
        results.files.retain(|entry| {
            if pinned.contains(&entry.path) {
                matching_pins.push(entry.clone());
                false
            } else {
                true
            }
        });
        matching_pins.sort_by_key(|entry| {
            preferences
                .pins
                .iter()
                .position(|pinned| pinned.path == entry.path)
                .unwrap_or(usize::MAX)
        });
        matching_pins.dedup_by(|left, right| left.path == right.path);
        results.pins = matching_pins;
    }
    if let Some(preferred_path) = preferences.selections.get(&key) {
        if let Some(index) = results
            .pins
            .iter()
            .position(|entry| entry.path == *preferred_path)
        {
            let preferred = results.pins.remove(index);
            results.pins.insert(0, preferred);
        } else {
            promote_search_result(&mut results.apps, apps, preferred_path, 50);
            promote_search_result(&mut results.files, files, preferred_path, 100);
        }
    }
    cache.insert(key.clone(), results.clone());
    if preferences.cached_queries.len() >= 64
        && let Some(oldest_key) = preferences.cached_queries.keys().next().cloned()
    {
        preferences.cached_queries.remove(&oldest_key);
    }
    preferences.cached_queries.insert(key, results.clone());
    results
}

fn promote_search_result(
    entries: &mut Vec<SearchEntry>,
    catalog: &[SearchEntry],
    preferred_path: &Path,
    limit: usize,
) {
    if let Some(index) = entries.iter().position(|entry| entry.path == preferred_path) {
        let preferred = entries.remove(index);
        entries.insert(0, preferred);
    } else if let Some(preferred) = catalog
        .iter()
        .find(|entry| entry.path == preferred_path)
        .cloned()
    {
        entries.insert(0, preferred);
        entries.truncate(limit);
    }
}

fn search_prefixes(query: &str) -> Vec<String> {
    let normalized = query.trim().to_ascii_lowercase();
    normalized
        .char_indices()
        .map(|(index, character)| normalized[..index + character.len_utf8()].to_owned())
        .filter(|prefix| !prefix.trim().is_empty())
        .collect()
}

fn record_search_selection(
    query: &str,
    entry: SearchEntry,
    preferences: &mut StoredSearchPreferences,
    cache: &mut HashMap<String, SearchResults>,
) {
    let prefixes = search_prefixes(query);
    for prefix in &prefixes {
        preferences
            .selections
            .insert(prefix.clone(), entry.path.clone());
        cache.remove(prefix);
        preferences.cached_queries.remove(prefix);
    }
    preferences
        .recents
        .retain(|recent| recent.path != entry.path);
    preferences.recents.insert(0, entry);
    preferences.recents.truncate(SEARCH_RECENT_LIMIT);
    cache.remove("");
    preferences.cached_queries.remove("");
}

fn record_command_selection(
    query: &str,
    process_name: String,
    preferences: &mut StoredSearchPreferences,
) {
    for prefix in search_prefixes(query) {
        preferences
            .command_selections
            .insert(prefix, process_name.clone());
    }
}

fn toggle_search_pin(
    entry: SearchEntry,
    preferences: &mut StoredSearchPreferences,
    cache: &mut HashMap<String, SearchResults>,
) {
    if let Some(index) = preferences
        .pins
        .iter()
        .position(|pinned| pinned.path == entry.path)
    {
        preferences.pins.remove(index);
    } else {
        preferences.pins.insert(0, entry);
    }
    cache.clear();
    preferences.cached_queries.clear();
}

fn search_home_results(preferences: &StoredSearchPreferences) -> SearchResults {
    let pinned_paths = preferences
        .pins
        .iter()
        .map(|entry| entry.path.clone())
        .collect::<Vec<_>>();
    let pinned = pinned_paths.iter().collect::<HashSet<_>>();
    SearchResults {
        query: String::new(),
        pins: preferences.pins.clone(),
        recents: preferences
            .recents
            .iter()
            .filter(|entry| !pinned.contains(&entry.path))
            .take(SEARCH_RECENT_LIMIT)
            .cloned()
            .collect(),
        pinned_paths,
        ..Default::default()
    }
}

fn invalidate_search_cache_for_entry(
    cache: &mut HashMap<String, SearchResults>,
    persistent_cache: &mut HashMap<String, SearchResults>,
    entry: &SearchEntry,
) {
    let retain = |query: &String| {
        if query.is_empty() || kill_command_term(query).is_some() {
            return true;
        }
        let matches = std::iter::once(query.as_str())
            .chain(search_aliases(query).iter().copied())
            .any(|term| entry.name_lower.contains(term) || entry.path_lower.contains(term));
        !matches
    };
    cache.retain(|query, _| retain(query));
    persistent_cache.retain(|query, _| retain(query));
}

fn reconcile_search_caches(
    cache: &mut HashMap<String, SearchResults>,
    persistent_cache: &mut HashMap<String, SearchResults>,
    app_paths: &HashSet<PathBuf>,
    file_paths: &HashSet<PathBuf>,
) {
    let reconcile = |results: &mut SearchResults| {
        results.apps.retain(|entry| app_paths.contains(&entry.path));
        results.files.retain(|entry| file_paths.contains(&entry.path));
    };
    for results in cache.values_mut() {
        reconcile(results);
    }
    for results in persistent_cache.values_mut() {
        reconcile(results);
    }
}

fn search_catalog(
    query: &str,
    apps: &[SearchEntry],
    pinned_apps: &[SearchEntry],
    files: &[SearchEntry],
) -> SearchResults {
    let term = query.trim().to_ascii_lowercase();
    if kill_command_term(query).is_some() || launcher_command(query).is_some() {
        return SearchResults {
            query: query.to_owned(),
            ..Default::default()
        };
    }
    if term.is_empty() {
        return SearchResults {
            query: query.to_owned(),
            apps: pinned_apps.to_vec(),
            files: Vec::new(),
            ..Default::default()
        };
    }
    let mut terms = vec![term.clone()];
    terms.extend(search_aliases(&term).iter().map(|alias| (*alias).to_owned()));

    let search = |entries: &[SearchEntry], limit: usize| {
        let mut matches = entries
            .iter()
            .filter_map(|entry| {
                let name = entry.name_lower.as_str();
                let path = entry.path_lower.as_str();
                let score = terms
                    .iter()
                    .filter_map(|term| {
                        if name.starts_with(term) {
                            Some(0)
                        } else if name
                            .split(|character: char| !character.is_alphanumeric())
                            .any(|word| word.starts_with(term))
                        {
                            Some(1)
                        } else if name.contains(term) {
                            Some(2)
                        } else if path.contains(term) {
                            Some(3)
                        } else {
                            None
                        }
                    })
                    .min()?;
                Some((score, name.len(), entry))
            })
            .collect::<Vec<_>>();
        if matches.len() > limit {
            matches.select_nth_unstable_by(limit, |left, right| {
                (left.0, left.1, left.2.name_lower.as_str()).cmp(&(
                    right.0,
                    right.1,
                    right.2.name_lower.as_str(),
                ))
            });
            matches.truncate(limit);
        }
        matches.sort_by(|left, right| {
            (left.0, left.1, left.2.name_lower.as_str()).cmp(&(
                right.0,
                right.1,
                right.2.name_lower.as_str(),
            ))
        });
        matches
            .into_iter()
            .map(|(_, _, entry)| entry.clone())
            .collect()
    };

    SearchResults {
        query: query.to_owned(),
        apps: search(apps, 50),
        files: search(files, 100),
        ..Default::default()
    }
}

fn search_aliases(term: &str) -> &'static [&'static str] {
    match term {
        "cmd" | "command" => &["command prompt", "cmd.exe"],
        "taskmgr" | "tskmgr" | "task manager" => &["task manager", "taskmgr.exe"],
        "pwsh" | "powershell" | "ps" => &["powershell", "powershell.exe"],
        "explorer" | "files" => &["file explorer", "explorer.exe"],
        "control" => &["control panel", "control.exe"],
        "settings" | "config" => &["settings", "system configuration"],
        "regedit" | "registry" => &["registry editor", "regedit.exe"],
        "calc" => &["calculator", "calc.exe"],
        "paint" | "mspaint" => &["paint", "mspaint.exe"],
        "snip" | "screenshot" => &["snipping tool", "snippingtool.exe"],
        "terminal" | "wt" => &["windows terminal", "wt.exe"],
        "services" => &["services", "services.msc"],
        "devices" | "devmgmt" => &["device manager", "devmgmt.msc"],
        "disks" | "diskmgmt" => &["disk management", "diskmgmt.msc"],
        "events" | "eventvwr" => &["event viewer", "eventvwr.msc"],
        "resmon" => &["resource monitor", "resmon.exe"],
        "msconfig" => &["system configuration", "msconfig.exe"],
        "mstsc" | "rdp" => &["remote desktop connection", "mstsc.exe"],
        "notepad" | "text editor" => &["notepad", "notepad.exe"],
        _ => &[],
    }
}

fn launcher_command(query: &str) -> Option<LauncherCommand> {
    let trimmed = query.trim();
    if let Some(term) = trimmed.strip_prefix('?').map(str::trim)
        && !term.is_empty()
    {
        return Some(LauncherCommand {
            name: format!("Search the web for “{term}”"),
            detail: "Web search · Opens in your default browser".to_owned(),
            action: LauncherCommandAction::WebSearch(term.to_owned()),
        });
    }
    let normalized = trimmed.to_ascii_lowercase();
    let power = |name: &str, detail: &str, action| LauncherCommand {
        name: name.to_owned(),
        detail: format!("Power · {detail}"),
        action: LauncherCommandAction::Power(action),
    };
    match normalized.as_str() {
        "lock" | "lock pc" => return Some(power("Lock", "Lock this PC", PowerAction::Lock)),
        "sleep" => return Some(power("Sleep", "Put this PC to sleep", PowerAction::Sleep)),
        "hibernate" => {
            return Some(power(
                "Hibernate",
                "Hibernate this PC",
                PowerAction::Hibernate,
            ));
        }
        "shutdown" | "shut down" | "poweroff" | "power off" => {
            return Some(power(
                "Shutdown",
                "Shut down this PC",
                PowerAction::Shutdown,
            ));
        }
        "restart" | "reboot" => {
            return Some(power(
                "Restart",
                "Restart this PC",
                PowerAction::Restart,
            ));
        }
        "sign out" | "log out" | "logout" | "logoff" => {
            return Some(power(
                "Sign out",
                "Sign out of Windows",
                PowerAction::SignOut,
            ));
        }
        "quit" | "exit" | "quit overbar" | "exit overbar" => {
            return Some(LauncherCommand {
                name: "Quit Overbar".to_owned(),
                detail: "System command · Close Overbar".to_owned(),
                action: LauncherCommandAction::Quit,
            });
        }
        _ => {}
    }

    let folder = |name: &str, path: PathBuf| LauncherCommand {
        name: name.to_owned(),
        detail: format!("System folder · {}", path.display()),
        action: LauncherCommandAction::OpenTarget(path.to_string_lossy().into_owned()),
    };
    let user_folder = |name: &str| {
        env::var_os("USERPROFILE").map(PathBuf::from).map(|path| path.join(name))
    };
    let folder_command = match normalized.as_str() {
        "home" | "user folder" | "profile" => env::var_os("USERPROFILE")
            .map(PathBuf::from)
            .map(|path| folder("Home", path)),
        "downloads" | "download" => user_folder("Downloads").map(|path| folder("Downloads", path)),
        "documents" | "docs" => user_folder("Documents").map(|path| folder("Documents", path)),
        "desktop" => user_folder("Desktop").map(|path| folder("Desktop", path)),
        "pictures" | "photos" => user_folder("Pictures").map(|path| folder("Pictures", path)),
        "screenshots" => user_folder("Pictures")
            .map(|path| folder("Screenshots", path.join("Screenshots"))),
        "music" => user_folder("Music").map(|path| folder("Music", path)),
        "videos" => user_folder("Videos").map(|path| folder("Videos", path)),
        "startup" | "startup folder" => env::var_os("APPDATA")
            .map(PathBuf::from)
            .map(|path| path.join(r"Microsoft\Windows\Start Menu\Programs\Startup"))
            .map(|path| folder("Startup", path)),
        "temp" | "temporary files" => Some(folder("Temp", env::temp_dir())),
        "appdata" | "roaming appdata" => env::var_os("APPDATA")
            .map(PathBuf::from)
            .map(|path| folder("AppData", path)),
        "localappdata" | "local appdata" => env::var_os("LOCALAPPDATA")
            .map(PathBuf::from)
            .map(|path| folder("Local AppData", path)),
        "programdata" | "program data" => env::var_os("PROGRAMDATA")
            .map(PathBuf::from)
            .map(|path| folder("ProgramData", path)),
        "windows" | "windows folder" => env::var_os("WINDIR")
            .map(PathBuf::from)
            .map(|path| folder("Windows", path)),
        "system32" => env::var_os("WINDIR")
            .map(PathBuf::from)
            .map(|path| folder("System32", path.join("System32"))),
        "fonts" => env::var_os("WINDIR")
            .map(PathBuf::from)
            .map(|path| folder("Fonts", path.join("Fonts"))),
        "recycle bin" | "trash" => Some(LauncherCommand {
            name: "Recycle Bin".to_owned(),
            detail: "System folder · Recycle Bin".to_owned(),
            action: LauncherCommandAction::OpenTarget("shell:RecycleBinFolder".to_owned()),
        }),
        "all apps" | "applications" => Some(LauncherCommand {
            name: "All Apps".to_owned(),
            detail: "System folder · Installed applications".to_owned(),
            action: LauncherCommandAction::OpenTarget("shell:AppsFolder".to_owned()),
        }),
        _ => None,
    };
    if folder_command.is_some() {
        return folder_command;
    }

    let settings = |name: &str, page: &str| LauncherCommand {
        name: name.to_owned(),
        detail: "Windows Settings · Open settings page".to_owned(),
        action: LauncherCommandAction::OpenTarget(page.to_owned()),
    };
    match normalized.as_str() {
        "bluetooth" => Some(settings("Bluetooth settings", "ms-settings:bluetooth")),
        "wifi" | "wi-fi" => Some(settings("Wi-Fi settings", "ms-settings:network-wifi")),
        "network" | "network settings" => Some(settings("Network settings", "ms-settings:network")),
        "display" | "display settings" => Some(settings("Display settings", "ms-settings:display")),
        "sound" | "sound settings" => Some(settings("Sound settings", "ms-settings:sound")),
        "apps" | "apps settings" => Some(settings("Apps settings", "ms-settings:appsfeatures")),
        "updates" | "windows update" => Some(settings("Windows Update", "ms-settings:windowsupdate")),
        "notifications" => Some(settings("Notification settings", "ms-settings:notifications")),
        "storage" | "storage settings" => Some(settings("Storage settings", "ms-settings:storagesense")),
        "personalization" | "personalisation" => Some(settings("Personalization", "ms-settings:personalization")),
        "privacy" | "privacy settings" => Some(settings("Privacy settings", "ms-settings:privacy")),
        "power settings" | "power options" => Some(settings("Power settings", "ms-settings:powersleep")),
        "default apps" => Some(settings("Default apps", "ms-settings:defaultapps")),
        "date and time" | "time settings" => Some(settings("Date & time", "ms-settings:dateandtime")),
        _ => None,
    }
}

fn percent_encode_query(query: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut encoded = String::with_capacity(query.len());
    for byte in query.bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' | b'~' => {
                encoded.push(byte as char);
            }
            b' ' => encoded.push('+'),
            _ => {
                encoded.push('%');
                encoded.push(HEX[(byte >> 4) as usize] as char);
                encoded.push(HEX[(byte & 0x0f) as usize] as char);
            }
        }
    }
    encoded
}

fn kill_command_term(query: &str) -> Option<&str> {
    let (command, term) = query.trim().split_once(char::is_whitespace)?;
    (command.eq_ignore_ascii_case("kill") && !term.trim().is_empty()).then_some(term.trim())
}

#[cfg(target_os = "windows")]
fn spawn_search_shortcut_worker(ctx: Context, running: Arc<AtomicBool>) -> Receiver<()> {
    use windows::Win32::UI::{
        Input::KeyboardAndMouse::{
            MOD_ALT, MOD_NOREPEAT, RegisterHotKey, UnregisterHotKey, VK_SPACE,
        },
        WindowsAndMessaging::{MSG, PM_REMOVE, PeekMessageW, WM_HOTKEY},
    };

    let (sender, receiver) = mpsc::channel();
    let _ = thread::Builder::new()
        .name("overbar-search-shortcut".into())
        .spawn(move || {
            const SEARCH_HOTKEY_ID: i32 = 0x4f42;
            if unsafe {
                RegisterHotKey(
                    None,
                    SEARCH_HOTKEY_ID,
                    MOD_ALT | MOD_NOREPEAT,
                    VK_SPACE.0 as u32,
                )
            }
            .is_err()
            {
                return;
            }
            while running.load(Ordering::Acquire) {
                let mut message = MSG::default();
                let hotkey_pressed = unsafe {
                    PeekMessageW(&mut message, None, WM_HOTKEY, WM_HOTKEY, PM_REMOVE).as_bool()
                } && message.wParam.0 as i32 == SEARCH_HOTKEY_ID;
                if hotkey_pressed {
                    if sender.send(()).is_err() {
                        break;
                    }
                    ctx.request_repaint();
                }
                thread::sleep(Duration::from_millis(10));
            }
            unsafe {
                let _ = UnregisterHotKey(None, SEARCH_HOTKEY_ID);
            }
        });
    receiver
}

#[cfg(not(target_os = "windows"))]
fn spawn_search_shortcut_worker(_ctx: Context, _running: Arc<AtomicBool>) -> Receiver<()> {
    let (_sender, receiver) = mpsc::channel();
    receiver
}

#[cfg(target_os = "windows")]
fn spawn_title_worker(ctx: Context, running: Arc<AtomicBool>) -> Receiver<String> {
    use windows::Win32::{
        System::Threading::GetCurrentProcessId,
        UI::WindowsAndMessaging::{
            GetClassNameW, GetForegroundWindow, GetWindowTextLengthW, GetWindowTextW,
            GetWindowThreadProcessId,
        },
    };

    let (sender, receiver) = mpsc::channel();
    let _ = thread::Builder::new()
        .name("foreground-title-watcher".into())
        .spawn(move || {
            let mut previous = String::new();
            while running.load(Ordering::Acquire) {
                let hwnd = unsafe { GetForegroundWindow() };
                if !hwnd.is_invalid() {
                    let mut process_id = 0_u32;
                    unsafe { GetWindowThreadProcessId(hwnd, Some(&mut process_id)) };
                    if process_id == unsafe { GetCurrentProcessId() } {
                        thread::sleep(Duration::from_millis(40));
                        continue;
                    }
                    let mut class_buffer = [0_u16; 256];
                    let class_length = unsafe { GetClassNameW(hwnd, &mut class_buffer) }
                        .max(0) as usize;
                    let class_name = String::from_utf16_lossy(&class_buffer[..class_length]);
                    let process_name = window_manager::window_process_name(hwnd)
                        .unwrap_or_default();
                    let length = unsafe { GetWindowTextLengthW(hwnd) };
                    let title = if length > 0 {
                        let mut buffer = vec![0_u16; length as usize + 1];
                        let copied = unsafe { GetWindowTextW(hwnd, &mut buffer) };
                        if copied > 0 {
                            String::from_utf16_lossy(&buffer[..copied as usize])
                                .trim()
                                .to_owned()
                        } else {
                            String::new()
                        }
                    } else {
                        String::new()
                    };
                    let title = if is_shell_surface_title(&title, &class_name, &process_name)
                        || is_transient_title_surface(hwnd, &class_name)
                    {
                        "Type here to search...".to_owned()
                    } else {
                        title
                    };
                    if !title.is_empty() && title != previous {
                        previous.clone_from(&title);
                        if sender.send(title).is_err() {
                            return;
                        }
                        ctx.request_repaint();
                    }
                }
                thread::sleep(Duration::from_millis(40));
            }
        });
    receiver
}

fn is_shell_surface_title(title: &str, class_name: &str, process_name: &str) -> bool {
    let title = title.trim().to_ascii_lowercase();
    let class_name = class_name.trim().to_ascii_lowercase();
    let process_name = process_name.trim().to_ascii_lowercase();
    let process_name = process_name.strip_suffix(".exe").unwrap_or(&process_name);
    let shell_class = matches!(
        class_name.as_str(),
        "progman" | "workerw" | "shell_traywnd" | "shell_secondarytraywnd"
            | "notifyiconoverflowwindow" | "toplevelwindowforoverflowxamlisland"
            | "multitaskingviewframe" | "tasklistthumbnailwnd" | "tasklistoverlaywnd"
            | "xaml_windowedpopupclass" | "foregroundstaging" | "immersivelauncher"
            | "launchertipwnd" | "tooltips_class32" | "#32768"
    );
    let shell_process = matches!(
        process_name,
        "popuphost" | "shellexperiencehost" | "startmenuexperiencehost"
            | "searchhost" | "searchapp" | "textinputhost" | "widgets"
            | "lockapp" | "securityhealthsystray" | "runtimebroker"
            | "backgroundtaskhost" | "taskhostw" | "sihost" | "ctfmon"
            | "fontdrvhost" | "audiodg" | "searchindexer"
    );
    let shell_title = matches!(
        title.as_str(),
        "program manager" | "system tray overflow window" | "task switching"
            | "notification center" | "action center" | "jump list" | "jumplist"
            | "popuphost" | "windows shell experience host"
    );
    shell_class
        || shell_process
        || is_background_window_identity(&title, &class_name)
        || (process_name == "explorer" && shell_title)
}

fn is_background_window_identity(title: &str, class_name: &str) -> bool {
    let title = title.trim().to_ascii_lowercase();
    let class_name = class_name.trim().to_ascii_lowercase();
    let background_class = matches!(
        class_name.as_str(),
        "olemainthreadwndclass" | "cicerouiwndframe" | "msctfime ui" | "ime"
            | "default ime" | "chrome_messagewindow" | "chrome_systemmessagewindow"
            | "mozillahiddenwindowclass" | "mozillataskbarpreviewclass"
            | "qtrayiconmessagewindow" | "systemresourcenotifywindow"
            | "mediacontextnotificationwindow" | "dde server window"
    ) || class_name.contains("broadcastwindow")
        || class_name.contains("hiddenwindow")
        || class_name.contains("messagewindow")
        || class_name.contains("trayicon")
        || class_name.contains("taskbarpreview");
    let background_title = matches!(
        title.as_str(),
        "default ime" | "msctfime ui" | "dde server window" | "olemainthreadwndname"
            | "systemresourcenotifywindow" | "mediacontextnotificationwindow"
    ) || title.starts_with(".net-broadcasteventwindow")
        || title.starts_with("gdi+ window")
        || title.starts_with("visualstudiobroadcastwindow");
    background_class || background_title
}

fn is_transient_title_class(class_name: &str) -> bool {
    let class_name = class_name.trim().to_ascii_lowercase();
    class_name.contains("popup")
        || class_name.contains("tooltip")
        || class_name.contains("flyout")
        || class_name.contains("qmenu")
        || class_name.contains("traymenu")
}

#[cfg(target_os = "windows")]
fn is_transient_title_surface(
    hwnd: windows::Win32::Foundation::HWND,
    class_name: &str,
) -> bool {
    use windows::Win32::UI::WindowsAndMessaging::{
        GWL_EXSTYLE, GWL_STYLE, GW_OWNER, GetWindow, GetWindowLongW, GetWindowRect, WS_CAPTION,
        WS_EX_APPWINDOW, WS_EX_NOACTIVATE, WS_EX_TOOLWINDOW, WS_POPUP, WS_THICKFRAME,
    };

    if is_transient_title_class(class_name) {
        return true;
    }
    let style = unsafe { GetWindowLongW(hwnd, GWL_STYLE) } as u32;
    let ex_style = unsafe { GetWindowLongW(hwnd, GWL_EXSTYLE) } as u32;
    if ex_style & WS_EX_NOACTIVATE.0 != 0 {
        return true;
    }
    if style & WS_POPUP.0 != 0
        && style & WS_CAPTION.0 == 0
        && ex_style & WS_EX_TOOLWINDOW.0 != 0
    {
        return true;
    }
    let owner = unsafe { GetWindow(hwnd, GW_OWNER) }
        .ok()
        .is_some_and(|owner| !owner.is_invalid());
    if owner
        || ex_style & WS_EX_APPWINDOW.0 != 0
        || style & (WS_CAPTION.0 | WS_THICKFRAME.0) != 0
    {
        return false;
    }
    let mut rect = windows::Win32::Foundation::RECT::default();
    unsafe { GetWindowRect(hwnd, &mut rect) }.is_err()
        || rect.right - rect.left < 320
        || rect.bottom - rect.top < 200
}

#[cfg(not(target_os = "windows"))]
fn spawn_title_worker(_ctx: Context, _running: Arc<AtomicBool>) -> Receiver<String> {
    let (_sender, receiver) = mpsc::channel();
    receiver
}

#[cfg(target_os = "windows")]
fn hide_child_console(command: &mut Command) {
    use std::os::windows::process::CommandExt;
    const CREATE_NO_WINDOW: u32 = 0x0800_0000;
    command.creation_flags(CREATE_NO_WINDOW);
}

#[cfg(not(target_os = "windows"))]
fn hide_child_console(_command: &mut Command) {}

#[cfg(target_os = "windows")]
fn process_can_terminate(pid: u32) -> bool {
    use windows::Win32::{
        Foundation::{BOOL, CloseHandle},
        System::Threading::{
            IsProcessCritical, OpenProcess, PROCESS_QUERY_LIMITED_INFORMATION, PROCESS_TERMINATE,
        },
    };

    if pid <= 4 {
        return false;
    }

    let Ok(query_handle) = (unsafe { OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, false, pid) })
    else {
        return false;
    };
    let mut critical = BOOL::default();
    let critical_result = unsafe { IsProcessCritical(query_handle, &mut critical) };
    unsafe {
        let _ = CloseHandle(query_handle);
    }
    if critical_result.is_err() || critical.as_bool() {
        return false;
    }

    let Ok(terminate_handle) = (unsafe { OpenProcess(PROCESS_TERMINATE, false, pid) }) else {
        return false;
    };
    unsafe {
        let _ = CloseHandle(terminate_handle);
    }
    true
}

#[cfg(not(target_os = "windows"))]
fn process_can_terminate(_pid: u32) -> bool {
    true
}

#[cfg(target_os = "windows")]
fn play_launcher_open_sound() {
    use std::os::windows::ffi::OsStrExt;
    use windows::{
        Win32::Media::Audio::{PlaySoundW, SND_FILENAME, SND_NODEFAULT, SND_SYNC},
        core::PCWSTR,
    };

    let Some(windows_directory) = env::var_os("WINDIR") else {
        return;
    };
    let sound_path = PathBuf::from(windows_directory)
        .join("Media")
        .join("Windows Navigation Start.wav");
    if !sound_path.is_file() {
        return;
    }
    let _ = thread::Builder::new()
        .name("overbar-launcher-sound".into())
        .spawn(move || {
            let wide = sound_path
                .as_os_str()
                .encode_wide()
                .chain(std::iter::once(0))
                .collect::<Vec<_>>();
            unsafe {
                let _ = PlaySoundW(
                    PCWSTR(wide.as_ptr()),
                    None,
                    SND_FILENAME | SND_NODEFAULT | SND_SYNC,
                );
            }
        });
}

#[cfg(not(target_os = "windows"))]
fn play_launcher_open_sound() {}

#[cfg(target_os = "windows")]
fn reveal_search_path(path: &Path) {
    let mut command = Command::new("explorer.exe");
    if path.to_string_lossy().starts_with("shell:AppsFolder\\") {
        // Packaged apps do not have a revealable filesystem location.
        command.arg("shell:AppsFolder");
    } else {
        command.arg(format!("/select,{}", path.display()));
    }
    hide_child_console(&mut command);
    let _ = command.spawn();
}

#[cfg(not(target_os = "windows"))]
fn reveal_search_path(path: &Path) {
    let directory = path.parent().unwrap_or(path);
    let _ = Command::new("xdg-open").arg(directory).spawn();
}

#[cfg(target_os = "windows")]
fn open_search_path(path: &Path) {
    use std::os::windows::ffi::OsStrExt;
    use windows::{
        Win32::UI::{Shell::ShellExecuteW, WindowsAndMessaging::SW_SHOWNORMAL},
        core::{PCWSTR, w},
    };

    let wide = path
        .as_os_str()
        .encode_wide()
        .chain(std::iter::once(0))
        .collect::<Vec<_>>();
    unsafe {
        let _ = ShellExecuteW(
            None,
            w!("open"),
            PCWSTR(wide.as_ptr()),
            PCWSTR::null(),
            PCWSTR::null(),
            SW_SHOWNORMAL,
        );
    }
}

#[cfg(not(target_os = "windows"))]
fn open_search_path(path: &Path) {
    let _ = Command::new("xdg-open").arg(path).spawn();
}

#[cfg(target_os = "windows")]
fn windows_accent_color() -> Color32 {
    use windows::Win32::{Foundation::BOOL, Graphics::Dwm::DwmGetColorizationColor};

    let mut color = 0_u32;
    let mut opaque = BOOL::default();
    if unsafe { DwmGetColorizationColor(&mut color, &mut opaque) }.is_ok() {
        return Color32::from_rgb(
            ((color >> 16) & 0xff) as u8,
            ((color >> 8) & 0xff) as u8,
            (color & 0xff) as u8,
        );
    }
    DEFAULT_ACCENT
}

#[cfg(not(target_os = "windows"))]
fn windows_accent_color() -> Color32 {
    DEFAULT_ACCENT
}

#[cfg(target_os = "windows")]
fn battery_percent() -> Option<u8> {
    use windows::Win32::System::Power::{GetSystemPowerStatus, SYSTEM_POWER_STATUS};

    let mut status = SYSTEM_POWER_STATUS::default();
    unsafe { GetSystemPowerStatus(&mut status).ok()? };
    (status.BatteryLifePercent <= 100).then_some(status.BatteryLifePercent)
}

#[cfg(not(target_os = "windows"))]
fn battery_percent() -> Option<u8> {
    None
}

#[cfg(target_os = "windows")]
fn window_icon_image(handle: isize, size: usize) -> Option<ColorImage> {
    use std::ffi::c_void;
    use windows::Win32::{
        Foundation::{HWND, LPARAM, WPARAM},
        Graphics::Gdi::{
            BI_RGB, BITMAPINFO, BITMAPINFOHEADER, CreateCompatibleDC, CreateDIBSection,
            DIB_RGB_COLORS, DeleteDC, DeleteObject, SelectObject,
        },
        UI::WindowsAndMessaging::{
            DI_NORMAL, DrawIconEx, GCLP_HICONSM, GetClassLongPtrW, HICON, ICON_SMALL, ICON_SMALL2,
            SMTO_ABORTIFHUNG, SendMessageTimeoutW, WM_GETICON,
        },
    };

    let hwnd = HWND(handle as *mut c_void);
    if hwnd.is_invalid() || size == 0 {
        return None;
    }
    let mut message_result = 0_usize;
    let _ = unsafe {
        SendMessageTimeoutW(
            hwnd,
            WM_GETICON,
            WPARAM(ICON_SMALL2 as usize),
            LPARAM(0),
            SMTO_ABORTIFHUNG,
            10,
            Some(&mut message_result),
        )
    };
    let mut icon = message_result as isize;
    if icon == 0 {
        let _ = unsafe {
            SendMessageTimeoutW(
                hwnd,
                WM_GETICON,
                WPARAM(ICON_SMALL as usize),
                LPARAM(0),
                SMTO_ABORTIFHUNG,
                10,
                Some(&mut message_result),
            )
        };
        icon = message_result as isize;
    }
    if icon == 0 {
        icon = unsafe { GetClassLongPtrW(hwnd, GCLP_HICONSM) as isize };
    }
    if icon == 0 {
        return None;
    }

    unsafe {
        let dc = CreateCompatibleDC(None);
        if dc.is_invalid() {
            return None;
        }
        let mut bitmap_info = BITMAPINFO::default();
        bitmap_info.bmiHeader = BITMAPINFOHEADER {
            biSize: size_of::<BITMAPINFOHEADER>() as u32,
            biWidth: size as i32,
            biHeight: -(size as i32),
            biPlanes: 1,
            biBitCount: 32,
            biCompression: BI_RGB.0,
            ..Default::default()
        };
        let mut bits = std::ptr::null_mut();
        let bitmap = match CreateDIBSection(
            dc,
            &bitmap_info,
            DIB_RGB_COLORS,
            &mut bits,
            None,
            0,
        ) {
            Ok(bitmap) => bitmap,
            Err(_) => {
                let _ = DeleteDC(dc);
                return None;
            }
        };
        let old_bitmap = SelectObject(dc, bitmap);
        let byte_count = size * size * 4;
        std::ptr::write_bytes(bits, 0, byte_count);
        let drawn = DrawIconEx(
            dc,
            0,
            0,
            HICON(icon as *mut c_void),
            size as i32,
            size as i32,
            0,
            None,
            DI_NORMAL,
        )
        .is_ok();

        let image = if drawn {
            let bgra = std::slice::from_raw_parts(bits as *const u8, byte_count);
            let mut rgba = Vec::with_capacity(byte_count);
            for pixel in bgra.chunks_exact(4) {
                let alpha = if pixel[3] == 0 && (pixel[0] != 0 || pixel[1] != 0 || pixel[2] != 0)
                {
                    255
                } else {
                    pixel[3]
                };
                rgba.extend_from_slice(&[pixel[2], pixel[1], pixel[0], alpha]);
            }
            Some(ColorImage::from_rgba_unmultiplied([size, size], &rgba))
        } else {
            None
        };
        let _ = SelectObject(dc, old_bitmap);
        let _ = DeleteObject(bitmap);
        let _ = DeleteDC(dc);
        image
    }
}

#[cfg(not(target_os = "windows"))]
fn window_icon_image(_handle: isize, _size: usize) -> Option<ColorImage> {
    None
}

#[cfg(target_os = "windows")]
fn shell_icon_image(path: &Path, size: usize) -> Option<ColorImage> {
    use std::os::windows::ffi::OsStrExt;
    use windows::Win32::{
        Graphics::Gdi::{
            BI_RGB, BITMAPINFO, BITMAPINFOHEADER, CreateCompatibleDC, CreateDIBSection,
            DIB_RGB_COLORS, DeleteDC, DeleteObject, SelectObject,
        },
        Storage::FileSystem::{FILE_ATTRIBUTE_NORMAL, FILE_FLAGS_AND_ATTRIBUTES},
        System::Com::{CoTaskMemFree, IBindCtx},
        UI::{
            Shell::{
                Common::ITEMIDLIST, SHFILEINFOW, SHGFI_ICON, SHGFI_PIDL, SHGFI_SMALLICON,
                SHGFI_USEFILEATTRIBUTES, SHGetFileInfoW, SHParseDisplayName,
            },
            WindowsAndMessaging::{DI_NORMAL, DestroyIcon, DrawIconEx},
        },
    };
    use windows::core::{PCWSTR, w};

    if size == 0 {
        return None;
    }
    let wide = path
        .as_os_str()
        .encode_wide()
        .chain(std::iter::once(0))
        .collect::<Vec<_>>();
    let mut info = SHFILEINFOW::default();
    let shell_app = path
        .to_string_lossy()
        .to_ascii_lowercase()
        .starts_with("shell:appsfolder\\");
    let mut result = unsafe {
        if shell_app {
            // Packaged/UWP applications are Shell namespace objects rather than
            // filesystem paths. Resolve their parsing name to a PIDL before asking
            // the Shell for the registered application icon.
            let mut pidl = std::ptr::null_mut::<ITEMIDLIST>();
            let parsed = SHParseDisplayName(
                PCWSTR(wide.as_ptr()),
                None::<&IBindCtx>,
                &mut pidl,
                0,
                None,
            )
            .is_ok();
            let result = if parsed && !pidl.is_null() {
                SHGetFileInfoW(
                    PCWSTR(pidl.cast()),
                    FILE_FLAGS_AND_ATTRIBUTES(0),
                    Some(&mut info),
                    size_of::<SHFILEINFOW>() as u32,
                    SHGFI_PIDL | SHGFI_ICON | SHGFI_SMALLICON,
                )
            } else {
                0
            };
            CoTaskMemFree((!pidl.is_null()).then_some(pidl.cast()));
            result
        } else {
            SHGetFileInfoW(
                PCWSTR(wide.as_ptr()),
                FILE_FLAGS_AND_ATTRIBUTES(0),
                Some(&mut info),
                size_of::<SHFILEINFOW>() as u32,
                SHGFI_ICON | SHGFI_SMALLICON,
            )
        }
    };

    let executable_like = shell_app
        || path
            .extension()
            .and_then(|extension| extension.to_str())
            .is_some_and(|extension| {
                matches!(
                    extension.to_ascii_lowercase().as_str(),
                    "exe" | "lnk" | "url" | "msi" | "msc"
                )
            });
    if (result == 0 || info.hIcon.is_invalid()) && executable_like {
        // Keep applications visually distinct even when the package or shortcut
        // does not publish an icon that the Shell can extract.
        info = SHFILEINFOW::default();
        result = unsafe {
            SHGetFileInfoW(
                w!("overbar-default.exe"),
                FILE_ATTRIBUTE_NORMAL,
                Some(&mut info),
                size_of::<SHFILEINFOW>() as u32,
                SHGFI_USEFILEATTRIBUTES | SHGFI_ICON | SHGFI_SMALLICON,
            )
        };
    }
    if result == 0 || info.hIcon.is_invalid() {
        return None;
    }

    let image = unsafe {
        let dc = CreateCompatibleDC(None);
        if dc.is_invalid() {
            let _ = DestroyIcon(info.hIcon);
            return None;
        }
        let mut bitmap_info = BITMAPINFO::default();
        bitmap_info.bmiHeader = BITMAPINFOHEADER {
            biSize: size_of::<BITMAPINFOHEADER>() as u32,
            biWidth: size as i32,
            biHeight: -(size as i32),
            biPlanes: 1,
            biBitCount: 32,
            biCompression: BI_RGB.0,
            ..Default::default()
        };
        let mut bits = std::ptr::null_mut();
        let bitmap = match CreateDIBSection(
            dc,
            &bitmap_info,
            DIB_RGB_COLORS,
            &mut bits,
            None,
            0,
        ) {
            Ok(bitmap) => bitmap,
            Err(_) => {
                let _ = DeleteDC(dc);
                let _ = DestroyIcon(info.hIcon);
                return None;
            }
        };
        let old_bitmap = SelectObject(dc, bitmap);
        let byte_count = size * size * 4;
        std::ptr::write_bytes(bits, 0, byte_count);
        let drawn = DrawIconEx(
            dc,
            0,
            0,
            info.hIcon,
            size as i32,
            size as i32,
            0,
            None,
            DI_NORMAL,
        )
        .is_ok();
        let image = if drawn {
            let bgra = std::slice::from_raw_parts(bits as *const u8, byte_count);
            let mut rgba = Vec::with_capacity(byte_count);
            for pixel in bgra.chunks_exact(4) {
                let alpha = if pixel[3] == 0 && (pixel[0] != 0 || pixel[1] != 0 || pixel[2] != 0)
                {
                    255
                } else {
                    pixel[3]
                };
                rgba.extend_from_slice(&[pixel[2], pixel[1], pixel[0], alpha]);
            }
            Some(ColorImage::from_rgba_unmultiplied([size, size], &rgba))
        } else {
            None
        };
        let _ = SelectObject(dc, old_bitmap);
        let _ = DeleteObject(bitmap);
        let _ = DeleteDC(dc);
        let _ = DestroyIcon(info.hIcon);
        image
    };
    image
}

#[cfg(not(target_os = "windows"))]
fn shell_icon_image(_path: &Path, _size: usize) -> Option<ColorImage> {
    None
}

#[cfg(target_os = "windows")]
pub(crate) static SEARCH_INPUT_ACTIVE: AtomicBool = AtomicBool::new(false);
#[cfg(target_os = "windows")]
static SEARCH_PREVIOUS_FOREGROUND: std::sync::atomic::AtomicIsize =
    std::sync::atomic::AtomicIsize::new(0);

#[cfg(target_os = "windows")]
fn configure_windows_overlay(cc: &eframe::CreationContext<'_>) {
    use raw_window_handle::{HasWindowHandle, RawWindowHandle};
    use std::ffi::c_void;
    use windows::Win32::Foundation::HWND;

    let Ok(handle) = cc.window_handle() else {
        return;
    };
    let RawWindowHandle::Win32(handle) = handle.as_raw() else {
        return;
    };
    let hwnd = HWND(handle.hwnd.get() as *mut c_void);
    if !configure_overlay_hwnd(hwnd, 1) {
        record_startup_event("main bar native overlay configuration was incomplete");
    }
}

#[cfg(target_os = "windows")]
fn configure_named_overlay(title: &str, subclass_id: usize) {
    use windows::{
        Win32::UI::WindowsAndMessaging::{FindWindowW, GetPropW},
        core::{PCWSTR, w},
    };

    let wide_title = title
        .encode_utf16()
        .chain(std::iter::once(0))
        .collect::<Vec<_>>();
    let Ok(hwnd) = (unsafe { FindWindowW(None, PCWSTR(wide_title.as_ptr())) }) else {
        return;
    };
    // A window property belongs to the HWND itself and disappears when that HWND
    // is destroyed. Unlike a process-wide boolean this therefore handles eframe
    // viewport recreation and numeric handle reuse without GetWindowSubclass,
    // which is not exported by comctl32 on every supported Windows installation.
    let configured = unsafe { GetPropW(hwnd, w!("OverbarOverlayConfigured")) };
    if configured.0 as usize == subclass_id {
        return;
    }
    if !configure_overlay_hwnd(hwnd, subclass_id) {
        record_startup_event(&format!(
            "overlay configuration incomplete: title={title:?} hwnd=0x{:x} subclass={subclass_id}",
            hwnd.0 as usize,
        ));
    }
}

#[cfg(target_os = "windows")]
fn configure_windows_panel_overlay() {
    configure_named_overlay("Overbar System Panel", 2);
}

#[cfg(not(target_os = "windows"))]
fn configure_windows_panel_overlay() {}

#[cfg(target_os = "windows")]
fn configure_windows_apps_overlay() {
    configure_named_overlay("Overbar Apps Panel", 3);
}

#[cfg(not(target_os = "windows"))]
fn configure_windows_apps_overlay() {}

#[cfg(target_os = "windows")]
fn configure_windows_power_overlay() {
    configure_named_overlay("Overbar Power Menu", 6);
}

#[cfg(not(target_os = "windows"))]
fn configure_windows_power_overlay() {}

#[cfg(target_os = "windows")]
fn configure_windows_wm_settings_overlay() {
    configure_named_overlay("Overbar WM Settings", 5);
}

#[cfg(target_os = "windows")]
fn reset_windows_wm_settings_overlay() {}

#[cfg(not(target_os = "windows"))]
fn configure_windows_wm_settings_overlay() {}

#[cfg(not(target_os = "windows"))]
fn reset_windows_wm_settings_overlay() {}

#[cfg(target_os = "windows")]
fn configure_windows_search_overlay() {
    configure_named_overlay("Overbar Search Panel", 4);
}

#[cfg(not(target_os = "windows"))]
fn configure_windows_search_overlay() {}

#[cfg(target_os = "windows")]
fn refresh_windows_bar_blur() {
    // Blur is persistent HWND state and the compositor updates the pixels behind
    // it automatically. Reapplying the accent policy plus DwmFlush on every
    // foreground event caused the search-focus flash and could stall animation.
}

#[cfg(not(target_os = "windows"))]
fn refresh_windows_bar_blur() {}

#[cfg(target_os = "windows")]
fn set_windows_overlay_topmost(title: &str, topmost: bool) {
    use windows::{
        Win32::UI::WindowsAndMessaging::{
            FindWindowW, GWL_EXSTYLE, GetWindowLongPtrW, HWND_NOTOPMOST, HWND_TOPMOST,
            SWP_NOACTIVATE, SWP_NOMOVE, SWP_NOSIZE, SetWindowPos, WS_EX_TOPMOST,
        },
        core::PCWSTR,
    };

    let title = title
        .encode_utf16()
        .chain(std::iter::once(0))
        .collect::<Vec<_>>();
    if let Ok(hwnd) = unsafe { FindWindowW(None, PCWSTR(title.as_ptr())) } {
        let ex_style = unsafe { GetWindowLongPtrW(hwnd, GWL_EXSTYLE) } as u32;
        let is_topmost = ex_style & WS_EX_TOPMOST.0 != 0;
        if is_topmost == topmost {
            return;
        }
        unsafe {
            let _ = SetWindowPos(
                hwnd,
                if topmost { HWND_TOPMOST } else { HWND_NOTOPMOST },
                0,
                0,
                0,
                0,
                SWP_NOACTIVATE | SWP_NOMOVE | SWP_NOSIZE,
            );
        }
    }
}

#[cfg(not(target_os = "windows"))]
fn set_windows_overlay_topmost(_title: &str, _topmost: bool) {}

#[cfg(target_os = "windows")]
fn ensure_windows_overlay_topmost(title: &str) {
    set_windows_overlay_topmost(title, true);
}

#[cfg(not(target_os = "windows"))]
fn ensure_windows_overlay_topmost(_title: &str) {}

#[cfg(target_os = "windows")]
fn set_search_keyboard_focus(active: bool, restore_previous_focus: bool) -> bool {
    use windows::{
        Win32::{
            Foundation::HWND,
            UI::{
                Input::KeyboardAndMouse::{GetFocus, SetActiveWindow, SetFocus},
                WindowsAndMessaging::{FindWindowW, GetForegroundWindow, SetForegroundWindow},
            },
        },
        core::w,
    };

    let Ok(hwnd) = (unsafe { FindWindowW(None, w!("Overbar")) }) else {
        return false;
    };
    if active {
        let previous = unsafe { GetForegroundWindow() };
        let starting_session = !SEARCH_INPUT_ACTIVE.swap(true, Ordering::AcqRel);
        if starting_session && previous != hwnd {
            SEARCH_PREVIOUS_FOREGROUND.store(previous.0 as isize, Ordering::Release);
        }

        // Use real window activation rather than an AttachThreadInput+SetFocus
        // trick. The trick could silently fail against protected/elevated
        // foreground apps (e.g. the Settings app's UWP host), and even when it
        // succeeded, winit never saw a WM_ACTIVATE for this window, so egui's
        // own "viewport focused" flag stayed false and the text cursor never
        // blinked. Full activation is safe now: the one-frame non-client
        // repaint flash this used to cause is independently suppressed by
        // forcing WM_NCACTIVATE's lParam to -1 in overlay_window_proc.
        unsafe {
            let _ = SetForegroundWindow(hwnd);
            let _ = SetActiveWindow(hwnd);
            let _ = SetFocus(hwnd);
            GetFocus() == hwnd
        }
    } else {
        SEARCH_INPUT_ACTIVE.store(false, Ordering::Release);
        let previous = SEARCH_PREVIOUS_FOREGROUND.swap(0, Ordering::AcqRel);
        unsafe {
            if restore_previous_focus && previous != 0 {
                let previous = HWND(previous as *mut std::ffi::c_void);
                let _ = SetForegroundWindow(previous);
                let _ = SetActiveWindow(previous);
                let _ = SetFocus(previous);
            }
        }
        true
    }
}

#[cfg(not(target_os = "windows"))]
fn set_search_keyboard_focus(_active: bool, _restore_previous_focus: bool) -> bool {
    true
}

#[cfg(target_os = "windows")]
fn search_keyboard_focus_is_active() -> bool {
    use windows::{
        Win32::UI::{
            Input::KeyboardAndMouse::GetFocus,
            WindowsAndMessaging::FindWindowW,
        },
        core::w,
    };
    let Ok(hwnd) = (unsafe { FindWindowW(None, w!("Overbar")) }) else {
        return false;
    };
    unsafe { GetFocus() == hwnd }
}

#[cfg(not(target_os = "windows"))]
fn search_keyboard_focus_is_active() -> bool {
    true
}

#[cfg(target_os = "windows")]
fn overlay_dismiss_requested(
    panel_title: &str,
    trigger_rect: eframe::egui::Rect,
    scale: f32,
) -> bool {
    use windows::Win32::{
        Foundation::{POINT, RECT},
        Graphics::Gdi::ClientToScreen,
        UI::{
            Input::KeyboardAndMouse::{
                GetAsyncKeyState, VK_ESCAPE, VK_LBUTTON, VK_MBUTTON, VK_RBUTTON,
            },
            WindowsAndMessaging::{FindWindowW, GetCursorPos, GetWindowRect},
        },
    };
    use windows::core::{PCWSTR, w};

    static MOUSE_DOWN: AtomicBool = AtomicBool::new(false);
    static ESCAPE_DOWN: AtomicBool = AtomicBool::new(false);

    let key_down = |key: u16| unsafe { GetAsyncKeyState(key as i32) < 0 };
    let escape_down = key_down(VK_ESCAPE.0);
    let escape_was_down = ESCAPE_DOWN.swap(escape_down, Ordering::AcqRel);
    let escape_pressed = escape_down && !escape_was_down;
    if escape_pressed {
        return true;
    }

    let mouse_down = key_down(VK_LBUTTON.0) || key_down(VK_RBUTTON.0) || key_down(VK_MBUTTON.0);
    let mouse_was_down = MOUSE_DOWN.swap(mouse_down, Ordering::AcqRel);
    let mouse_pressed = mouse_down && !mouse_was_down;
    if !mouse_pressed {
        return false;
    }

    let mut cursor = POINT::default();
    if unsafe { GetCursorPos(&mut cursor) }.is_err() {
        return false;
    }

    let panel_title = panel_title
        .encode_utf16()
        .chain(std::iter::once(0))
        .collect::<Vec<_>>();
    if let Ok(panel) = unsafe { FindWindowW(None, PCWSTR(panel_title.as_ptr())) } {
        let mut rect = RECT::default();
        if unsafe { GetWindowRect(panel, &mut rect) }.is_ok()
            && cursor.x >= rect.left
            && cursor.x < rect.right
            && cursor.y >= rect.top
            && cursor.y < rect.bottom
        {
            return false;
        }
    }

    if let Ok(bar) = unsafe { FindWindowW(None, w!("Overbar")) } {
        let mut origin = POINT::default();
        if unsafe { ClientToScreen(bar, &mut origin) }.as_bool() {
            let left = origin.x + (trigger_rect.left() * scale).round() as i32;
            let top = origin.y + (trigger_rect.top() * scale).round() as i32;
            let right = origin.x + (trigger_rect.right() * scale).round() as i32;
            let bottom = origin.y + (trigger_rect.bottom() * scale).round() as i32;
            if cursor.x >= left && cursor.x < right && cursor.y >= top && cursor.y < bottom {
                return false;
            }
        }
    }

    true
}

#[cfg(not(target_os = "windows"))]
fn overlay_dismiss_requested(
    _panel_title: &str,
    _trigger_rect: eframe::egui::Rect,
    _scale: f32,
) -> bool {
    false
}

#[cfg(target_os = "windows")]
fn configure_overlay_hwnd(
    hwnd: windows::Win32::Foundation::HWND,
    subclass_id: usize,
) -> bool {
    use std::ffi::c_void;
    use windows::Win32::{
        Foundation::{BOOL, HANDLE},
        Graphics::Dwm::{
            DWM_BB_ENABLE, DWMWA_TRANSITIONS_FORCEDISABLED, DWMWA_USE_IMMERSIVE_DARK_MODE,
            DWMWA_WINDOW_CORNER_PREFERENCE, DWMWCP_DONOTROUND, DWM_BLURBEHIND,
            DwmEnableBlurBehindWindow, DwmSetWindowAttribute,
        },
        Graphics::Gdi::{CreateRectRgn, DeleteObject, SetWindowRgn},
        System::LibraryLoader::{GetModuleHandleW, GetProcAddress},
        UI::Shell::SetWindowSubclass,
        UI::WindowsAndMessaging::{
            GWL_EXSTYLE, GetClientRect, GetWindowLongPtrW, SWP_FRAMECHANGED, SWP_NOACTIVATE,
            SWP_NOMOVE, SWP_NOSIZE, SWP_NOZORDER, SetPropW, SetWindowLongPtrW, SetWindowPos,
            WS_EX_APPWINDOW, WS_EX_NOACTIVATE, WS_EX_TOOLWINDOW,
        },
    };
    use windows::core::{PCSTR, w};

    unsafe {
        let style = GetWindowLongPtrW(hwnd, GWL_EXSTYLE) as u32;
        let overlay_style = if subclass_id == 1 || subclass_id == 5 {
            (style | WS_EX_TOOLWINDOW.0) & !(WS_EX_APPWINDOW.0 | WS_EX_NOACTIVATE.0)
        } else {
            (style | WS_EX_TOOLWINDOW.0 | WS_EX_NOACTIVATE.0) & !WS_EX_APPWINDOW.0
        };
        if overlay_style != style {
            SetWindowLongPtrW(hwnd, GWL_EXSTYLE, overlay_style as isize);
            let _ = SetWindowPos(
                hwnd,
                None,
                0,
                0,
                0,
                0,
                SWP_FRAMECHANGED | SWP_NOACTIVATE | SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER,
            );
        }
        // Enforce non-activation even if the UI backend asks Windows to focus us,
        // and skip Win32's background erase before OpenGL redraws the transparent frame.
        let subclassed = SetWindowSubclass(hwnd, Some(overlay_window_proc), subclass_id, 0)
            .as_bool();
        let marked = subclassed
            && SetPropW(
                hwnd,
                w!("OverbarOverlayConfigured"),
                HANDLE(subclass_id as *mut c_void),
            )
            .is_ok();
        remove_window_from_taskbar(hwnd);

        let dark_mode = BOOL(1);
        let transitions_disabled = BOOL(1);
        let _ = DwmSetWindowAttribute(
            hwnd,
            DWMWA_TRANSITIONS_FORCEDISABLED,
            &transitions_disabled as *const _ as *const c_void,
            size_of_val(&transitions_disabled) as u32,
        );
        let _ = DwmSetWindowAttribute(
            hwnd,
            DWMWA_USE_IMMERSIVE_DARK_MODE,
            &dark_mode as *const _ as *const c_void,
            size_of_val(&dark_mode) as u32,
        );
        let corners = DWMWCP_DONOTROUND;
        let _ = DwmSetWindowAttribute(
            hwnd,
            DWMWA_WINDOW_CORNER_PREFERENCE,
            &corners as *const _ as *const c_void,
            size_of_val(&corners) as u32,
        );

        // A rectangular region prevents Windows 11 from clipping the overlay's bottom
        // corners even when the system backdrop is enabled.
        let mut client_rect = windows::Win32::Foundation::RECT::default();
        if GetClientRect(hwnd, &mut client_rect).is_ok()
            && client_rect.right > client_rect.left
            && client_rect.bottom > client_rect.top
        {
            let region = CreateRectRgn(0, 0, client_rect.right, client_rect.bottom);
            if !region.is_invalid() {
                // Windows owns the region after a successful call.
                if SetWindowRgn(hwnd, region, true) == 0 {
                    let _ = DeleteObject(region);
                }
            }
        }

        // Request pure compositor blur with no gradient/tint color. This compositor
        // attribute is also used by established Windows vibrancy libraries.
        let policy = AccentPolicy {
            accent_state: ACCENT_ENABLE_BLUR_BEHIND,
            accent_flags: 0,
            gradient_color: 0,
            animation_id: 0,
        };
        let mut data = WindowCompositionAttributeData {
            attribute: WCA_ACCENT_POLICY,
            data: &policy as *const _ as *mut c_void,
            size: size_of_val(&policy),
        };
        let mut composition_applied = false;
        if let Ok(user32) = GetModuleHandleW(w!("user32.dll")) {
            if let Some(address) = GetProcAddress(
                user32,
                PCSTR(c"SetWindowCompositionAttribute".as_ptr().cast()),
            ) {
                let set_window_composition_attribute: SetWindowCompositionAttributeFn =
                    std::mem::transmute(address);
                composition_applied =
                    set_window_composition_attribute(hwnd, &mut data).as_bool();
            }
        }
        if !composition_applied {
            // Supported fallback for systems where the undocumented accent-policy
            // entry point is unavailable or rejected by the compositor.
            let fallback = DWM_BLURBEHIND {
                dwFlags: DWM_BB_ENABLE,
                fEnable: BOOL(1),
                ..Default::default()
            };
            composition_applied = DwmEnableBlurBehindWindow(hwnd, &fallback).is_ok();
            record_startup_event(&format!(
                "accent blur unavailable: hwnd=0x{:x} documented_fallback={composition_applied}",
                hwnd.0 as usize,
            ));
        }

        marked && composition_applied
    }
}

#[cfg(target_os = "windows")]
unsafe fn remove_window_from_taskbar(hwnd: windows::Win32::Foundation::HWND) {
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
        let _ = unsafe { taskbar.DeleteTab(hwnd) };
    }
    if initialized_here {
        unsafe { CoUninitialize() };
    }
}

#[cfg(target_os = "windows")]
const WCA_ACCENT_POLICY: i32 = 19;
#[cfg(target_os = "windows")]
const ACCENT_ENABLE_BLUR_BEHIND: i32 = 3;

#[cfg(target_os = "windows")]
#[repr(C)]
struct AccentPolicy {
    accent_state: i32,
    accent_flags: i32,
    gradient_color: u32,
    animation_id: i32,
}

#[cfg(target_os = "windows")]
#[repr(C)]
struct WindowCompositionAttributeData {
    attribute: i32,
    data: *mut std::ffi::c_void,
    size: usize,
}

#[cfg(target_os = "windows")]
unsafe extern "system" fn overlay_window_proc(
    hwnd: windows::Win32::Foundation::HWND,
    message: u32,
    wparam: windows::Win32::Foundation::WPARAM,
    lparam: windows::Win32::Foundation::LPARAM,
    subclass_id: usize,
    _reference_data: usize,
) -> windows::Win32::Foundation::LRESULT {
    use windows::Win32::{
        Foundation::{LPARAM, LRESULT, RECT},
        Graphics::Gdi::{CreateRectRgn, DeleteObject, SetWindowRgn},
        UI::{
            Shell::DefSubclassProc,
            WindowsAndMessaging::{
                GWL_EXSTYLE, GetClientRect, HTTRANSPARENT, MA_NOACTIVATE, STYLESTRUCT,
                RemovePropW, WM_ERASEBKGND, WM_MOUSEACTIVATE, WM_NCACTIVATE, WM_NCHITTEST,
                WM_NCDESTROY, WM_SIZE, WM_STYLECHANGING, WS_EX_APPWINDOW, WS_EX_NOACTIVATE,
                WS_EX_TOOLWINDOW,
            },
        },
    };
    use windows::core::w;

    match message {
        WM_NCHITTEST if subclass_id == 4 && !SEARCH_INPUT_ACTIVE.load(Ordering::Acquire) =>
        {
            LRESULT(HTTRANSPARENT as isize)
        }
        WM_MOUSEACTIVATE
            if subclass_id != 5
                && (subclass_id != 1 || !SEARCH_INPUT_ACTIVE.load(Ordering::Acquire)) =>
        {
            LRESULT(MA_NOACTIVATE as isize)
        }
        WM_ERASEBKGND => LRESULT(1),
        WM_NCDESTROY => {
            let _ = unsafe { RemovePropW(hwnd, w!("OverbarOverlayConfigured")) };
            unsafe { DefSubclassProc(hwnd, message, wparam, lparam) }
        }
        WM_NCACTIVATE => {
            // Our search-focus trick (AttachThreadInput + SetFocus) legitimately
            // activates these overlay windows without going through
            // SetForegroundWindow, but Windows still sends WM_NCACTIVATE, which by
            // default repaints the non-client area to reflect the new
            // active/inactive state. For these borderless/custom-chrome windows
            // that repaint is the visible one-frame flash. Passing lParam = -1
            // tells DefWindowProc to skip that repaint while still handling the
            // message correctly.
            unsafe { DefSubclassProc(hwnd, message, wparam, LPARAM(-1)) }
        }
        WM_STYLECHANGING if wparam.0 as i32 == GWL_EXSTYLE.0 && lparam.0 != 0 => {
            let styles = unsafe { &mut *(lparam.0 as *mut STYLESTRUCT) };
            styles.styleNew = (styles.styleNew | WS_EX_TOOLWINDOW.0) & !WS_EX_APPWINDOW.0;
            if subclass_id != 1 && subclass_id != 5 {
                styles.styleNew |= WS_EX_NOACTIVATE.0;
            } else {
                styles.styleNew &= !WS_EX_NOACTIVATE.0;
            }
            unsafe { DefSubclassProc(hwnd, message, wparam, lparam) }
        }
        WM_SIZE => {
            let mut client_rect = RECT::default();
            if unsafe { GetClientRect(hwnd, &mut client_rect).is_ok() }
                && client_rect.right > client_rect.left
                && client_rect.bottom > client_rect.top
            {
                let region = unsafe {
                    CreateRectRgn(0, 0, client_rect.right, client_rect.bottom)
                };
                if !region.is_invalid() {
                    if unsafe { SetWindowRgn(hwnd, region, true) } == 0 {
                        let _ = unsafe { DeleteObject(region) };
                    }
                }
            }
            unsafe { DefSubclassProc(hwnd, message, wparam, lparam) }
        }
        _ => unsafe { DefSubclassProc(hwnd, message, wparam, lparam) },
    }
}

#[cfg(target_os = "windows")]
type SetWindowCompositionAttributeFn = unsafe extern "system" fn(
    windows::Win32::Foundation::HWND,
    *mut WindowCompositionAttributeData,
) -> windows::Win32::Foundation::BOOL;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn long_titles_are_ellipsized() {
        assert_eq!(ellipsize_title("abcdef", 5), "abcd…");
        assert_eq!(ellipsize_title("short", 5), "short");
    }

    #[test]
    fn release_versions_are_compared_numerically() {
        assert!(release_version_is_newer("v1.2.0", "1.1.9"));
        assert!(release_version_is_newer("2.0", "1.99.99"));
        assert!(!release_version_is_newer("v1.1.1", "1.1.1"));
        assert!(!release_version_is_newer("v1.1.0", "1.1.1"));
        assert!(release_version_is_newer("v1.1.1", "1.1.1-beta.1"));
        assert!(!release_version_is_newer("latest", "1.1.1"));
        assert_eq!(
            decode_powershell_output(&[0xff, 0xfe, b'{', 0, b'}', 0]),
            "{}"
        );
        #[cfg(target_os = "windows")]
        {
            assert_eq!(
                windows_powershell_path(Path::new(
                    r"\\?\C:\Users\respite\Documents\Overbar\overbar.exe"
                )),
                PathBuf::from(r"C:\Users\respite\Documents\Overbar\overbar.exe")
            );
            assert_eq!(
                windows_powershell_path(Path::new(r"\\?\UNC\server\share\overbar.exe")),
                PathBuf::from(r"\\server\share\overbar.exe")
            );
        }
    }

    #[cfg(target_os = "windows")]
    #[test]
    #[ignore = "requires access to the GitHub Releases API"]
    fn live_github_release_response_is_compatible() {
        assert!(check_for_update().is_ok());
    }

    #[test]
    fn shell_surfaces_use_the_search_fallback() {
        assert!(is_shell_surface_title("Program Manager", "Progman", "explorer.exe"));
        assert!(is_shell_surface_title(
            "System tray overflow window",
            "TopLevelWindowForOverflowXamlIsland",
            "explorer.exe",
        ));
        assert!(is_shell_surface_title(
            "",
            "Windows.UI.Core.CoreWindow",
            "PopupHost.exe",
        ));
        assert!(is_shell_surface_title(
            "Pinned",
            "Xaml_WindowedPopupClass",
            "explorer.exe",
        ));
        assert!(is_shell_surface_title("Jump List", "Anything", "explorer.exe"));
        assert!(!is_shell_surface_title(
            "Project - Visual Studio Code",
            "Chrome_WidgetWin_1",
            "Code.exe",
        ));
        assert!(!is_shell_surface_title(
            "Downloads",
            "CabinetWClass",
            "explorer.exe",
        ));
        assert!(!is_shell_surface_title(
            "Overbar: a Windows topbar · GitHub",
            "MozillaWindowClass",
            "zen.exe",
        ));
        assert!(!is_shell_surface_title(
            "Jump List",
            "MozillaWindowClass",
            "zen.exe",
        ));
        assert!(is_transient_title_class(
            "Qt5152QWindowPopupDropShadowSaveBits"
        ));
        assert!(is_transient_title_class("TrayMenuWindow"));
        assert!(!is_transient_title_class("MozillaWindowClass"));
        assert!(is_shell_surface_title(
            "Background task",
            "Anything",
            "RuntimeBroker.exe",
        ));
        assert!(is_shell_surface_title(
            "Server",
            "Chrome_MessageWindow",
            "example.exe",
        ));
        assert!(is_shell_surface_title(
            "GDI+ Window (example.exe)",
            "Anything",
            "example.exe",
        ));
        assert!(!is_shell_surface_title(
            "Development Server - Visual Studio Code",
            "Chrome_WidgetWin_1",
            "Code.exe",
        ));
    }

    #[test]
    fn common_windows_aliases_resolve_to_apps() {
        let apps = vec![SearchEntry::new(
            "Task Manager".to_owned(),
            PathBuf::from(r"C:\Windows\System32\Taskmgr.exe"),
        )];
        let results = search_catalog("tskmgr", &apps, &[], &[]);
        assert_eq!(results.apps.len(), 1);
        assert_eq!(results.apps[0].name, "Task Manager");
    }

    #[test]
    fn repeated_queries_are_cached() {
        let apps = vec![SearchEntry::new(
            "Command Prompt".to_owned(),
            PathBuf::from(r"C:\Windows\System32\cmd.exe"),
        )];
        let mut cache = HashMap::new();
        let mut preferences = StoredSearchPreferences::default();
        let first = cached_search_catalog("cmd", &apps, &[], &[], &mut cache, &mut preferences);
        let second = cached_search_catalog("CMD", &apps, &[], &[], &mut cache, &mut preferences);
        assert_eq!(first.apps[0].name, second.apps[0].name);
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn selected_results_are_learned_for_every_query_prefix() {
        assert_eq!(search_prefixes("Zen"), ["z", "ze", "zen"]);
    }

    #[test]
    fn recent_launcher_items_are_capped_at_fifteen() {
        let mut preferences = StoredSearchPreferences::default();
        let mut cache = HashMap::new();
        for index in 0..20 {
            record_search_selection(
                "app",
                SearchEntry::new(
                    format!("App {index}"),
                    PathBuf::from(format!(r"C:\Apps\app-{index}.exe")),
                ),
                &mut preferences,
                &mut cache,
            );
        }
        assert_eq!(preferences.recents.len(), SEARCH_RECENT_LIMIT);
        assert_eq!(search_home_results(&preferences).recents.len(), SEARCH_RECENT_LIMIT);
    }

    #[test]
    fn matching_pins_are_separated_ahead_of_regular_results() {
        let pinned = SearchEntry::new("Zen Browser".to_owned(), PathBuf::from("zen.exe"));
        let regular = SearchEntry::new("Zen Notes".to_owned(), PathBuf::from("notes.exe"));
        let apps = vec![regular.clone(), pinned.clone()];
        let mut preferences = StoredSearchPreferences {
            pins: vec![pinned.clone()],
            ..Default::default()
        };
        let results = cached_search_catalog(
            "zen",
            &apps,
            &[],
            &[],
            &mut HashMap::new(),
            &mut preferences,
        );
        assert_eq!(results.pins[0].path, pinned.path);
        assert_eq!(results.apps[0].path, regular.path);
    }

    #[test]
    fn command_selections_are_learned_for_every_query_prefix() {
        let mut preferences = StoredSearchPreferences::default();
        record_command_selection("kill explorer", "explorer.exe".into(), &mut preferences);
        assert_eq!(
            preferences.command_selections.get("kill explorer"),
            Some(&"explorer.exe".to_owned())
        );
        assert_eq!(
            preferences.command_selections.get("k"),
            Some(&"explorer.exe".to_owned())
        );
    }

    #[test]
    fn scientific_calculator_handles_precedence_functions_and_constants() {
        assert_eq!(calculator_result("2 + 3 * 4"), Some("14".into()));
        assert_eq!(calculator_result("sin(pi / 2)"), Some("1".into()));
        assert_eq!(calculator_result("sqrt(81) + 3!"), Some("15".into()));
        assert_eq!(calculator_result("2pi"), Some("6.28318530718".into()));
    }

    #[test]
    fn calculator_supports_scientific_helpers() {
        assert_eq!(calculator_result("log(1000)"), Some("3".into()));
        assert_eq!(calculator_result("ncr(10, 3)"), Some("120".into()));
        assert_eq!(calculator_result("round(1 / 3, 4)"), Some("0.3333".into()));
        assert_eq!(calculator_result("not a calculation"), None);
    }

    #[test]
    fn launcher_resolves_power_and_settings_commands() {
        assert!(matches!(
            launcher_command("hibernate").map(|command| command.action),
            Some(LauncherCommandAction::Power(PowerAction::Hibernate))
        ));
        assert!(matches!(
            launcher_command("bluetooth").map(|command| command.action),
            Some(LauncherCommandAction::OpenTarget(target))
                if target == "ms-settings:bluetooth"
        ));
    }

    #[test]
    fn question_mark_queries_become_web_searches() {
        assert!(matches!(
            launcher_command("? best mechanical keyboards").map(|command| command.action),
            Some(LauncherCommandAction::WebSearch(query))
                if query == "best mechanical keyboards"
        ));
        assert_eq!(
            percent_encode_query("75% keyboard + quiet"),
            "75%25+keyboard+%2B+quiet"
        );
    }

    #[test]
    fn launcher_commands_do_not_return_local_search_results() {
        let apps = vec![SearchEntry::new(
            "Bluetooth Utility".to_owned(),
            PathBuf::from("bluetooth.exe"),
        )];
        let results = search_catalog("bluetooth", &apps, &[], &[]);
        assert!(results.apps.is_empty());
        assert!(results.files.is_empty());
    }
}
