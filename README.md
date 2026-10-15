# Overbar
<img width="1920" height="1199" alt="image" src="https://github.com/user-attachments/assets/79754e03-0d45-4e00-a539-34fa933e76d8" />


A lightweight native Windows topbar and tiling window manager written in Rust.

(this is completely vibecoded i made this for myself lol)

## Features

- native, event-driven Windows workspace manager
- dynamic workspaces, tiling, floating windows, workspace moves, focus, and pause mode
- native Windows acrylic blur
- live CPU/RAM/temperature (if supported), battery, storage, network, task, volume, and clock panels
- app launcher and indexed search
- cool topbar :3

## Window-manager bindings

| Binding | Action |
| --- | --- |
| `Alt+1` … `Alt+9` | Focus workspace |
| `Alt+Shift+1` … `Alt+Shift+9` | Move focused window to workspace |
| `Alt+H/J/K/L` or `Alt+Arrow` | Focus in a direction |
| `Alt+Shift+H/J/K/L` or `Alt+Shift+Arrow` | Move the focused window in the layout |
| `Alt+U/P` | Decrease / increase width by 2% |
| `Alt+I/O` | Decrease / increase height by 2% |
| `Alt+R` | Enter resize mode; use H/J/K/L or arrows, then Enter/Escape |
| `Alt+V` | Toggle horizontal / vertical tiling |
| `Alt+Shift+Space` | Cycle tiled / floating for the focused window |
| `Alt+T` | Set tiled: floating windows become tiled, tiled windows are retiled in place |
| `Alt+F` | Toggle fullscreen |
| `Alt+M` | Toggle minimized |
| `Alt+Shift+Q` | Close the focused window |
| `Alt+A` / `Alt+S` | Focus previous / next active workspace |
| `Alt+D` | Focus the previously active workspace |
| `Alt+Shift+A/F/D/S` | Move the active workspace to the left/right/up/down monitor |
| `Alt+Shift+P` | Pause / resume automatic tiling |
| `Alt+Shift+W` | Redraw the active workspace |
| `Alt+Shift+R` | Reload/redraw manager state |
| `Alt+Shift+E` | Exit Overbar and restore managed windows |

The workspace buttons and tiling-direction icon expose the same actions through the bar.

## Launcher commands

- Power/session: `lock`, `sleep`, `hibernate`, `shutdown`, `restart`, `sign out`, `quit`
- Folders: `downloads`, `documents`, `desktop`, `pictures`, `screenshots`, `music`, `videos`, `startup`, `temp`, `appdata`, `localappdata`, `programdata`, `windows`, `system32`, `fonts`, `recycle bin`, `all apps`
- Settings: `bluetooth`, `wifi`, `network`, `display`, `sound`, `apps`, `updates`, `notifications`, `storage`, `personalization`, `privacy`, `power settings`, `default apps`, `date and time`
- Web: prefix a query with `?`, such as `? best mechanical keyboards`; a web result also appears when no local results match

## Run

```powershell
cargo run --release
```

Overbar requests administrator elevation when it starts so its window manager can
tile and focus elevated applications such as Task Manager. If the UAC prompt is
declined, the bar continues to run but Windows will block control of elevated windows.
The Window Manager Settings panel can create or refresh an `Overbar Startup`
Scheduled Task that launches the current executable at sign-in with highest
privileges, avoiding subsequent UAC prompts.

## Build

```powershell
cargo build --release
```
