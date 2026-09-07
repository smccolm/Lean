# Visualization Suite

This directory contains exploratory visualizations used alongside the mathematical projects. It is not part of any Lean proof or verification gate.

- `dashboard.html`: self-contained interactive WebGL dashboard.
- `visualizer.py`: Python visualization entry point.
- `server.py`: small local HTTP server for browser access.

Run the Python entry point from the workspace root:

```powershell
python visualizer/visualizer.py
```

Or serve the browser assets locally:

```powershell
python visualizer/server.py
```
