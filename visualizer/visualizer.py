"""
===============================================================================
Animated Visualization Engine for Compacted Graphs & Riemann Zeta Trajectories
===============================================================================
Author: Antigravity AI Pair Programmer
Project: Lean / Compacted Graphs

Provides animated 3D and 2D interactive WebGL visualization engines using 
Plotly, NumPy, and mpmath. Generates interactive HTML dashboards with sleek HTML 
control buttons, timeline sliders, and auto-launches them in your browser.
"""

import os
import sys
import webbrowser
import numpy as np
import mpmath
import plotly.graph_objects as go
from plotly.subplots import make_subplots

# Pre-computed known first 10 non-trivial zeros on the critical line t
KNOWN_ZEROS = [
    14.13472514, 21.02203964, 25.01085758, 30.42487613, 32.93506159,
    37.58617815, 40.91871901, 43.32707328, 48.00515088, 49.77383248
]

class CompactedGraphsVisualizer:
    """Engine for generating animated 3D cylindrical, compactified torus, and Riemann Zeta visualizations."""

    def __init__(self, output_dir: str = None):
        if output_dir is None:
            self.output_dir = os.path.dirname(os.path.abspath(__file__))
        else:
            self.output_dir = output_dir
        os.makedirs(self.output_dir, exist_ok=True)

    def generate_cylindrical_compactified_fig(self, num_points=600):
        """Generates 3D cylindrical spiral and compactified torus projection with animation frames."""
        theta = np.linspace(0, 4 * np.pi, num_points)
        r = 1 + 0.3 * np.sin(3 * theta)
        z = theta

        # 3D Cylindrical Cartesian
        x_cyl = r * np.cos(theta)
        y_cyl = r * np.sin(theta)
        z_cyl = z

        # Torus Compactification S¹ x S¹
        R_torus = 3.0
        r_torus = r
        x_torus = (R_torus + r_torus * np.cos(z)) * np.cos(theta)
        y_torus = (R_torus + r_torus * np.cos(z)) * np.sin(theta)
        z_torus = r_torus * np.sin(z)

        fig = make_subplots(
            rows=1, cols=2,
            specs=[[{'type': 'scene'}, {'type': 'scene'}]],
            subplot_titles=[
                "Uncompactified 3D Cylindrical Spiral (r(θ), θ, z)",
                "Compacted Graph on Torus S¹ × S¹ (Closed Loops)"
            ]
        )

        # Initial Full Curves
        fig.add_trace(
            go.Scatter3d(
                x=x_cyl, y=y_cyl, z=z_cyl,
                mode='lines+markers',
                line=dict(color='#00e5ff', width=5),
                marker=dict(size=2, color=z_cyl, colorscale='Viridis'),
                name='Cylindrical Spiral'
            ),
            row=1, col=1
        )

        fig.add_trace(
            go.Scatter3d(
                x=x_torus, y=y_torus, z=z_torus,
                mode='lines+markers',
                line=dict(color='#ff4081', width=6),
                marker=dict(size=2, color=theta, colorscale='Plasma'),
                name='Compacted Loop S¹'
            ),
            row=1, col=2
        )

        # Torus wireframe mesh background
        u_mesh = np.linspace(0, 2*np.pi, 25)
        v_mesh = np.linspace(0, 2*np.pi, 25)
        U, V = np.meshgrid(u_mesh, v_mesh)
        X_mesh = (R_torus + 1.0 * np.cos(V)) * np.cos(U)
        Y_mesh = (R_torus + 1.0 * np.cos(V)) * np.sin(U)
        Z_mesh = 1.0 * np.sin(V)

        fig.add_trace(
            go.Surface(
                x=X_mesh, y=Y_mesh, z=Z_mesh,
                opacity=0.15,
                showscale=False,
                colorscale='Greys',
                name='Torus Surface'
            ),
            row=1, col=2
        )

        # Animation Frames: Tracing progress over time steps
        step_indices = np.linspace(20, num_points, 40, dtype=int)
        frames = []
        for idx in step_indices:
            frame_data = [
                go.Scatter3d(
                    x=x_cyl[:idx], y=y_cyl[:idx], z=z_cyl[:idx],
                    mode='lines+markers',
                    line=dict(color='#00e5ff', width=6),
                    marker=dict(size=3, color=z_cyl[:idx], colorscale='Viridis')
                ),
                go.Scatter3d(
                    x=x_torus[:idx], y=y_torus[:idx], z=z_torus[:idx],
                    mode='lines+markers',
                    line=dict(color='#ff4081', width=7),
                    marker=dict(size=3, color=theta[:idx], colorscale='Plasma')
                )
            ]
            frames.append(go.Frame(data=frame_data, name=f"frame_{idx}"))

        fig.frames = frames

        fig.update_layout(
            template="plotly_dark",
            title="<b>Cylindrical Graph Compactification Engine</b>",
            height=620,
            margin=dict(l=30, r=30, b=80, t=80),
            legend=dict(
                orientation="h",
                yanchor="top",
                y=-0.08,
                xanchor="center",
                x=0.5
            )
        )

        return fig

    def generate_zeta_fig(self, t_min=0.0, t_max=40.0, num_points=600):
        """Computes and visualizes the Riemann Zeta trajectory on the critical line s = 1/2 + it with animation."""
        t_vals = np.linspace(t_min, t_max, num_points)
        
        zeta_vals = []
        for t in t_vals:
            z_val = complex(mpmath.zeta(0.5 + 1j * t))
            zeta_vals.append(z_val)
        
        zeta_vals = np.array(zeta_vals)
        re_zeta = np.real(zeta_vals)
        im_zeta = np.imag(zeta_vals)

        zeros_in_range = [z for z in KNOWN_ZEROS if t_min <= z <= t_max]

        fig = make_subplots(
            rows=1, cols=2,
            specs=[[{'type': 'scene'}, {'type': 'xy'}]],
            subplot_titles=[
                "3D Trajectory (t, Re(ζ), Im(ζ)) & Zeros",
                "2D Complex Plane Projection: ζ(1/2 + it)"
            ]
        )

        # 1. Full 3D Zeta Trajectory Line & Markers
        fig.add_trace(
            go.Scatter3d(
                x=re_zeta, y=im_zeta, z=t_vals,
                mode='lines+markers',
                line=dict(color='#00e5ff', width=4),
                marker=dict(size=3, color=t_vals, colorscale='Turbo', showscale=False),
                name='ζ(1/2 + it) 3D Spiral'
            ),
            row=1, col=1
        )

        # Central axis line (r = 0)
        fig.add_trace(
            go.Scatter3d(
                x=np.zeros_like(t_vals), y=np.zeros_like(t_vals), z=t_vals,
                mode='lines',
                line=dict(color='#ffffff', width=2, dash='dash'),
                name='Zero Axis (r = 0)'
            ),
            row=1, col=1
        )

        # Highlight Nontrivial Zeros in 3D
        if zeros_in_range:
            fig.add_trace(
                go.Scatter3d(
                    x=[0]*len(zeros_in_range),
                    y=[0]*len(zeros_in_range),
                    z=zeros_in_range,
                    mode='markers+text',
                    marker=dict(size=9, color='#ff1744', symbol='diamond'),
                    text=[f"  Zero t={z:.2f}" for z in zeros_in_range],
                    textposition="top right",
                    name='Nontrivial Zeros (r=0)'
                ),
                row=1, col=1
            )

        # 2. Full 2D Projection on Complex Plane
        fig.add_trace(
            go.Scatter(
                x=re_zeta, y=im_zeta,
                mode='lines+markers',
                line=dict(color='#00e5ff', width=2.5),
                marker=dict(
                    size=4, 
                    color=t_vals, 
                    colorscale='Turbo', 
                    showscale=True, 
                    colorbar=dict(
                        title=dict(text="t", side="top"),
                        x=1.02,
                        len=0.8,
                        y=0.5
                    )
                ),
                hovertemplate="Re: %{x:.3f}<br>Im: %{y:.3f}<extra></extra>",
                name='Complex Loops'
            ),
            row=1, col=2
        )

        # Origin Marker (0,0)
        fig.add_trace(
            go.Scatter(
                x=[0], y=[0],
                mode='markers',
                marker=dict(size=14, color='#ff1744', symbol='cross'),
                name='Origin (Zero Point)'
            ),
            row=1, col=2
        )

        # Build Animation Frames: Real-time tracing of trajectory along t
        step_indices = np.linspace(20, num_points, 45, dtype=int)
        frames = []
        for idx in step_indices:
            current_t = t_vals[idx-1]
            frame_data = [
                go.Scatter3d(
                    x=re_zeta[:idx], y=im_zeta[:idx], z=t_vals[:idx],
                    mode='lines+markers',
                    line=dict(color='#00e5ff', width=5),
                    marker=dict(size=3, color=t_vals[:idx], colorscale='Turbo')
                ),
                go.Scatter3d(
                    x=np.zeros(idx), y=np.zeros(idx), z=t_vals[:idx],
                    mode='lines',
                    line=dict(color='#ffffff', width=2, dash='dash')
                ),
                go.Scatter3d(
                    x=[0]*len([z for z in zeros_in_range if z <= current_t]),
                    y=[0]*len([z for z in zeros_in_range if z <= current_t]),
                    z=[z for z in zeros_in_range if z <= current_t],
                    mode='markers+text',
                    marker=dict(size=9, color='#ff1744', symbol='diamond'),
                    text=[f"  Zero t={z:.2f}" for z in zeros_in_range if z <= current_t],
                    textposition="top right"
                ),
                go.Scatter(
                    x=re_zeta[:idx], y=im_zeta[:idx],
                    mode='lines+markers',
                    line=dict(color='#00e5ff', width=3),
                    marker=dict(size=4, color=t_vals[:idx], colorscale='Turbo')
                )
            ]
            frames.append(go.Frame(data=frame_data, name=f"frame_{idx}"))

        fig.frames = frames

        fig.update_layout(
            template="plotly_dark",
            title="<b>Riemann Zeta Critical Line Trajectory & Nontrivial Zeros</b>",
            height=620,
            margin=dict(l=30, r=40, b=80, t=80),
            legend=dict(
                orientation="h",
                yanchor="top",
                y=-0.08,
                xanchor="center",
                x=0.5
            )
        )
        fig.update_xaxes(title_text="Re(ζ)", row=1, col=2, gridcolor='#333333')
        fig.update_yaxes(title_text="Im(ζ)", row=1, col=2, gridcolor='#333333')

        return fig

    def build_and_launch_dashboard(self, html_filename="dashboard.html", auto_open=True):
        """Combines all interactive animated figures into a single HTML dashboard and opens it."""
        fig_cyl = self.generate_cylindrical_compactified_fig()
        fig_zeta = self.generate_zeta_fig()

        html_path = os.path.join(self.output_dir, html_filename)

        html_content = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <title>Compacted Graphs & Riemann Zeta Animated Explorer</title>
    <script src="https://cdn.plot.ly/plotly-latest.min.js"></script>
    <style>
        body {{
            background-color: #0b0c10;
            color: #e0e0e0;
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            margin: 0;
            padding: 20px;
        }}
        h1 {{
            text-align: center;
            color: #66fcf1;
            margin-bottom: 5px;
        }}
        p.subtitle {{
            text-align: center;
            color: #c5c6c7;
            margin-top: 0;
            margin-bottom: 25px;
        }}
        .card {{
            background: #1f2833;
            border-radius: 12px;
            padding: 20px;
            margin-bottom: 30px;
            box-shadow: 0 8px 20px rgba(0,0,0,0.6);
            border: 1px solid #45a29e;
        }}
        .card-header {{
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 10px;
            padding-bottom: 10px;
            border-bottom: 1px solid #333340;
        }}
        .card-title {{
            font-size: 1.2rem;
            font-weight: bold;
            color: #66fcf1;
        }}
        .btn-group {{
            display: flex;
            gap: 10px;
        }}
        .btn {{
            background: #45a29e;
            color: #0b0c10;
            border: none;
            padding: 8px 16px;
            border-radius: 6px;
            font-weight: bold;
            cursor: pointer;
            transition: all 0.2s ease;
        }}
        .btn:hover {{
            background: #66fcf1;
            transform: translateY(-1px);
        }}
        .btn-secondary {{
            background: #333340;
            color: #e0e0e0;
        }}
        .btn-secondary:hover {{
            background: #555566;
        }}
        .plot-container {{
            width: 100%;
            height: 620px;
        }}
    </style>
</head>
<body>
    <h1>Compacted Graphs & Riemann Zeta Animated Explorer</h1>
    <p class="subtitle">Interactive 3D Trajectory Tracing, Compactification & Critical Line Loops | Antigravity AI Suite</p>

    <div class="card">
        <div class="card-header">
            <div class="card-title">🌀 3D Cylindrical Graph Compactification Engine</div>
            <div class="btn-group">
                <button class="btn" onclick="playPlot('cylindrical-plot')">▶ Play Animation</button>
                <button class="btn btn-secondary" onclick="pausePlot('cylindrical-plot')">⏸ Pause</button>
            </div>
        </div>
        <div id="cylindrical-plot" class="plot-container"></div>
    </div>

    <div class="card">
        <div class="card-header">
            <div class="card-title">✨ Riemann Zeta Critical Line Trajectory & Nontrivial Zeros</div>
            <div class="btn-group">
                <button class="btn" onclick="playPlot('zeta-plot')">▶ Trace Trajectory (Play)</button>
                <button class="btn btn-secondary" onclick="pausePlot('zeta-plot')">⏸ Pause</button>
            </div>
        </div>
        <div id="zeta-plot" class="plot-container"></div>
    </div>

    <script>
        var figCyl = {fig_cyl.to_json()};
        var figZeta = {fig_zeta.to_json()};

        Plotly.newPlot('cylindrical-plot', figCyl.data, figCyl.layout, {{responsive: true}}).then(function() {{
            Plotly.addFrames('cylindrical-plot', figCyl.frames);
        }});
        
        Plotly.newPlot('zeta-plot', figZeta.data, figZeta.layout, {{responsive: true}}).then(function() {{
            Plotly.addFrames('zeta-plot', figZeta.frames);
        }});

        function playPlot(divId) {{
            Plotly.animate(divId, null, {{
                frame: {{duration: 80, redraw: true}},
                fromcurrent: true,
                transition: {{duration: 40}}
            }});
        }}

        function pausePlot(divId) {{
            Plotly.animate(divId, [], {{
                mode: 'immediate',
                frame: {{duration: 0, redraw: false}}
            }});
        }}
    </script>
</body>
</html>
"""
        with open(html_path, "w", encoding="utf-8") as f:
            f.write(html_content)

        print(f"[Visualizer] Dashboard saved to: {html_path}")

        if auto_open:
            webbrowser.open(f"file:///{html_path}")

        return html_path

if __name__ == "__main__":
    viz = CompactedGraphsVisualizer()
    path = viz.build_and_launch_dashboard(auto_open=True)
    print(f"Successfully launched animated visualizer at: {path}")
