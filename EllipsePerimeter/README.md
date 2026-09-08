# EllipsePerimeter

This is the canonical Lean 4 ellipse-perimeter formalization. The complete proof formerly developed under the `EllipseLab` project name now lives here under the stable `EllipsePerimeter` package name.

The principal result is:

```lean
EllipseOmega.ellipse_perimeter_series
```

`EllipsePerimeter/Shape.lean` connects the full-loop parametric arc length to the complete elliptic integral, proves the open-interval series, handles the degenerate endpoint, and states the symmetric result for nonnegative semiaxes. `EllipsePerimeter.lean` is the package root and imports the complete proof.

## Build

From this directory:

```powershell
lake build
```

A successful build verifies the complete geometric perimeter theorem and its supporting declarations.

## Papers and history

- `paper/` contains the associated manuscripts and Word artifacts.
- `archive/development-history/` preserves the numbered intermediate proof states outside the production Lean namespace.
- `archive/early-extraction/` preserves the useful source from the older partial `EllipsePerimeter` extraction as inert `.lean.txt` records.

The archived files are historical evidence, not imported Lean modules.
