# EllipseLab

This is the current complete Lean 4 ellipse-perimeter formalization. Despite the historical “Lab” name, the package root imports the integrated proof in `EllipseLab/Shape.lean`.

The principal result is:

```lean
EllipseOmega.ellipse_perimeter_series
```

It connects the full-loop parametric arc length to the complete elliptic integral, proves the open-interval series, handles the degenerate endpoint, and states the symmetric result for nonnegative semiaxes.

## Build

From this directory:

```powershell
lake build
```

The project is pinned by `lean-toolchain` and `lake-manifest.json`. `EllipseLab.lean` is the production root and imports both `EllipseLab.Basic` and `EllipseLab.Shape`.

## Historical files

The `Intermediate state *.txt` files and `Cop-out.txt` record development attempts. They are not imported production modules and should not be used as evidence for the final theorem. The manuscripts under `../Article/` describe the completed `Shape.lean` theorem chain.
