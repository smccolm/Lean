# EllipsePerimeter

This package is an earlier, incomplete extraction of the ellipse-perimeter development. It is retained because its Wallis-coefficient and open-interval binomial-series modules contain useful proved components, but it is not the canonical home of the completed perimeter theorem.

Current module status:

- `EllipsePerimeter/Wallis.lean`: Wallis and elliptic-series coefficient definitions and recurrences.
- `EllipsePerimeter/Binomial.lean`: summability and the identity for the square-root series on `|x| < 1`.
- `EllipsePerimeter/Boundary.lean`: empty placeholder.
- `EllipsePerimeter/EllipticE.lean`: empty placeholder.
- `EllipsePerimeter/Geometry.lean`: empty placeholder.

The complete theorem `EllipseOmega.ellipse_perimeter_series` is instead in `../EllipseLab/EllipseLab/Shape.lean` and is imported by the `EllipseLab` package root.

## Build

From this directory:

```powershell
lake build
```

A successful build here verifies only the partial modules listed above. It must not be reported as verification of the complete geometric perimeter formula.

The current build also emits a style-whitespace linter warning from the package root import file. This does not prevent elaboration, but this partial package is not documented as warning-free.
