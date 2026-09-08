# Article drafts

This directory contains natural-language manuscripts for the ellipse-perimeter formalization.

- `input - Paper v2.md` and `Ellipse Perimeter v2.docx` are the latest full-paper pair in this directory.
- The `v1` files are earlier retained drafts.
- `input - abstract.md` and `Abstract v1.docx` contain the short abstract.
- `Two Endpoint Normalizations v1.md` and its DOCX counterpart are a separate explanatory note.
- `build-docx.bat` regenerates Word output using the locally configured document toolchain.

The complete Lean theorem described by the paper is `EllipseOmega.ellipse_perimeter_series` in `../EllipsePerimeter/Shape.lean` and is imported by the canonical package root `../EllipsePerimeter.lean`.
