# 71 Guth--Maynard, 2026

This node is the physical source root for the completed, frozen Guth--Maynard formalization. `RiemannZeta.lean` is the package root; `GuthMaynard/`, `GuthMaynardExternal/`, and the support/audit modules sit directly beside it. `GuthMaynardExternal/` gives the vendored PNT files a collision-free module prefix. Declaration namespaces remain `RiemannZeta.*`, while filesystem module names follow this flat layout. The project-root `lakefile.toml` points `srcDir` here.

Run `run_guth_maynard_build.bat --no-pause` from this directory for the canonical build, exact-contract checks, dependency audit, and lint gate.

The Guth–Maynard documentation is colocated here:

- [`Lean Alignment Checklist.md`](Lean%20Alignment%20Checklist.md): exhaustive
  acceptance checklist and chronological repair ledger.
- [`Proof Architecture.md`](Proof%20Architecture.md): canonical Mermaid dependency and completion diagram.
- [`Research Agenda Progress.MD`](Research%20Agenda%20Progress.MD): evidence-based current status and completion report.

See [the project README](../../README.md), [the source freeze](../../verification/SOURCE_FREEZE.md), and [the publication-readiness packet](../../Publication%20Readiness%20and%20Semantic%20Audit.md).
