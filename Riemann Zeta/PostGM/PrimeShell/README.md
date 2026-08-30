# Prime Shell

This directory is the isolated research and implementation area for the Prime Shell program.

## Boundary

- Frozen Guth–Maynard source: commit `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`, tag `gm-foundation-freeze-v1.0.1`, Lean `v4.30.0`.
- Pinned Zeta23 source: Anthropic `formal-math` tag `v1.0`, commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, Lean `v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.
- `Extension/` is a separate Zeta23-compatible Lake project. It neither imports the frozen GM project nor enters `RiemannZeta.lean`.
- The immutable dependency may replay its own warnings during `lake build`; direct Prime Shell elaboration is used to distinguish project-source diagnostics from upstream diagnostics.

## Corrected program verdict

Prime Shell reached the permitted **ROUTE DISPROVED** endpoint. It proves no new theorem about zeta zeros.

The earlier claim that a disconnected shell was impossible because Zeta23 `WindowProfile` is strictly positive was not a faithful terminal model: the gap can be placed in a smooth amplitude `q`, and the actual source can be formed as `atV (q²)`. That correction is now formalized. The faithful class is nonempty; `concreteFaithfulAmplitudeShell` supplies an explicit smooth two-band member.

The actual terminal obstruction is spectral. For every faithful separated amplitude in the full explicit-formula range, Lean proves

```text
3 < kappaXi lambda (q²).
```

Consequently the exact Zeta23 rank/inertia output `2 - kappaXi` cannot improve `2/3` by any positive amount, even if all prime-correlation errors were controlled perfectly. The public endpoint is `primeShell_universal_no_gain_native`, and `faithfulSeparatedAmplitudeGain_iff_false` is its two-sided trusted-statement comparator.

This does not rule out connected positive-valley windows, a different source construction, or any approach outside the `FaithfulAmplitudeShell` mechanism.

## Documents

- [Prime Shell Architecture](Prime%20Shell%20Architecture.md): corrected dependency graph and numbered status.
- [Prime Shell Research Agenda](Prime%20Shell%20Research%20Agenda.md): mathematical program, source analysis, and terminal criterion.
- [Prime Shell Source Ledger](Prime%20Shell%20Sources.md): pins, papers, code crosswalk, and source qualifications.
- [Prime Shell Shitlist](Prime%20Shell%20Shitlist.md): exhaustive local acceptance checklist.
- [Prime Shell Phase I Report](Prime%20Shell%20Phase%20I%20Report.md): reproduction, exact kernel work, and F1 verdict.
- [Prime Shell Final Report](Prime%20Shell%20Final%20Report.md): corrected non-vacuous terminal theorem, proof ledger, verification, and nonclaims.
- [Prime Shell Candidate Manifest](Prime%20Shell%20Candidate%20Manifest.md): immutable pins and source hashes.
- `push_to_github.bat`: owner-operated add/commit/push-to-main helper; it performs no build or CI work.

Supply an explicit current commit message when running the push script. Agents do not run it as part of verification. PSH-21 remains an external expert-review obligation.
