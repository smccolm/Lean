# Owner-authorized zeta-growth source-contract repair

Authorized by the project owner on 27 September 2026. This changes only the
accepted EPZAE-21 growth/nonexistence clause and its old-pair consequence.
It is **not a proof of the false printed statement**, an edit to the frozen
paper, or authorization to drop any other acceptance requirement.

## Accepted corrected contract

For real `τ>0` and `1/2≤c,σ≤1`,

```text
c + τ·μ(c) < σ   and   1−τ < σ   imply   LV_zeta(σ,τ) = −infinity.
```

Here `μ` is the actual extended-real growth infimum and `LV_zeta` uses the
actual coefficient-one large-value patterns. No finiteness, attainment,
moment bound or nonexistence conclusion is assumed.

The existing kernel-checked public theorem is
`zetaCorrected_exponent_eq_bot_of_mu` in
[ZetaGrowthCorrectedTransfer.lean](Extension/TaoTrudgianYang2025/ZetaGrowthCorrectedTransfer.lean).
Its `hres : 1-τ < σ` is essential. Its signature actually needs no separate
positive-height premise, so it covers the full corrected source domain.
The same module proves the uniform empty-pattern threshold and
sharp-interval pointwise power-saving consumers. The theorem for a genuine
`IsZetaGrowthBound c m` retains the corresponding two strict inequalities.

For the proved old pair `(3/40,31/40)`, the accepted `lvz-340` consequence is

```text
τ>0, 1/2≤σ≤1,
7/10 + (3/40)τ < σ   and   1−τ < σ
imply LV_zeta(σ,τ) = −infinity.
```

This follows directly from
`exponentPair_three_fortieths` in
[RobertSargosExponentPair.lean](Extension/TaoTrudgianYang2025/RobertSargosExponentPair.lean)
and `ExponentPair.zetaLargeValueExponent_eq_bot` in
[ZetaPairNonexistence.lean](Extension/TaoTrudgianYang2025/ZetaPairNonexistence.lean):
`(3/40)τ + 31/40 − 3/40 = 7/10 + (3/40)τ`.
Alternatively, `old_pair_zetaGrowthBound` and the corrected growth-bound
consumer give this same statement. No Watt or Robert--Sargos analytic input
remains assumed in this application. At `τ≥1`, the residual inequality is
automatic on the source sigma strip; it must not be discarded at low height.

## Frozen false source and permanent counterexample

The original `add-bound(i)` and `lvz-340` remain unchanged in
[the frozen TeX](Sources/TaoTrudgianYang-v1-source/Tao_Trudgian_Yang_v2.tex).
Their omission of the residual condition is false in the project's actual
semantics. This repair does not reinterpret them as true or rename their
counterexample out of the audit.

At `σ=3/4`, `τ=1/4`, the exact low-height result is
`LV_zeta(3/4,1/4)=1/4≠−infinity`. Nevertheless,
`μ(1/2)≤1/6` gives `1/2+(1/4)μ(1/2)≤13/24<3/4`, and
`7/10+(3/40)(1/4)=23/32<3/4`. Thus both unrestricted clauses fail.
The repaired strict residual excludes this example because `1−τ=σ`.
Replacing the strict inequality by a non-strict one would remain false.

Permanently retain:

- [ZetaLowHeightObstruction.lean](Extension/TaoTrudgianYang2025/ZetaLowHeightObstruction.lean),
  including the actual growing pattern construction and
  `zetaGrowth_unrestricted_largeValue_transfer_counterexample`;
- [ZetaLowHeightExact.lean](Extension/TaoTrudgianYang2025/ZetaLowHeightExact.lean)
  and [ZetaLowHeightVanishing.lean](Extension/TaoTrudgianYang2025/ZetaLowHeightVanishing.lean),
  including the exact boundary formula;
- the existing obstruction accounts in the Checklist, Crosswalk, Sources,
  Research Agenda and architecture history; approval supersedes only their
  pending-authorization status, not their mathematical findings;
- [SemanticRegression.lean](Extension/TaoTrudgianYang2025/SemanticRegression.lean):
  `ZetaSharpLowHeightRegression` checks the exact boundary, the false old-pair
  statement and the false non-strict variant;
  `CorrectedGeneralGrowthRegression` checks the actual corrected theorem,
  its uniform consumers and retained counterexamples;
- all existing [Audit.lean](Extension/TaoTrudgianYang2025/Audit.lean) entries
  for these declarations, and the separate energy-powering obstruction and repair.

## Completed acceptance and verification (28 September 2026)

**EPZAE-21 is DONE under the owner-authorized contract; aggregate 34/42.**
The separate analytic proof in
[AtkinsonPrintedSource.lean](Extension/TaoTrudgianYang2025/AtkinsonPrintedSource.lean)
now supplies the sharp printed source form. The focused build and both
mandatory BATs pass, exit 0, with zero Lean diagnostics. Completion rests
on all the following checked source consumers, not on this repair alone.
The principal run passes 7,229 regressions and 18,053 exhaustive dependency
audits; the foundation run passes 14,290 audits. No acceptance requirement
was waived. This remains a repair, not a proof of the false printed clauses.

| Acceptance clause | Exact public evidence |
| --- | --- |
| Corrected growth/nonexistence | `zetaCorrected_exponent_eq_bot_of_mu`, with the actual EReal growth infimum and strict `1−τ<σ`; uniform empty-pattern and sharp-interval consumers are also proved. |
| Corrected old-pair consequence | `exponentPair_three_fortieths` composed with `ExponentPair.zetaLargeValueExponent_eq_bot`; both strict inequalities are retained. |
| Printed real-moment transfer | `zetaRealMoment_largeValueBound_closed_strip` and `zetaLargeValueExponent_le_of_realMoment_closed_strip`, including `c=1`, every real order at least one and arbitrary real moment exponent; only the source's dyadic moment hypothesis is supplied. |
| Printed reflection | `zetaLargeValueExponent_reflection_supremum`, the literal affine supremum identity for `τ>1`, including EReal bottom cases, not the informal pointwise heuristic. |
| Genuine twelfth moment and LV consequence | `zeta_twelfth_dyadic`, `zetaTwelfth_largeValueBound`, and the proved short-range consumers; no moment certificate is assumed. |
| Sharp Atkinson source form | `AtkinsonPrintedSource.exists_zetaSquareLocalMean_le_printedAtkinson`, the actual integral of `norm(riemannZeta(1/2+it))^2`, with constants before `T,G`, original full power widths, exact phase, prefix, damping, dyadic range and cutoff. |

The last row was checked against printed page 107 of Ivić Orsay 83.06,
Theorem 6.2, (6.20)--(6.23). Its finite dyadic definition has a proved exact
membership equivalence; its phase has a proved constant/unit-modulus bridge.
Geometry and cutoff positivity are derived from the original width hypotheses.
The shifted-height corollary (6.24) is distinct and is not asserted here.
No acceptance requirement is removed.

In particular, [AtkinsonStationaryZetaSource.lean](Extension/TaoTrudgianYang2025/AtkinsonStationaryZetaSource.lean)
retains the earlier error `C(G log T + T^(1/4+ε))` with `G≥T^(1/4)`,
or `C G log T` with `G≥T^(1/4+κ)`, retaining the other physical-scale
hypotheses. The subsequent
[AtkinsonMorseStationary.lean](Extension/TaoTrudgianYang2025/AtkinsonMorseStationary.lean)
proves `C_delta G log T` for the actual Gaussian and local-mean stationary
consumers throughout `T^delta≤G≤T^(1/2−delta)`. This is a new analytic proof,
not a consequence of the growth-contract repair. Both original signed sums,
coefficients and the ceiling cutoff are retained. The subsequent printed-source
consumer applies that theorem at width `4G`, controls both signed weights,
uses exact logarithmic divisor summation for small blocks, and pays the tail
beyond the literal printed cutoff. It assumes no source-form inequality.

[run_tao_trudgian_yang_build.bat](run_tao_trudgian_yang_build.bat) must retain
this repair document in its required inventory, frozen-source verification,
full module coverage, the counterexample regressions and dependency audits.
It and the foundation `run_lake_build.bat` remain mandatory, with unchanged
zero-Lean-warning and no-shortcut gates. Maintain them as coverage changes.
Current run evidence belongs in the
[Reproduction Manifest](Tao-Trudgian-Yang%20Reproduction%20Manifest.md).
