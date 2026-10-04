# Tao--Trudgian--Yang 2025: errata and formalization repairs

Status: 4 October 2026. This is the local project's consolidated record,
not an author-issued erratum or an independent referee report. It covers the
twelve issues in the owner's supplied summary and the additional source
discrepancies already recorded in the source-to-Lean crosswalk.

The source edition is arXiv `2501.16779v1`, *New exponent pairs, zero density
estimates, and zero additive energy estimates: a systematic approach*.
The [frozen TeX](Sources/TaoTrudgianYang-v1-source/Tao_Trudgian_Yang_v2.tex)
has an internal `v2` filename; that does not change its arXiv version.
Source labels below refer to this frozen edition, not a newly inspected
upstream version. The original source files remain unchanged.

The distinctions matter: a disproved statement, an insufficient cited proof,
an incomplete formalization, and a tooling failure are different findings.
All 42 local acceptance gates are complete under the documented
owner-authorized contracts. That does not prove either false printed
supporting statement or establish external review. Every frozen public end
statement, including the stronger Pintz endpoint values, is preserved.

## Issue register

The numbering matches the owner's twelve-item summary. Items 4--6 are the
three resolutions of the single endpoint-source issue in item 3, not three
additional counterexamples to the paper's conclusions.

| Item | Classification | Finding and disposition |
| --- | --- | --- |
| 1. Lemma 62 energy powering | Disproved supporting statement; authorized contract repair | The restriction `s'≤s/k` contradicts the singleton energy pattern. Use the proved, independent cardinality and energy witnesses, without fifth-coordinate scaling. |
| 2. Unrestricted zeta-growth transfer | Disproved supporting statement; authorized contract repair | `add-bound(i)` and `lvz-340` omit the necessary strict condition `1−τ<σ`. The corrected implications are proved; the original counterexample remains. |
| 3. Closed Pintz endpoints | Source-attribution/proof gap; research strengthening | Pintz Theorem 1's max formula and strict cell boundaries do not supply the stronger printed values at equality. The separate source-faithful table is preserved, not substituted. |
| 4. Second endpoint, `A(41/42)≤63/85` | Original research resolving item 3 | Mixed-height logarithmic Taylor counting and critical VMVT control the actual far correlation, proving the exact missing zeta-LV strip and density endpoint. |
| 5. First endpoint, `A(39/40)≤16/21` | Original research resolving item 3 | The actual mixed-cell reciprocal-cubic/quartic far-correlation argument, with moment, Abel and Gram consumers, proves the unchanged endpoint. |
| 6. Every integer-tail endpoint | Original research resolving item 3 | A uniform far-correlation/physical-moment argument proves the required general-LV strip for every integer `n≥6`, then the unchanged `3/(n−1)` density bound. |
| 7. Atkinson source form | Former formalization gap, not a disproof of Atkinson | The literal Ivić Theorem 6.2, (6.20)--(6.23) consumer is proved independently, including the original widths, phase, damping and cutoff. Earlier weaker results remain distinct. |
| 8. Huxley source chain | Former formalization/provenance gap | Actual source consumers discharge the geometry and linked-scale obligations for every beta segment used by the four pairs. Unused sharper printed rows are not claimed proved. |
| 9. Exponent-pair provenance | Analytic proof obligation, not a paper erratum by itself | The exact Watt coordinates follow from a stronger proved Bourgain pair; the Robert--Sargos/old-pair route has actual analytic provenance. A table entry or assumed pair is not proof. |
| 10. Historical computation | Reproduction and proof-integrity boundary | The pinned replay and deterministic rational certificates are checked independently. Archived Python, including its false powering rule, is never a Lean proof oracle. |
| 11. Build/integrity defects | Local implementation defects | Missing PDF pinning, UTF-8 manifest handling and an ambiguous regression reference were repaired before the recorded complete BAT reruns. These are not mathematical errata in the paper. |
| 12. Failed proof routes | Interpretation safeguard | Scalar barriers rule out the specified majorants, not the endpoint statements. Retained route obstructions are compatible with the later independent endpoint proofs. |

## 1. Lemma 62: false fifth-coordinate powering

Source: `power-energy`, Lemma 62. The printed claim requires each of its
three potentially different output witnesses to satisfy `s'≤s/k`, and one
to attain equality. The double-zeta sum is unnormalized:

\[
S(N,W)=\sum_{t,u\in W}\left|\sum_{n\in[N,2N]}n^{-i(t-u)}\right|^2.
\]

For integers `N>1`, take coefficients one, `W={0}`, `T=N²` and
`V=N^(3/4)`. Then `S(N,{0})=(N+1)²`, and the actual asymptotic energy
region contains `(3/4,2,0,0,2)`. Every energy-region point satisfies
`ρ+2≤s`, hence `s≥2`. At `k=2` the printed conclusion requires `s'≤1`:
there is no such output point, even before demanding an equality witness.

This is a counterexample to the supporting lemma, not to the nine final
additive-energy estimates. See
[EnergyPoweringObstruction.lean](Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean),
especially `energyPowering_source_counterexample`, and the permanent
[obstruction account](Tao-Trudgian-Yang%20Energy%20Powering%20Obstruction.md).

Owner-authorized repair, 20 September 2026: write
`E₄(σ,τ,ρ,e) := ∃s, E(σ,τ,ρ,e,s)`. For every fixed positive integer `k`,
an actual `E₄(σ,τ,ρ,e)` yields both

\[
\begin{aligned}
&\exists e_c,\ E_4(\sigma,\tau/k,\rho/k,e_c)\ \land\ e_c\le e/k,\\
&\exists r_e,\ E_4(\sigma,\tau/k,r_e,e/k)\ \land\ r_e\le\rho/k.
\end{aligned}
\]

The witnesses may differ. Their fifth coordinates are independently
existential, with no comparison to the old `s` or to `s/k`; there is no
third, double-zeta-preserving witness. Region membership retains the
original sigma range and nonnegative exponent conditions.

`correctedCardinalityEnergyPowering` and
`InLargeValueEnergyRegion.corrected_powering` in
[CorrectedEnergyPowering.lean](Extension/TaoTrudgianYang2025/CorrectedEnergyPowering.lean)
prove this replacement. `InCardinalityEnergyRegion.heathBrown_powered`
consumes the corrected energy witness and the independently proved relation.
Exact optimization then proves all nine unchanged `add_est_i` through
`add_est_ix` in [NewAdditiveEnergy.lean](Extension/TaoTrudgianYang2025/NewAdditiveEnergy.lean).
The [repair account](Tao-Trudgian-Yang%20Energy%20Powering%20Repair.md)
records normalization, limits, monotonicity and bounded-range transfer.
This is an authorized source-contract repair, not a proof of Lemma 62 as printed.

## 2. Zeta-growth transfer: missing low-height restriction

Sources: `add-bound(i)` and its old-pair consequence `lvz-340`.
At `σ=3/4`, `τ=1/4`, the actual exponent is
`LV_zeta(3/4,1/4)=1/4`, not negative infinity. Nevertheless, the printed
growth hypothesis holds with `c=1/2`, since

\[
\tfrac12+\tfrac14\mu(\tfrac12)\le\tfrac{13}{24}<\tfrac34,
\qquad
\tfrac7{10}+\tfrac3{40}\tfrac14=\tfrac{23}{32}<\tfrac34.
\]

Owner-authorized repair, 27 September 2026: for `τ>0` and
`1/2≤c,σ≤1`, require **both**

\[
c+\tau\mu(c)<\sigma\quad\text{and}\quad 1-\tau<\sigma
\quad\Longrightarrow\quad \mathrm{LV}_\zeta(\sigma,\tau)=-\infty.
\]

The old-pair consequence similarly retains both
`7/10+(3/40)τ<σ` and `1−τ<σ`. The added inequality must be strict:
the counterexample has `1−τ=σ`, so a non-strict repair is still false.

Public proof: `zetaCorrected_exponent_eq_bot_of_mu` in
[ZetaGrowthCorrectedTransfer.lean](Extension/TaoTrudgianYang2025/ZetaGrowthCorrectedTransfer.lean).
The genuine old pair and `ExponentPair.zetaLargeValueExponent_eq_bot`
give the corrected old-pair consequence. Preserve
[ZetaLowHeightObstruction.lean](Extension/TaoTrudgianYang2025/ZetaLowHeightObstruction.lean),
the exact low-height results and their regression sections.

The [Zeta Growth Repair](Tao-Trudgian-Yang%20Zeta%20Growth%20Repair.md)
records every EPZAE-21 acceptance clause. Moment transfer, exact reflection,
the genuine twelfth moment and the sharp Atkinson source form were separate
obligations and are also complete. The growth repair alone did not close them.

## 3--6. Pintz boundaries: stronger endpoints, not false conclusions

The completed source audit identifies a boundary-ownership gap: Pintz
Theorem 1 supplies a max formula on strict cells. Its arithmetic does not
supply the next cell's stronger value at the closed lower boundary assigned
by the printed best-known table. This is not a counterexample to those
stronger values. They are classified as **RESEARCH STRENGTHENINGS**.

[LiteratureDensity.lean](Extension/TaoTrudgianYang2025/LiteratureDensity.lean)
preserves the source-faithful bounds, separate table and source-audit evidence.
That table is not the acceptance replacement. The three original research
proofs establish the frozen endpoints:

| Endpoint | Exact public evidence in namespace `TaoTrudgianYang2025` |
| --- | --- |
| `A(41/42)≤63/85` | `PintzEndpointResearch.pintz_second_endpoint_research_density` in [PintzEndpointResearch.lean](Extension/TaoTrudgianYang2025/PintzEndpointResearch.lean) |
| `A(39/40)≤16/21` | `PintzFirstEndpointResearch.pintz_first_endpoint_research_density` in [PintzFirstEndpointResearch.lean](Extension/TaoTrudgianYang2025/PintzFirstEndpointResearch.lean) |
| `A(1−1/(2n(n−1)))≤3/(n−1)`, every integer `n≥6` | `PintzTailCorrelationResearch.pintz_tail_research_density` in [PintzTailCorrelationResearch.lean](Extension/TaoTrudgianYang2025/PintzTailCorrelationResearch.lean) |

For item 4, `pintz_second_endpoint_research_largeValueBound` proves precisely

\[
\mathrm{LV}_\zeta(41/42,\tau)\le\frac{3\tau}{170},
\qquad \frac{37}{7}\le\tau<\frac{340}{63}.
\]

For item 6, `pintz_tail_research_exponent` proves the general-coefficient strip

\[
\mathrm{LV}\left(1-\frac1{2n(n-1)},\tau\right)
\le\frac{3\tau}{2n(n-1)^2},
\qquad \frac{2(n-1)}3\le\tau\le n-1,\quad n\ge6.
\]

These proofs bound the actual far correlations, retain original difference
multiplicities, and discharge the physical-scale, Gram, epsilon-loss and
zero-density-transfer steps. Endpoint inequalities are not assumed inputs.
The tail module's `zeroDensityExponent_le_printedTable` assembles the
unchanged full envelope on `1/2≤σ<1`; `printedDensityTable_tail_lower`
checks the exact frozen tail value. None of this changes what Pintz's cited
strict-cell theorem says. The [current crosswalk](Tao-Trudgian-Yang%20Crosswalk.md)
records the actual consumers and their semantics.

## Further audited source discrepancies

These supplement the owner's twelve-item list. They are already documented
in the crosswalk; this errata document does not authorize additional repairs
or alter any frozen conclusion.

| Location | Discrepancy | Implemented resolution and scope |
| --- | --- | --- |
| `exp-pair-def` | One prose quantifier reads `T≥N≤1`, whereas the displayed estimate continues with `T≥N≥1`. | Use the latter intended range in the actual analytic exponent-pair predicate. This is a documented notation correction. |
| `lv-edef` | The nonnegative-coordinate binder names `ρ'`, while the five-coordinate tuple uses `ρ*` and `s`. | Use the actual five-coordinate energy semantics and the source's non-asymptotic clarification, with explicit coordinate constraints. |
| Proof of `hbt` | The final finite-estimate term has `E₁(W)^(3/4) N T^(1/2)`, inconsistent with the stated exponent `3ρ*/4+ρ+τ/2`. | The native moment and finite-pattern bridges independently prove the displayed exponent relation through `heathBrown_largeValuePattern_energy_squared` and `InLargeValueEnergyRegion.heathBrown_relation`. The mismatched archived line is not used. |
| Proof of `Add-est (i)` | An intermediate conclusion uses `min` in place of the target maximum; another substitution omits `σ` after `25/2`. | `EnergyClauseOneZeta` proves the target maximum and the exact substitution `23/2−(25/2)σ+τ/4` from checked branch formulas. |
| Proof of `bourgain-density-improved` | The printed Jutila `k=3` comparison and displayed Bourgain choice both exceed the required `11/20` at `σ=38/49`, `τ=6/5`. | The proved `k=4` Jutila bound repairs the comparison. `zeroDensityExponent_le_bourgain_improved` in [BourgainImprovedDensity.lean](Extension/TaoTrudgianYang2025/BourgainImprovedDensity.lean) proves the unchanged full max formula; `BourgainImprovedDensityRegression` preserves both the gap and the replacement check. |
| ANTEDB twelfth-moment proof inspected 20 September 2026 | Theorem 9.7 displays a minimum where its cited Lemma 8.11 supplies a maximum. | Keep `max(a,2a)` with `a=τ−6(σ−1/2)`: the nonnegative branch is `2a`, and the negative branch uses actual zeta-exponent discreteness. This algebra does not itself prove the analytic moment input. |
| Best-known table's cross-reference | The optimized Bourgain result is called a corollary although its labeled declaration is a theorem. | Resolve by source label and exact statement, not the descriptive type name. |
| Ivić source identification | A local filename suggests a zeta book, but the inspected scan is Orsay 83.06, *Topics in Recent Zeta Function Theory*. | Use that edition's Theorem 6.2 and Theorem 7.1/Corollary 7.2 numbering; do not conflate it with the book theorem numbers cited by the blueprint. |

## 7--9. Formalization and analytic provenance

These entries describe obligations resolved in this implementation, not
counterexamples to Atkinson, Huxley, Watt or Robert--Sargos.

- **Atkinson:** `AtkinsonPrintedSource.exists_zetaSquareLocalMean_le_printedAtkinson`
  in [AtkinsonPrintedSource.lean](Extension/TaoTrudgianYang2025/AtkinsonPrintedSource.lean)
  realizes Ivić Orsay 83.06, Theorem 6.2, (6.20)--(6.23), printed page 107.
  Constants precede the physical parameters; the original power-width range,
  phase, prefix, signed weights, damping, dyadic range and cutoff are retained.
  The separate shifted-height corollary (6.24) is not claimed here.
- **Huxley:** [HuxleyLinearForms.lean](Extension/TaoTrudgianYang2025/HuxleyLinearForms.lean)
  and the public consumers in
  [BourgainOptimizedTransfer.lean](Extension/TaoTrudgianYang2025/BourgainOptimizedTransfer.lean)
  supply the actual beta bounds consumed by the four new pairs. Geometry,
  common labels, Taylor errors and physical scales are not replaced by
  assumed final estimates. Sharper unused printed short rows 3/4 and the
  optional full literal Huxley family fifth moment remain outside the
  completed actually-consumed-segment claim.
- **Pairs:** `exponentPair_bourgain` and `exponentPair_watt_of_bourgain` in
  [ParabolaBilinearLocalization.lean](Extension/TaoTrudgianYang2025/ParabolaBilinearLocalization.lean)
  prove `(13/84,55/84)` and then the exact Watt coordinates `(89/560,369/560)`.
  This is alternate analytic provenance, not reproduction of Watt's historical
  argument. `exponentPair_robertSargos` and `exponentPair_three_fortieths` in
  [RobertSargosExponentPair.lean](Extension/TaoTrudgianYang2025/RobertSargosExponentPair.lean)
  prove `(1/13,10/13)` and `(3/40,31/40)` from the derivative/counting chain
  and the classical pair, without assuming the desired analytic output.

## 10--12. Reproduction, implementation and interpretation

Historical ANTEDB computation is replayed in its pinned environment. All
nine energy recipes, exact replay comparisons and deterministic certificate
regeneration are covered by the paper verifier. Lean checks rational
certificates and consumes independently proved analytic inputs; it does not
trust Python truth values or the archived false five-coordinate powering rule.
Replay adapters and the clause-5 strict relaxation are disclosed in the
[tooling guide](Tools/README.md).

The missing source-PDF pin, Windows UTF-8 manifest handling and ambiguous
regression-name failures are retained in the
[Reproduction Manifest](Tao-Trudgian-Yang%20Reproduction%20Manifest.md).
Failed runs are not represented as PASS evidence. The final recorded
foundation and paper BATs both pass with zero Lean diagnostics; the two
archived Python invalid-escape SyntaxWarnings remain explicitly disclosed.
This errata addition is documentation only, not a new build receipt.

Route-obstruction lemmas are limited to their specified inequalities,
parameters and majorants. They neither refute the endpoint nor exhaust all
possible proof methods. The later endpoint proofs do not erase those earlier
findings; they use arguments that overcome the missing far-correlation step.

## Preservation and maintenance

- Keep the frozen source, all public end statements, both counterexamples,
  source-faithful table, route-obstruction evidence, audits and regressions.
- Treat the two supporting-statement repairs as owner-authorized contracts;
  never describe them as proofs of their false printed originals.
- Keep closed Pintz endpoints classified as original research strengthenings,
  not newly recovered consequences of Pintz's strict source cells.
- Keep `run_tao_trudgian_yang_build.bat` and the foundation
  `run_lake_build.bat` synchronized with relevant implementation changes and
  rerun them sequentially when required. Do not narrow their coverage or gates.
- Recovery-record maintenance remains permanently optional and skipped.

This record consolidates existing results; it changes no theorem, dependency,
acceptance test or proof status. It does not assert that the original authors
have endorsed these findings, that an upstream erratum has been issued, or
that the work has received independent semantic or peer review.
