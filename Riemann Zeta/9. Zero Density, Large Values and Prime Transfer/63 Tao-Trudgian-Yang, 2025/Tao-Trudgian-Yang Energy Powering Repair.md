# Authorized cardinality/energy powering repair

Authorized by the owner on 20 September 2026. This replaces the false
supporting requirement in EPZAE-34, not any advertised final theorem.
The printed Lemma 62 and its kernel-checked counterexample are preserved.

## Corrected statement

Let `E₄(σ,τ,ρ,e)` mean `∃ s, E(σ,τ,ρ,e,s)`, using the existing, faithfully
defined five-dimensional energy region. For each fixed positive **integer**
`k` and each point `E₄(σ,τ,ρ,e)`, prove both:

```text
∃ eCard, E₄(σ, τ/k, ρ/k, eCard) ∧ eCard ≤ e/k;
∃ rEnergy, E₄(σ, τ/k, rEnergy, e/k) ∧ rEnergy ≤ ρ/k.
```

The two points may be different. Expanded into five coordinates, their last
coordinates are independent existential values `sCard` and `sEnergy`.
Neither is compared with the original `s`, with `s/k`, or with each other.
There is no third witness preserving the double-zeta exponent. The domain
`1/2 ≤ σ ≤ 1`, `τ,ρ,e ≥ 0` is retained through region membership.
The integer-power domain makes explicit the polynomial expansion used in
the source proof.

`EnergyPowering.lean` defines this exact target as
`CorrectedCardinalityEnergyPowering`. Its full proof is now
`correctedCardinalityEnergyPowering` in `CorrectedEnergyPowering.lean`.
`InLargeValueEnergyRegion.corrected_powering` exposes the expanded
five-coordinate conclusion above, with no mathematical theorem parameter.
The proposition definition alone is not the proof evidence.

## Kernel-checked repair argument

Start with a realizing sequence of actual large-value patterns. The fixed
power `k` is chosen before the sequence and all limiting arguments.

1. If reusing the local half-open polynomial API, remove the single left
   endpoint of `[N,2N]`. Its contribution has norm at most one. Since
   `V = N^(σ+o(1))` and `σ ≥ 1/2`, this replaces `V` by `V-1` without changing
   its exponent. `LargeValuePattern.halfOpen_large` proves the loss-one
   bound and `tendsto_logb_sub_one` proves the limiting bridge.
2. Expand the `k`th power. The product coefficients have a bound
   `C(k,η) m^η` uniform in the original scale and coefficients. Subdivide
   `(N^k,2^k N^k]` into `k` dyadic blocks. Assign each ordinate to a block
   where the powered polynomial has modulus at least `V^k/k`, with the
   endpoint adjustment above when applicable.
3. Normalize coefficients to be one-bounded. Choose `η→0` and the original
   scale large enough to absorb `C(k,η)` before extracting a sequence.
   Each output scale has `M = N^(k+o(1))`, height exponent `τ/k`, and value
   exponent `σ`. Embed half-open blocks into the closed-support pattern
   definition by putting zero at the left endpoint.
4. Ordinary pigeonholing selects a class with cardinality at least `|W|/k`.
   Its energy is at most the original energy. A separate energy selection
   selects a class with energy at least `E₁(W)/(9 k^4)` and cardinality at
   most `|W|`. Constants depending on fixed `k` disappear in the exponents.
5. Extract convergent logarithmic coordinates along a subsequence for each
   selected family. Cardinality and energy are bounded by the existing
   one-separation estimates. The **new** double-zeta exponent can also be
   extracted using `|W'| M² ≲ S(M,W') ≲ |W'|² M²`; it is not inherited
   from the old scale. The two resulting subsequences give the two witnesses.

All five steps above are now implemented. `EnergyPoweredPatterns` constructs
every normalized block and the two selected patterns;
`EnergyPoweringLimits` proves the logarithmic limits and compactness;
`CorrectedEnergyPowering` assembles the full two-witness theorem.
Neither output witness is a theorem hypothesis.

The source sequence is chosen at accuracy `1/(8*(n+1))`, with its scale
threshold at least `exp(|log C_n|/accuracy_n + 1)` and `n+2`. This proves
`log C_n / log N_n → 0` even though the divisor constant varies with the
accuracy. A fixed-accuracy coefficient bound alone would not suffice.

Existing reusable inputs include local `finite_polynomial_power_identity_Ioc`,
`finitePowCoeff_bound_uniform`, and `exists_energy_color_classes`, together
with the target's energy logarithmic-coordinate compactness machinery.

## Why the Heath–Brown step survives

Write the exact displayed right side as `H(σ,τ,ρ,e)`. It has no `s`
argument and is nondecreasing in `ρ` for fixed `σ,τ,e`. Applying the
analytic relation to the energy-preserving output gives

```text
e/k ≤ H(σ, τ/k, rEnergy, e/k) ≤ H(σ, τ/k, ρ/k, e/k).
```

Likewise the cardinality-preserving output transfers bounds on `ρ/k`.
The explicit use of Lemma 62 in the paper's proof of `Add-est` (i) records
an `s'≤s/k` condition but never uses it in the following Heath–Brown
deduction. Removing that unused condition repairs this particular logical
step. See the [pinned paper](https://arxiv.org/html/2501.16779v1).

`EnergyPowering` proves the finite energy-class selection and the separate
monotone-constraint consumers. The full repair now discharges the witnesses
in `InCardinalityEnergyRegion.powered_heathBrown_relation`. This actual-region
consumer retains its explicit conditional interface as a reusable deduction.
The analytic input is now independently proved by
`InLargeValueEnergyRegion.heathBrown_relation`; the new assembled consumer
`InCardinalityEnergyRegion.heathBrown_powered` has **no remaining analytic
theorem parameter**. Its proof really applies the relation to the corrected
energy witness and then uses cardinality monotonicity.
Identity-power and singleton regressions check that the repair retains the
original region semantics; the singleton's new `s` is still `2`.

## Optimization boundary

Inspection of the pinned paper-time archive `9953003` found:

- `additive_energy.py:get_raise_to_power_hypothesis` scales all five
  coordinates using `[1,k,k,k,k]`. Keep this as historical source, not as
  a trusted rule for the repaired proof.
- `literature.py:add_lver_heath_brown_1979b1` represents the displayed
  relation by nine affine alternatives. Each has zero coefficient on `s`.
- `additive_energy.py:lv_to_lver` lifts large-value estimates without a
  mathematical `s` constraint, but adds finite computational boxes.
- The inspected `derived.py:prove_zero_density_energy_2` through `_10`
  use the Heath–Brown `2a` relation and large-value estimates as their
  analytic inputs. This supports an `s`-free repair route; it is not an
  exact replay or Lean certification of their endpoint outputs.

The repaired finite proof must work with the four-coordinate projection
and individually justified monotone inequalities. **An arbitrary `s`-free
polytope is not automatically preserved by two separate witnesses.**
Conditional consumers in Lean state the needed monotonicity explicitly.
Discard the fifth-coordinate computational boxes when projecting, and
justify the remaining finite boxes on the actual parameter ranges.
Never scale an `s`-dependent constraint using the disproved rule.

The exact general-energy certificate for `Add-est (i)` is now checked on
its full source interval, with actual-region consumption and uniform
high-height consequences. The zeta rational certificate is also checked;
its analytic twelfth-moment input and the remaining eight clauses'
certificates and analytic inputs remain open. The short-zeta continuation
below now supplies the full short range from that same moment.
The public bounds are unchanged; full recovery by this repaired route
remains an obligation, not a conclusion of the static source inspection.

## Acceptance and preservation

EPZAE-34 is complete: `correctedCardinalityEnergyPowering` proves
`CorrectedCardinalityEnergyPowering` on its full domain, and both actual
witnesses are available through `InLargeValueEnergyRegion.corrected_powering`.
EPZAE-35 is also complete through the native second/fourth-moment route.
EPZAE-36/37 remain separate optimization and final-estimate obligations.
The architecture and goal now follow that route; authorization is no longer
a blocker.

Semantic completion audit:

| Required edge | Public proof evidence |
|---|---|
| Actual input region, all positive integer powers | `correctedCardinalityEnergyPowering` |
| Exact closed/half-open support and phase | `LargeValuePattern.halfOpen_large`, `closedSupportPolynomial_eq_halfOpen` |
| Uniform coefficient normalization and actual finite witnesses | `exists_normalized_powered_pattern_partition`, `exists_normalized_powered_subpatterns` |
| Constants chosen before realizing scales | `exists_powering_input_family` |
| Linked physical scale and threshold limits | `PoweringInputFamily.powered_time_value_limits` |
| Fresh double-zeta exponent and coordinate-preserving subsequences | `energyRegion_subsequence_of_log_limits`, consumed twice in the full proof |
| Expanded two-witness output | `InLargeValueEnergyRegion.corrected_powering` |
| Actual-region downstream consumption | `InCardinalityEnergyRegion.heathBrown_powered`, with both powering and analytic inputs proved |

All names above are in namespace `TaoTrudgianYang2025`. The three new
full-proof modules are imported by the root library, explicitly inventoried
by the principal runner, and covered by named and dynamic transitive audits.
Semantic regressions exercise the full theorem at `σ=1/2`, `σ=1`, `τ=0`,
arbitrary positive integer powers, and the preserved `k=2` counterexample.

Keep `EnergyPoweringObstruction.lean`, its explicit axiom audits, and its
semantic regressions in the default import graph and in
`run_tao_trudgian_yang_build.bat` coverage. Its preserved source SHA-256 is
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The source archives, source-hash ledger, definitions of `S` and `E`, and all
advertised final theorem statements are unchanged.

The proved repair is also consumed by `EnergyPoweringBounds`.
`IsLargeValueEnergyBound.of_powered` transfers a bound at `τ/k` to one at
`τ`; `isLargeValueEnergyBound_of_bounded_power_range` reduces all higher
general scales to `[τ₀,2τ₀]`. The resulting compact-range zero-energy
consumer retains zeta endpoint `1`, and must not be mistaken for the
source's still-open endpoint-two corollary. This downstream module is also
imported, inventoried, explicitly audited, and regression-tested.

## Completed Heath–Brown analytic step

`HeathBrownEnergyFinite` identifies the indexed energy exactly with native
ordered-pair energy, reflects the ordinate interval without changing energy,
and removes the left support endpoint with the explicit threshold loss
`V-1`. The native large-value energy inequality, second moment, fourth
moment, and finite Hölder inequality then give the squared finite bound.
In particular the mixed fourth-moment term contains `E^(3/4) |W|`, not the
discrepant `E^(3/4) N` printed in the archived `hbt` proof.

`EnergyLogLimits` and `HeathBrownEnergy` pass that bound along actual region
witnesses. Constants are uniform before the pattern is chosen; the scale
tends to infinity; `log_N(V-1) → σ`; and sums give exactly the displayed
maxima. Padding height to `max N T` is removed using `ρ ≤ τ`, preserving
the full domain, including `τ < 1`. No condition on `s` is added or used.

Additional semantic completion evidence:

| Required edge | Public proof evidence |
|---|---|
| Exact native energy and reflected source polynomial | `finsetAdditiveEnergy_eq_native`, `LargeValuePattern.reflectedOrdinates_energy`, `LargeValuePattern.reflectedHalfOpenPolynomial_eq` |
| Uniform finite analytic inequality on actual patterns | `heathBrown_largeValuePattern_energy_squared` |
| Linked physical limits, including all constants | `PoweringInputFamily.heathBrown_energy_padded` |
| Full source region and removal of height padding | `InLargeValueEnergyRegion.heathBrown_relation`, `heathBrownEnergyRHS_max_one` |
| Corrected powered analytic consumer | `InCardinalityEnergyRegion.heathBrown_powered` |
| Small-height optimization constraints | `InLargeValueEnergyRegion.heathBrown_small_height`, `InCardinalityEnergyRegion.heathBrown_small_height_powered` |

All 19 current named public theorems in these three modules have explicit audits;
all three modules are root-imported and in the principal runner inventory.
All nine final `Add-est` clauses remain open.

## Completed first general-energy optimization

The repair now reaches the exact general half of `Add-est (i)` in
`EnergyClauseOneGeneral`, not merely a conditional optimization interface.
For `3/4 ≤ σ ≤ 5/6` and `8σ-4 ≤ τ ≤ 2(8σ-4)`, it proves the source's
two energy-rate pieces with their crossover at `σ=4/5`. The certificate
is six explicit rational-affine branches with checked denominator signs,
closed height endpoints, and exact interpolation. Separate cardinality
and energy witnesses are used only in their justified directions.

| Required edge | Public proof evidence |
|---|---|
| Native finite cardinality estimate on actual patterns | `classical_largeValuePattern_estimate` |
| Linked logarithmic limits and actual region | `PoweringInputFamily.classical_cardinality`, `InCardinalityEnergyRegion.huxley_cardinality` |
| Corrected cardinality witnesses at `k` and `k+1` | `InCardinalityEnergyRegion.huxley_cardinality_powered`, `InCardinalityEnergyRegion.energyClauseOneGeneral_cardinality_cap` |
| Exact six-branch elimination and interval certificate | `exists_heathBrownEnergyBranch`, `energyClauseOneGeneral_branch_bound`, `energyClauseOneGeneral_power_cover` |
| Actual energy witness and both source pieces | `InCardinalityEnergyRegion.energyClauseOneGeneral`, `InLargeValueEnergyRegion.energyClauseOneGeneral_lower_piece`, `InLargeValueEnergyRegion.energyClauseOneGeneral_upper_piece` |
| Uniform bound and all higher general heights | `energyClauseOneGeneral_uniform_bound`, `energyClauseOneGeneral_high_height_bound` |
| Advertised rate with remaining zeta hypothesis explicit | `energyClauseOne_of_zeta_range` |

The last theorem requires uniform zeta-energy bounds on `[1,8σ-4)`;
these remain unproved, as does the source endpoint-two transfer. Thus it is
conditional and does not close any final `Add-est` clause. The original
counterexample, all source archives, and final output contracts are unchanged.
Both new modules are root-imported, runner-inventoried, and explicitly audited.

## Completed zeta rational optimization

`EnergyClauseOneZeta` proves the source's six-branch zeta certificate,
height transition, strict slope bounds, `65/86` crossover, and comparison
with the advertised maximum. Its Huxley cap uses the actual corrected
cardinality witness at power two, not any fifth-coordinate scaling.

| Required edge | Public proof evidence and status |
|---|---|
| Corrected Huxley cap on actual regions | `InCardinalityEnergyRegion.energyClauseOneZeta_cardinality_cap`, proved |
| Exact source maximum from two cardinality caps | `energyClauseOneZeta_branch_bound`, proved |
| Actual zeta region and proved Heath--Brown relation | `InZetaLargeValueEnergyRegion.energyClauseOneZeta_of_twelfth_cardinality`, conditional on twelfth-moment cardinality |
| Uniform LV bound to actual cardinality coordinate | `InZetaLargeValueEnergyRegion.rho_le_of_largeValueBound`, proved |
| Uniform zeta-energy bound including closed endpoints | `energyClauseOneZeta_uniform_bound_of_twelfth`, conditional on uniform twelfth-moment LV |
| Advertised final maximum | `energyClauseOneZetaRate_le_public`, proved |
| Full zero-energy assembly | `energyClauseOne_of_twelfth_and_short_zeta`, conditional on twelfth-moment LV over `[2,8σ-4)` and short zeta energy over `[1,2)` |

The uniform LV premise in this modular interface is now derived from the
genuine dyadic critical-line moment, as recorded below. The short-zeta
continuation also derives the short input from that moment; neither the
certificate nor the counterexample repair proves the moment itself.
In particular the nearby Gafni--Tao twelfth-moment
statement is not a proved theorem instance. The source endpoint-two
alternative and all nine final `Add-est` clauses remain open. All 11 public
theorems and their conditional signatures are explicitly audited, with
root imports, runner inventory, and endpoint/consumer regressions installed.

## Proved modular moment-transfer analysis

The repaired route now includes the critical-line, twelfth-power summation
step in source `add-bound (ii)`. `ZetaMomentKernel` counts separated points
in unit distance shells around an arbitrary center (including the central
point), integrates the literal kernel `1/(1+|u-t|)`, and proves weighted
twelfth-power Hölder by integrating Young's inequality.

`ZetaMomentTransfer` applies that result to
`|ζ(1/2+iu)|` on `[T/2,3T]`, for one-separated `W ⊆ [T,2T]`.
Writing `F_T(t)` for this convolution, it proves
`Σ_{t∈W} F_T(t)^12 ≤ L(T)^12 M₁₂(T)`, with
`L(T)=3+2 log(ceil(2T)+1)` and the actual source-window moment `M₁₂`.
Given the explicit pointwise input `V ≤ C sqrt(N) F_T(t)`, the actual
pattern consumer proves `|W| V^12 ≤ C^12 N^6 L(T)^12 M₁₂(T)`.

`ZetaMomentAsymptotics` proves that every fixed power of `L` is subpower
and enlarges the source window into the three dyadic intervals starting
at `T/2`, `T`, and `2T`. A genuine uniform dyadic moment hypothesis then
gives `L(T)^12 M₁₂(T) ≤ T^(2+ε)` eventually. The assembled actual-pattern
consumer retains both analytic hypotheses, not a supplied cardinality bound.

| Required edge | Public proof evidence and status |
|---|---|
| Arbitrary-center separated kernel sum | `sum_zetaMomentKernel_le_harmonic`, proved |
| Exact kernel mass and weighted Hölder | `integral_zetaMomentKernel`, `integral_weighted_twelfth`, proved |
| Literal zeta function and source-window summation | `sum_zetaMomentConvolution_twelfth`, proved |
| Actual pattern and physical `C^12 N^6` factor | `ZetaLargeValuePattern.twelfth_cardinality_of_convolution`, conditional on pointwise entry |
| Uniform logarithmic-loss absorption | `eventually_zetaMomentLogLoss_pow_le_rpow`, proved |
| Three dyadic intervals with correct endpoints | `zetaTwelfthMoment_le_three_dyadic`, proved |
| Normalized moment and actual-pattern bound | `eventually_zetaMomentLoss_twelfth_of_dyadic`, `zetaPattern_twelfth_cardinality_of_dyadic_and_convolution`, conditional on the stated analytic inputs |

The low-level transfer keeps its two inputs explicit. The Perron entry,
source domains, uniform error absorption, and epsilon--delta LV deduction
are now proved by the continuation below; the dyadic twelfth-moment
estimate remains open under EPZAE-19/21.
No nearby Gafni--Tao assumption was imported. This does
not close the general-parameter `add-bound (ii)`, `twelfth-bound`, the
independent endpoint-two source transfer, or any final `Add-est` clause.
All 21 public theorems
in these three modules have named audits and runner coverage, with ten
semantic regressions. The preserved Lemma 62 counterexample is unchanged.

## Exact critical-line source identity (EPZAE-21)

The next source-entry edge is now kernel-checked for actual patterns.
For an active integer interval `[a,b]`, the real cutoff is
`w(x)=smoothTransition(2(x-a)+1) smoothTransition(2(b-x)+1)`.
It equals the sharp indicator at every integer, including `a` and `b`,
and is supported in `[a-1/2,b+1/2]`. For an inhabited large-value set,
the actual pattern implies `N ≤ a ≤ b ≤ 2N`, hence support in `[N/2,3N]`.
Empty intervals are also handled exactly; they cannot support a large
ordinate because the actual threshold is positive.

`ZetaMellinEntry` derives the right-line identity from native Mellin
inversion and absolute sum/integral interchange, with the original
`n^(-it)` phase. `ZetaMellinContour` clears the pole of the real zeta
function, proves the finite rectangle residue formula, and identifies
the residue at `s=1-it` as `M_w(1-it)`. `ZetaMellinShift` proves
absolute integrability on the two vertical boundaries and vanishing
horizontal integrals, using native Abel bounds and smooth Mellin decay.
Its actual-pattern consumer proves, for every real ordinate,

```text
Σ_{n in indices} coeff(n) n^(-it)
  = M_w(1-it)
    + (1/(2π)) ∫_{u in ℝ} ζ(1/2+i(u+t)) M_w(1/2+iu) du.
```

The source-facing theorem is
`ZetaLargeValuePattern.polynomial_eq_critical_zeta_mellin`.
`exists_critical_zeta_mellin_large` selects one common cutoff for all
large ordinates. Neither theorem accepts an independent analytic estimate
or a supplied smooth-test hypothesis: the native test object is constructed
from the exact cutoff.

This green edge is only the exact identity. Its contour-tail constant
can depend on the fixed cutoff and ordinate. The separate quantitative
continuation below now proves uniform kernels, localization, and error
absorption; it does not infer them from fixed-cutoff convergence.
The dyadic twelfth moment remains open. The short-zeta continuation below
now supplies the short energy range from it. No final `Add-est` clause is
newly claimed.

All four modules are root-imported and inventoried by
`run_tao_trudgian_yang_build.bat`. Their 36 public theorems and actual
cutoff constructor have named audits; ten regressions cover endpoints,
empty intervals, physical support, the phase, and the explicit residue.
The counterexample and original source archives remain unchanged.

## Completed uniform Perron entry and moment-to-LV deduction (EPZAE-21)

For `a ≤ b`, the exact cutoff is the sum of its two endpoint transitions
minus one. Thus every positive derivative order has two fixed-width
pieces. `integral_norm_complex_cutoff_deriv_le` bounds its integral norm
by `zetaCutoffDerivativeMass j`, independent of `a,b,N,t`.
`mellin_derivative_recurrence` and `mellin_iteratedDeriv_norm` derive the
integration-by-parts factors from genuine smooth test functions, including
zero endpoint terms. These proofs consume the constructed derivative test,
not an independently assumed Mellin estimate.

The actual-pattern `cutoff_mellin_bound` gives
`|M_w(σ+iu)| ≤ C_j(σ) N^(σ+j-1)/(1+|u|)^j` for `σ ≥ 1/2`, `j ≥ 1`.
Its `j=1` critical-line specialization has the exact `sqrt(N)` factor.
The residue obeys `|M_w(1-it)| ≤ C_j(1) N^j/(1+|t|)^j`.
The constants are positive and depend only on the fixed transition, order,
and real line, not the actual pattern.

Outside the shifted window `[T/2-t,3T-t]`, actual `t ∈ [T,2T]` implies
`|u| > T/2` and `|t| ≤ 4|u|`. The native Abel bound and fourth-order
Mellin estimate give a multiple of `N^(7/2)|u|^(-3)`.
`cutoff_critical_far_integral` integrates this to
`120 C_4(1/2) N^(7/2)/T²`. The near integral is bounded by the literal
source convolution with no lost endpoints.

`polynomial_norm_le_convolution_and_errors` retains both error terms.
`perron_entry` then derives `V ≤ C sqrt(N) F_T(t)` for every actual large
ordinate under `T ≥ N^(7/4)` and `V ≥ 2 zetaPerronError`.
`exists_zetaPerron_uniform_threshold` derives those hypotheses from one
common large-`N` threshold and all source windows
`σ ≥ 1/2`, `τ ≥ 2`, `δ ≤ 1/4`. This closes the critical-line source-entry
edge, including its physical uniformity, not only its fixed-cutoff identity.

`zetaTwelfth_largeValueBound_of_dyadic` consumes this actual entry and
the proved convolution/logarithmic/window chain. It concludes
`IsZetaLargeValueBound σ τ (2τ-12(σ-1/2))`, with all constants and radii
chosen before the pattern. Its sole analytic theorem parameter is

```text
for every η > 0, there exist C ≥ 0 and T₀ such that for all H ≥ T₀, H > 0,
  integral_H^(2H) |ζ(1/2+iu)|^12 du ≤ C H^(2+η).
```

The parameter is a genuine upstream moment statement, not a cardinality,
energy, or density conclusion. It remains unproved.
`energyClauseOne_of_dyadic_moment_and_short_zeta` performs the complete
downstream deduction through the repaired witnesses, Heath--Brown relation,
and exact optimizations, retaining only this moment and short zeta energy
on `[1,2)` in its modular signature. The next continuation discharges
the latter premise from the former; no final `Add-est` clause is complete.

The six continuation modules now contain 39 named public theorem audits plus
the derivative-test constructor audit. Fourteen regressions check uniform
derivative mass, complexification, frequency zero, both source height
endpoints, explicit errors, actual-pattern entry, physical normalization,
closed exponent windows, uniform LV, and conditional final assembly.
They are root-imported and covered by `run_tao_trudgian_yang_build.bat`.
The original counterexample, source archives, and publication contracts
are unchanged.

## Short-zeta range discharged from the genuine moment (EPZAE-21/37)

The actual `perron_entry_with_scaled_error` retains the same residue and
far integral, but absorbs the error against `V`. If `T ≥ N^(23/16)`,
the far integral is at most `120 C_4(1/2) N^(5/8)`, while the residue
is bounded by `C_4(1) ≤ C_4(1) N^(5/8)`. Thus the entry follows when
`V ≥ 2 zetaPerronError N^(5/8)`. A single scale threshold derives these
hypotheses from every `σ ≥ 3/4`, `τ ≥ 3/2`, `δ ≤ 1/16` window.
`zetaTwelfth_short_largeValueBound_of_dyadic` consumes this entry and
the existing moment/window/logarithmic chain, including its constants
and physical exponents. It is conditional only on the genuine moment.

Below `3/2`, `polynomial_norm_le_short_majorant` proves, for the literal
coefficient-one sharp interval and `1 ≤ t ≤ N²`,

```text
|polynomial(t)| ≤ 2 + 200 sqrt(t) + 12 pi N/t.
```

The proof bounds two prefixes and retains the possible left endpoint
of `[N,2N]`. It consumes the native first-derivative bound when `t ≤ N`
and the native second-derivative bound when `N ≤ t ≤ N²`, with the exact
negative phase. For `1 ≤ τ < 3/2`, choose
`δ=(3/2-τ)/8` and `β=3/4-2δ`. The actual window puts the right side
below `K N^β`, whereas `V ≥ N^(σ-δ)` exceeds it eventually for `σ ≥ 3/4`.
`exists_zetaShort_empty_uniform_threshold` derives `W=∅`, rather than
restricting the definition of a pattern. Its consumers give every real
cardinality/energy bound and `zetaShort_largeValueExponent_eq_bot`.

On `[3/2,2]`, cubic energy gives the exponent
`3(2τ-12(σ-1/2))`. `energyClauseOne_short_cubic_bound` proves it is at most
`energyClauseOnePublicRate σ * τ`, using the exact comparison
`15-18σ ≤ energyClauseOnePublicRate σ` and closed height endpoints.
`energyClauseOne_short_zeta_of_dyadic` combines both ranges without a
short-zeta hypothesis. `energyClauseOne_of_dyadic_moment` then consumes
the existing corrected-witness, Heath--Brown, general/zeta optimization,
and endpoint-one transfer chain on the full `3/4 ≤ σ ≤ 5/6` interval.

Semantic completion audit: the two new green architecture edges are
`exists_zetaPerron_short_uniform_threshold` (actual windows to actual
pointwise entry) and `exists_zetaShort_empty_uniform_threshold` with
`zetaShort_largeValueExponent_eq_bot` (actual sharp patterns to genuine
nonexistence). The short-energy and final-clause nodes stay open because
their assembled public consumer still requires the dyadic twelfth moment.
It does not require a cardinality, short-energy, or zero-density conclusion.
The general endpoint-two source theorem is independently open; the
clause-(i) deduction uses the proved endpoint-one interface exactly.

The three added modules and the strengthened moment-to-LV module have
12 new public theorem audits and eight new regressions, with root imports
and principal-runner coverage. The counterexample is unchanged. The next
clause-(i) obligation is the actual twelfth moment, not the short-zeta input.

## Zeta nonexistence semantics and the source maximum

`ZetaLargeValueDiscreteness` and `ZetaPointwiseNonexistence` now prove
`LV_ζ < 0 iff LV_ζ = -∞ iff uniform eventual emptiness iff uniform
positive-height sharp-interval power saving`. The first step uses actual
integer cardinalities below one; the infimum-to-candidate step spends only
epsilon slack. The pointwise forward step builds the exact singleton
pattern at height `t`. The reverse step pays explicitly for `t ≤ 2T` by
using a quarter-radius window and a common threshold. No singleton
counterexample or pattern definition has been changed.

`zetaShort_pointwise_powerSaving` is an unconditional actual-interval
consumer for `σ ≥ 3/4`, `1 ≤ τ < 3/2`. The maximum-to-double theorem uses
the same discreteness when the base exponent is negative; at zero it
does not infer negative infinity. These 13 new public theorems have named
audits and eight boundary/consumer regressions. They repair the logical
branch reduction suggested by the online twelfth-moment proof, not its
still-missing analytic estimate. `energyClauseOne_of_dyadic_moment`
continues to require the genuine dyadic twelfth moment alone.

### Exact local mean-square entry toward the remaining moment

The six `ZetaSquare*` modules now prove a complete ordinary-divisor
series identity for the actual local second moment. They derive the
one-sided reflected contour, whole-line integrability, absolute
integrated-norm summability, Gamma normalization, compact-height
continuity, and the second sum--integral exchange.
`hasSum_zetaSquareLocalMean` has no moment or local mean-square premise.
It is not the sharp Atkinson inequality. Averaging is proved in the next
continuations, including the actual unit phase and uniform amplitude/source
remainder. Divisor shortening, oscillatory reduction, sharp Atkinson
remainders, and the dyadic twelfth moment remain open.
Thus `energyClauseOne_of_dyadic_moment` is still conditional.

The original singleton counterexample is unchanged. Nothing in this
entry modifies the repaired two witnesses or introduces an `s/k`
constraint. The goal and architecture retain the full route through
the moment to the unchanged nine `Add-est` clauses. All six modules,
47 named public theorem audits, and nine regressions are covered by
the root imports and maintained `run_tao_trudgian_yang_build.bat`.

### Uniform averaging continuation

Three further modules prove the actual Gaussian averaging step,
weighted divisor-series interchange, and whole-line source approximation
with a uniform `G T^(-A)` logarithmic-window tail. The width Jacobian
and common threshold are explicit. The quadratic Gaussian transform
also has a proved exact formula and physical frequency damping for
`G²≤2T`. These are 31 named public theorem audits and nine regressions,
all covered by the root imports and principal batch runner.

The unit-phase approximation and its uniform integrated error are now
proved below, followed by the uniform shifted-Gamma/pole approximation
and complete reflected-source remainder. Divisor shortening,
Voronoi/stationary reduction and the dyadic twelfth moment remain open.
Hence the repaired-witness/Heath--Brown/optimization
assembly of clause (i) is
still conditional on the same genuine moment; no final clause is
marked complete. The counterexample and unrestricted fifth coordinates
are unchanged.

### Actual phase continuation

The next four modules prove the actual digamma logarithmic estimate and
the reflected quotient `GammaR(1/2-it)/GammaR(1/2+it)`, including its
zeta functional-equation identity and exact source normalization. They
derive its real-frequency differential equation and closed-window
quadratic approximation. The whole-line Gaussian transform consumer
pays the finite integrated error and both omitted tails, then uses
the proved quadratic frequency damping. There are now 26 named public
audits and 12 regressions, all in the principal batch-runner inventory.

The shifted-Gamma amplitude in the source factorization is not set to
one or assumed controlled: the continuation below proves its uniform
estimate and consumes it in the complete reflected divisor series.
Divisor truncation, Voronoi/stationary reduction and the actual twelfth
moment remain open.
The repaired powering and Heath--Brown theorems are unchanged, and
`energyClauseOne_of_dyadic_moment` remains conditional. The original
counterexample remains byte-for-byte unchanged and audited.

### Uniform amplitude and complete reflected-series continuation

Seven further modules prove the actual shifted Gamma ratio and pole
amplitude, then combine near and far bounds into one height-independent
integrable majorant for the complete normalized kernel. The far estimate
uses the actual inverse Gamma normalization, not a fixed-height constant.
`hasSum_zetaSquareLeadingDivisorContribution` proves the complete leading
ordinary-divisor series. `exists_norm_zetaSquareDivisorIntegral_sub_leading_le`
consumes it and the original source integral to prove one uniform `O(1)`
remainder for all `t≥4`, with no moment hypothesis.

This adds 44 public audits, one newly public Gamma derivative audit,
and 14 boundary/source regressions, all in root imports and the inventory
behind `run_tao_trudgian_yang_build.bat`. That batch runner and the
foundation runner must continue to be updated and rerun with this chain.
Leading divisor weight bounds/height variation, shortening, Gaussian
assembly, Voronoi/stationary phase and the genuine dyadic twelfth moment
remain open. Thus clause (i) remains conditional; all final `Add-est`
clauses and the full EPZAE-00--41 goal are unchanged and incomplete.
The original counterexample and both independent fifth coordinates remain
preserved; this analytic continuation does not alter the repaired powering.
