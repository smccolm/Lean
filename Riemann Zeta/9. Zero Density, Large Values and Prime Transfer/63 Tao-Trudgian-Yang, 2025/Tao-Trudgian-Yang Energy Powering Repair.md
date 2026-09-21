# Authorized cardinality/energy powering repair

Current analytic progress: [Jutila physical-scale smoothing and uniform pattern bounds](#jutila-physical-scale-smoothing-and-uniform-pattern-bounds--current-checkpoint).
The moments and full-domain clauses (i)--(ii) are proved; clauses (iii)--(ix) and the full goal remain open.
Earlier checkpoint sections retain historical status and next-step notes;
the frozen public contract is unchanged.


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
and complete reflected-source remainder. Later continuations prove
divisor shortening and actual smooth Voronoi/Bessel entry. Uniform
stationary reduction and the dyadic twelfth moment remain open.
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
The following continuation proves weight bounds/height variation and
the complete quadratic Gaussian-window comparison. The later continuation
also proves source-scale shortening and actual smooth Voronoi/Bessel
entry. Uniform stationary phase and the genuine dyadic twelfth moment remain open.
Thus clause (i) remains conditional; all
final `Add-est` clauses and the full EPZAE-00--41 goal are incomplete.
The original counterexample and both independent fifth coordinates remain
preserved; this analytic continuation does not alter the repaired powering.

### Actual weight and Gaussian-source continuation

Nine additional modules prove the Mellin weight's reflection and bounded
small-index regime, its signed physical argument and height variation,
and the summed coefficient bound `Cε T^(1/2+ε)`.
Only the smooth weight is frozen: the phase and divisor oscillation
remain at `T+x`. The freezing error is `Cε |x| T^(-1/2+ε)` on
`T≥8`, `|x|≤T/2`.

The two actual contour branches are proved conjugate, giving
`|ζ(1/2+it)|²=2 Re(I(-t)/GammaNormalization(t))`, including `t=0`.
`exists_abs_zetaSquareGaussianWindow_sub_quadratic_le` then bounds
the actual Gaussian zeta window by its complete quadratic divisor
source plus explicit freezing, Gaussian-tail and phase-replacement
errors. Absolute integrated-norm summability justifies the exchange.
This is not a shortened sum or a twelfth-moment theorem.

The 78 public theorem audits, 20 regressions and nine root imports
are included in the backing inventory of `run_tao_trudgian_yang_build.bat`.
Keep that exact runner updated and rerun both principal runners as the
chain changes. No analytic theorem premise was added to these source
consumers. The moment premise in `energyClauseOne_of_dyadic_moment`
is still open. The counterexample, corrected independent fifth
coordinates and all repaired powering/Heath--Brown conclusions remain
unchanged.

### Source-scale finite divisor entry

Six further modules now prove actual finite frequency shortening,
uniform logarithmic Gaussian tails and the `Oδ(G log T)` error
for all `0<G≤T^(1/2-δ)`, beyond one threshold depending only on `δ>0`.
`exists_zetaSquareLocalMean_le_short_divisor` applies this to the
actual unsmoothed local zeta second moment, retaining the finite
oscillatory divisor source rather than assuming a moment estimate.
On `G≥T^δ`, its physical band has radius `T log T/(pi G)` about
`T/(2pi)`, with indices in `[T/(4pi),T/pi]`.

All 29 new public theorem audits and 18 semantic regressions are
covered by root imports and the inventory behind
`run_tao_trudgian_yang_build.bat`. Both principal runners remain
required as this chain changes. The next continuation proves the smooth
actual test and native Voronoi/Bessel entry. Uniform stationary
reduction, the sharp Atkinson estimate and genuine dyadic twelfth
moment are still open. No final
`Add-est` clause or full-goal completion is claimed.

The original Lemma 62 counterexample remains byte-for-byte unchanged,
as do the corrected independent fifth coordinates, powering and
Heath--Brown theorems. No new analytic theorem premise is used in the
finite source entry; the moment premise in the existing conditional
clause-(i) assembly is not discharged by it.

### Actual smooth Voronoi/Bessel entry

Eight modules now prove entire complex-weight smoothness, construct a
fixed-profile cutoff with positive compact support, pay every transition
term from the frequency tail, and consume native modulus-one Voronoi.
Both native transforms are identified with literal Bessel integrals,
retaining `-2pi`, `4`, the full logarithmic main term and `d(0)=0`.
`exists_zetaSquareLocalMean_le_bessel` is the actual source consumer,
with one constant and height threshold uniform in all
`0<G≤T^(1/2-δ)` for each `δ>0`. The associated physical Gaussian
identity has error `Cδ G log T`. None of these theorems assumes a
moment, smoothness, support or Voronoi input for the actual source.

The 43 public theorem audits and 18 regressions are covered by the
root imports and `run_tao_trudgian_yang_build.bat` inventory. The
goal retains both principal runners and all EPZAE-00--41 obligations.
The original counterexample is unchanged, as are the independent
corrected fifth coordinates and the powering/Heath--Brown theorems.
The following continuation discharges the complete modified-Bessel
branch. The remaining main/Y0 oscillatory estimates, sharp Atkinson
inequality and actual twelfth moment are not discharged; all
unconditional `Add-est` clauses and EPZAE-21/37 remain open.

### Complete modified-Bessel branch removed

Seven modules now prove the literal `K0` exponential bound and consume
the actual smooth source support, mass, absolute integrability and
ordinary-divisor series at two. The complete branch satisfies
`norm(VK)≤G T^(-A)` for every fixed real `A`, uniformly beyond one
height threshold on `T^δ≤G≤T^(1/2-δ)` for each `δ>0`.
`exists_zetaSquareLocalMean_le_main_minus` applies this proved bound
to the actual zeta local mean; the unchanged logarithmic main term
and oscillatory `Y0` sum remain, with error `Cδ G log T`.

This is not the Atkinson inequality or the genuine twelfth moment.
The later continuation proves the phase-adjusted main estimate;
sharp stationary estimates remain required. The
moment premise in the earlier conditional clause-(i) theorem is not
discharged. All unconditional `Add-est` outputs and EPZAE-21/37 stay
open. The 29 public audits and 16 regressions are included in root
imports and the `run_tao_trudgian_yang_build.bat` inventory; both
principal runners and the full goal remain required. The counterexample,
independent corrected fifth coordinates and powering/Heath–Brown
proofs are untouched.

### Source-required lattice phase and nondegenerate carrier saddle

Six additional modules now insert `exp(-2pi i x)` into the actual
continuous divisor test, following the conjugate-sign version of
Ivić (6.36). Every natural-index coefficient, norm and support is
proved unchanged; native Voronoi is applied to the newly constructed
smooth test. The new continuous integrals are not equated with the
old ones. The complete K0 bound transfers by its actual norm
majorant, with integrability, arithmetic convergence and a proved
`HasSum`. `exists_zetaSquareLocalMean_le_atkinson_reduced` is
the actual phase-adjusted local-source consumer, with uniform
`Cδ G log T` error on `T^δ≤G≤T^(1/2-δ)`.

The true cutoff, Mellin weight, Gamma factor and quadratic Gaussian
are retained in the amplitude. Exact carrier factorization and
derivatives give the unique positive saddle for both real signs,
and its second derivative is strictly negative. This is not a Y0
asymptotic expansion or a uniform stationary-phase estimate.
The phase-adjusted main estimate is proved below; the Y0 estimate
and genuine twelfth moment are still needed before the moment-to-energy consumer
can close clause (i). All unconditional `Add-est` outputs and
EPZAE-21/37 remain open. The counterexample, independent corrected
fifth coordinates and proved powering/Heath–Brown chain are preserved.

All six modules, 40 public audits and 22 regressions are included
in root imports and the backing inventory of
`run_tao_trudgian_yang_build.bat`. Both principal runners remain
required after Lean changes, and the full EPZAE-00--41 goal is
unchanged.

### Actual main integral removed from the phase-aligned source

Nine additional modules now prove and consume the phase-adjusted
logarithmic main-integral bound `C G log T`. All amplitude bounds
are constructed: the actual cutoff has uniformly bounded variation,
the actual Mellin weight is a fixed profile after `x/T` rescaling,
and the complex quadratic Gaussian's derivative is controlled by
its literal damping envelope. Its total variation is `O(G)`, not
a bound losing another power of G. The full amplitude has norm
and variation `O(G sqrt(T) log T)`; native logarithmic reflection
supplies `O(1/sqrt(T))` cancellation. Positive support, absolute
integrability and the exact main/reflection identity are proved.

`exists_zetaSquareLocalMean_le_atkinson_minus` now links the
actual zeta local mean to only the complete phase-adjusted Y0
divisor sum, with uniform `Cδ G log T` error on
`T^δ≤G≤T^(1/2-δ)`. The physical Gaussian companion is also
proved. The main term is not an assumed or discarded error.

All nine modules, 38 public audits and 20 regressions are covered
by the root and `run_tao_trudgian_yang_build.bat` inventory.
The goal retains both principal runners and every EPZAE-00--41
obligation. The original counterexample and proved independent
cardinality/energy powering and Heath–Brown chain are unchanged.
The literal Y0 expansion is proved and consumed below. Uniform stationary estimates, genuine
twelfth moment and unconditional Add-est outputs are not discharged;
EPZAE-21/37 remain open.

### Literal Y0 expansion consumed by the actual zeta source

Thirteen further production modules prove the exact decaying-ray
representation of the native Schläfli kernel and its two-term expansion
with explicit error `K x^(-5/2)` for every positive argument. Both
principal branches, the ray endpoint and Gamma moments are checked.
The source argument is linked to physical support and divisor index,
giving `T^(-5/4) n^(-5/4)` error. The actual divisor series at
`5/4` sums the complete remainder, with bound `C G`.

`exists_zetaSquarePhysicalGaussian_atkinson_twoTerm_approximation`
and `exists_zetaSquareLocalMean_le_atkinson_twoTerm` consume that
replacement. They retain the full two-term oscillatory series, its
`-2pi` normalization, source factors `2` and `2 exp(1)`, and
uniform `Cδ G log T` error on `T^δ≤G≤T^(1/2-δ)`.
There is no assumed Bessel estimate, summability or moment theorem.

All 71 public audits and 25 regressions are included in the root and
the backing inventory of `run_tao_trudgian_yang_build.bat`.
The goal requires that exact interface and `run_lake_build.bat`
after relevant changes. The original counterexample is byte-for-byte
preserved, and the corrected two independent witnesses and actual
Heath–Brown theorem remain proved. Uniform stationary estimates,
the sharp Atkinson inequality and the genuine twelfth moment are
still needed before the conditional clause-(i) route closes.
EPZAE-21/37, all unconditional Add-est outputs and the full goal
remain open; no verification or mathematical contract is narrowed.

### Actual signed carriers and frequency-uniform cancellation

Ten further modules prove cancellation for the actual power-weighted
source, uniformly in both carrier signs and every real carrier parameter.
The exact substitution `x=y²` gives
`q=(T/pi)log y-y²+2by`. Its slope factors at the actual positive
saddle r, and has magnitude at least two outside r±1.
The native first-derivative integral estimate, with a proved reflection
for the left tail, and the central interval of length at most two give
`norm(integral exp(2pi i q))≤4` on every positive interval.

The actual amplitude's derivative-norm integral is preserved under
the square substitution. Its constructed norm/variation bound and
integration by parts prove `|Iα(T,G,L,b)|≤Cα G T^(-α)`.
No amplitude, oscillatory estimate or analytic theorem is a premise.
Exact carrier algebra and integrability identify all four terms of
the genuine Neumann two-term source, including its quarter powers,
both signs and `d(n)(-2pi)` normalization.
The complete carrier series is genuinely summable by equality with
the source. The actual per-summand bounds have `n^(-1/4)` and
`n^(-3/4)` decay; those bounds alone are not summable.

`exists_zetaSquarePhysicalGaussian_carrier_approximation` and
`exists_zetaSquareLocalMean_le_carriers` retain that complete
series and the uniform `Cδ G log T` source error.
This does not prove stationary main values, sharper arithmetic
tails, the sharp Atkinson inequality or the genuine twelfth moment.
Thus the existing clause-(i) theorem still has its moment premise;
EPZAE-21/37 and every unconditional Add-est clause remain open.

All ten modules, 43 public audits and 24 regressions are included
in root imports and the backing inventory of
`run_tao_trudgian_yang_build.bat`. The goal retains this exact
runner and `run_lake_build.bat` after relevant changes.
The original counterexample remains byte-for-byte preserved.
The corrected independent cardinality/energy witnesses, actual
Heath–Brown theorem and full EPZAE-00--41 goal are unchanged.

### Complete correction removal on the moment route

The next actual analytic edge is now proved. Both signed carriers
gain `1/|b|` for `|b|≥8sqrt(T)` across the full physical
support. The native first-derivative estimate consumes the actual
slope bounds and the constructed amplitude variation.
Near frequencies instead use the earlier uniform cancellation.
Together these give a `C G/sqrt(n)` bound for the actual
correction pair and a summable divisor majorant at exponent
`5/4` after its exact quarter-power coefficient is included.

`exists_norm_atkinsonCorrectionSum_le` bounds the complete
correction by `C G`. The leading series is genuinely summable
by the proved source decomposition. Both physical zeta consumers
in `AtkinsonLeadingSource` retain only the complete leading
signed carriers and the uniform `Cδ G log T` error.
This is complete correction removal, not a stationary main-value
estimate for the leading source or a proof of the twelfth moment.
The clause-(i) moment premise and every unconditional Add-est
output remain open under the unchanged full goal.

Four new modules and the generalized weighted-primitive helper
add 19 named public audits and 16 regressions, all in the root
and exact `run_tao_trudgian_yang_build.bat` inventory.
Both principal runners remain required after relevant changes.
The original counterexample is unchanged, as are the repaired
independent coordinates and actual powering/Heath–Brown chain.

### Quantitative leading tail on the repaired moment route

The corrected two-witness powering and full Heath–Brown relation remain
proved; the original counterexample remains byte-for-byte intact.
The moment route now has constructed second-order bounds and an exact
signed Fourier identity for its actual leading carrier. The full
leading-series tail is bounded by C G T^(5/4) N^(-1/8), hence by C G
for N≥T^10. Both physical zeta consumers retain the finite actual
leading sum with Cδ G log T error on the original power-width range.
This is coarse polynomial truncation, not the sharp Atkinson formula.
The later continuations below prove evaluated stationary mains and
source-scale localization. The summed stationary error and genuine
twelfth moment remain missing; the Add-est clause-(i) premise is not discharged.

The fifteen new modules, 59 named public audits and 20 regressions are
covered by the root and `run_tao_trudgian_yang_build.bat` inventory.
Keep that runner synchronized and execute both principal evaluation scopes.
The complete EPZAE-00--41 goal remains active.

## Finite stationary reduction: downstream progress only

The corrected independent cardinality/energy witnesses and the full
Heath–Brown relation are unchanged. The original counterexample remains
byte-for-byte intact. Twelve additional moment-route modules now prove
paired source phases and the actual full carrier's finite-quadratic
stationary approximation. The natural amplitude scale G/sqrt(T),
cubic phase error and reciprocal-window tails are constructed; physical
containment is derived for both signs from 10000n≤T.

The finite quadratic integral is not an assumed Fresnel constant.
The sharp Atkinson estimate and genuine twelfth moment remain unproved;
therefore clause (i)'s explicit moment premise remains, and no
unconditional Add-est output is claimed. The full goal stays active.
Keep all 71 new public audits and 22 regressions in the root and
`run_tao_trudgian_yang_build.bat` coverage; update that runner as needed
and execute both evaluation scopes. Never reintroduce false s scaling.

## Evaluated stationary continuation: no change to the repair

The proved Fresnel value and uniform tail are now consumed by the actual
carrier. Both signed evaluated phases and physical source-width
per-carrier power saving are kernel-checked in nine modules, with
35 named audits and 16 regressions in the root and exact batch inventory.

This does not discharge the genuine twelfth-moment premise: sharp
localization, summed stationary errors and physical dyadic/Gram assembly
remain open. Unconditional Add-est is still open. Preserve Lemma 62's
counterexample byte-for-byte, the independent ρ/k and ρ*/k witnesses
and the proved Heath–Brown relation. Never restore false s scaling.
The goal remains active; maintain `run_tao_trudgian_yang_build.bat`
and rerun both principal evaluation scopes after relevant changes.

## Source-scale truncation: downstream progress with repair preserved

The actual complete leading tail is now O(G) beyond
N≥36T(log T/G)², and both physical zeta consumers use it.
An explicit ceiling cutoff connects every retained index to the
evaluated stationary estimates. This replaces the earlier coarse
polynomial truncation; it does not discharge the required summed
stationary error or genuine twelfth moment.

Eleven modules, 53 public audits and 22 regressions are in the root
and exact `run_tao_trudgian_yang_build.bat` inventory.
Keep both principal runners maintained and rerun them after changes.
Preserve the original counterexample byte-for-byte, the independent
ρ/k and ρ*/k witnesses and the proved Heath–Brown relation.
No false s scaling is restored; unconditional Add-est and the full
EPZAE-00--41 goal remain open.

## Symmetric stationary summation with the repair preserved

The downstream analytic chain now sums the stationary errors with actual
divisor and Bessel coefficients. Both physical zeta consumers prove
Cδ,ε (G log T+T^(1/4+ε)) on G≥T^(1/4), and Cδ,κ G log T on
G≥T^(1/4+κ), retaining the original power-width hypotheses.

This does not discharge smaller source widths, remaining main assembly
or the genuine twelfth-moment premise. Every unconditional Add-est clause
and the full goal remain open. The original counterexample is unchanged
byte-for-byte; the two independent powering witnesses and proved
Heath–Brown relation are preserved.

Ten modules, 43 named audits and 24 regressions are covered by the root
and exact `run_tao_trudgian_yang_build.bat` inventory. Maintain the
batch entry point and its PowerShell implementation, and rerun both
principal evaluation scopes after relevant changes.

## Normalized main and partial-summation checkpoint

Five new modules, 30 named audits and 24 regressions derive the actual
common fourth-root coefficient from the original saddle power, curvature
and Bessel constants. Both signed main sums retain separate cutoff/Mellin
weights. Only the raw phase sums are conjugated.

The actual weights have a proved uniform bound
C G T^(-1/4) n^(-1/4) exp(-G²n/(12T)) on n≤T,
T,G,L>0, G²≤2T and 8L≤G. The exact Abel bound retains literal finite
weight differences. Both physical zeta consumers are linked to the same
explicit source cutoff and normalized mains. Errors remain
Cδ,ε(G log T+T^(1/4+ε)) for G≥T^(1/4), or Cδ,κ G log T above
T^(1/4+κ), within the original power-width range.

The continuation below proves uniform damped variation and the actual
source-block bound. Global dyadic/Gram assembly, smaller source widths or
a proved lower-value-range reduction, and the genuine twelfth moment remain open. No unconditional Add-est clause is closed.
The original counterexample and corrected powering/Heath–Brown chain
are unchanged. The exact `run_tao_trudgian_yang_build.bat` inventory
is synchronized; maintain it and rerun both principal evaluation scopes.

## Damped variation and source-block checkpoint

Six new modules, from `FiniteWeightVariation` through
`AtkinsonPhaseBlockBound`, have 36 named public audits and 24 regressions.
The actual Gaussian increments telescope against a decreasing real
envelope. Ordered actual saddle samples, the constructed Mellin bound,
both original cutoff transitions and the decreasing fourth-root
coefficient give uniform variation for both separate normalized weights.

`exists_finiteVariationBound_atkinsonMainWeights` bounds both the
supremum on indices 0..N and the adjacent-difference sum by
C G T^(-1/4) m^(-1/4) exp(-G²m/(12T)), for
T,G,L>0, G²≤2T, m>0 and 10000(m+N)≤T.
No 8L≤G condition or conjugacy of residual weights is assumed.

The actual stationary Bessel/divisor block at m..m+N-1 is bounded by
that same shape times the maximum of the actual raw phase partial sums,
with a larger uniform C. `exists_atkinsonSourceCutoff_block_bound`
derives its small-frequency and scale conditions for every retained
block from the original power-width range and the exact source ceiling
cutoff, beyond a δ-dependent threshold.

ZVB records these proved consumers; the continuation below also proves
global dyadic assembly. The phase-sum/Gram bound, smaller-width stationary errors or a proved
lower-value-range reduction, and the genuine twelfth moment remain open.
The block theorem has no fourth-root-width restriction; the earlier
stationary-error/zeta consumer still does. No unconditional Add-est
clause or full EPZAE-00--41 completion is claimed.

The original counterexample and independent-coordinate powering/
Heath–Brown chain are unchanged. The exact
`run_tao_trudgian_yang_build.bat` root/audit/PowerShell inventory is
synchronized; maintain it and rerun both principal evaluation scopes.
See the Reproduction Manifest for the semantic audit and terminal evidence.

## Complete dyadic-source checkpoint

Three new modules, `TruncatedDyadicPartition`, `AtkinsonDyadicMain`
and `AtkinsonDyadicZetaConsumer`, have 20 named public audits and
24 regressions. The exact partition uses M=2^j and block length
min(M,N-M), for j<clog(2,N). Every retained endpoint stays at or below
the original cutoff; zero/one cutoffs and exact powers of two are covered.

The actual complete stationary Bessel/divisor series is now bounded by
C G T^(-1/4) times the sum of
M^(-1/4) exp(-G²M/(12T)) times the actual block phase-prefix maximum.
The same source ceiling cutoff supplies every block's small-frequency
geometry. Enlarging only the last raw phase maximum to a full block
does not enlarge the stationary source.

Four Gaussian/local-mean consumers use this complete dyadic bound.
Their error remains Cδ,ε(G log T+T^(1/4+ε)) for G≥T^(1/4), or
Cδ,κ G log T for G≥T^(1/4+κ), within the original power-width range.
The stationary-main bound itself has no fourth-root-width restriction.
ZDA records this exact assembly and these physical consumers.

Global dyadic assembly is now proved; the continuation below proves
finite maximal-prefix Gram assembly. The numerical phase-difference
estimates, source-form bridge, smaller-width errors or a proved
lower-value-range reduction, and the genuine twelfth moment remain open.
No unconditional Add-est clause or full-goal completion is claimed.

The counterexample and corrected powering/Heath–Brown chain are unchanged.
Maintain the synchronized root, audits, regressions and exact backing
inventory of `run_tao_trudgian_yang_build.bat`; run it and
`run_lake_build.bat` after relevant changes. The Reproduction Manifest
records the separate semantic and terminal integrity evidence.

## Height-dependent maximal Gram checkpoint

Eight production modules, from `FinitePrefixGram` through
`AtkinsonGramPhysicalCutoff`, add 41 named public theorem audits
and 24 `HeightDependentPrefixGramRegression` examples.

Finite Gram duality now consumes the actual divisor coefficients and
raw phase sums on [M,M+j). Each height has its own maximizing prefix;
the exact paired Gram entry uses the minimum of the two prefix lengths.
Its finite maximum has diagonal M and is symmetric in the two heights.
The separate arithmetic theorem proves coefficient energy
E(M,N)≤Cε M^(1+ε) for 0<M and N≤M; it does not assert a sharp
logarithmic divisor-square asymptotic.

The actual complete stationary packet and two actual local-mean excess
packets now consume the maximal Gram inequality. Their common cutoff is
derived from the source: for heights in [H,2H], it is bounded by
ceil(72H(log(2H)/G)²). The nonnegative Gram budget, not the stationary
source, is enlarged. Gaussian damping is removed by a proved upper bound;
the final budget retains literal coefficient energy E.

The stationary packet bound requires only the original power-width
range, eventually. The local-mean excess subtracts the proved error
Cδ,ε(G log t+t^(1/4+ε)) with G≥t^(1/4), or Cδ,κ G log t with
G≥t^(1/4+κ). Those restrictions are not discharged.
ZMG is DONE for finite maximal Gram assembly and these actual physical
consumers. The continuation below proves uniform truncated cancellation and its
physical consumers; ZGB retains separated-height summation and scale
optimization as open.

The source-form bridge, smaller-width error or a proved lower-value
reduction, genuine twelfth moment and unconditional Add-est remain open.
EPZAE-21/37 and the complete EPZAE-00--41 goal are unchanged.
The original counterexample and proved independent powering/
Heath–Brown chain remain intact; no false fifth-coordinate scaling returns.

Maintain all eight root imports, 41 named audits, 24 regressions and
the exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`.
Update that interface and its implementation as needed, and run it and
`run_lake_build.bat` after relevant changes. The Reproduction Manifest
records semantic fidelity separately from terminal build/audit evidence.

## Uniform truncated cancellation and numerical source budgets

Thirteen production modules, from `AtkinsonIndexPhase` through
`AtkinsonArithmeticGapPackets`, add 79 named public theorem audits
and 30 `TruncatedPhaseCancellationRegression` examples.

The literal source phase now has proved real-index slope, curvature,
height variation and uniform box bounds. Native second-derivative
cancellation and decreasing-increment Kusmin–Landau are applied to
every prefix [M,M+j), j≤N, with fixed ambient parameters. The result
covers empty prefixes, both height orders and the exact diagonal.
It is not an application of a full-block bound to an unknown prefix.

The resulting numerical entry majorant takes the minimum of N, the
explicit B-process expression and, when its exact half-period condition
holds, the reciprocal-gap first-derivative bound. It retains the physical
height gap and radical scales; no oscillatory sum remains in this
majorant.

The actual cutoff at 2H supplies every full block's two extra mean-value
endpoints: eventually 2*ceil(72H(log(2H)/G)²)+2≤H from H^δ≤G.
That lower-width condition is derived from an actual height in a
nonempty source packet; empty packets are handled separately.

All three actual stationary/local-excess packets consume the numerical
entry bounds. The final `arithmeticGap` versions also consume
E(M,M)≤Cη M^(1+η), yielding the explicit dyadic weight M^(1/2+η).
Their right sides have no unevaluated phase sum or coefficient-energy
sum. The local-mean errors and G≥t^(1/4), or G≥t^(1/4+κ), remain
unchanged; the stationary-only bound has no such restriction.

ZPC is DONE for uniform truncated cancellation, derived physical
geometry and these actual numerical consumers. ZGB is OPEN for
separated-height summation of the explicit gap bounds and scale
optimization. No height-separation estimate is claimed by the present
finite double sum. The source-form bridge, smaller-width error or a
proved lower-value reduction, genuine twelfth moment and unconditional
Add-est remain open. EPZAE-21/37 and the full EPZAE-00--41 goal are
unchanged.

Maintain all thirteen root imports, 79 named audits, 30 regressions and
the exact backing inventory of `run_tao_trudgian_yang_build.bat`.
Update that interface and its implementation as needed and run both
principal evaluation scopes. The original counterexample remains
byte-preserved, with the corrected independent powering witnesses and
actual Heath–Brown application intact. No false fifth-coordinate
scaling or third witness returns. See the Reproduction Manifest for
the separate semantic and terminal verification evidence.

## Constructed covering and local-mean counts — preceding checkpoint

EPZAE-21 now proves a sixth-power superlevel counting estimate for
the actual critical-line local zeta integral. For every δ>0, ε>0
and ν>0 there are C,D>0 and H0≥40000, before H,G,Y,W, such that

```text
card {t in W : C*(G*log(t)+t^(1/4+ε)) + Y
                 <= integral_(t-G)^(t+G) |zeta(1/2+i*u)|^2 du}
 <= D*H^ν * (H/(G*Y^2) + H^2/Y^6).
```

The hypotheses are H≥H0, G>0, Y>0, G-separation of W, and for
each t in W, `H<=t<=2H`,
`t^δ<=G<=t^(1/2-δ)`, and `t^(1/4)<=G`.
The above-fourth-root version instead has error `C*G*log(t)`
and requires `t^(1/4+κ)<=G`, κ>0. All source restrictions
remain explicit. Both theorems count the literal integral's
superlevel set; no analytic packet estimate, prescribed covering,
absorption inequality or cardinality bound is a premise.

The preceding physical packet theorem remains installed:
the square of the sum of actual excesses is at most
`D0*H^a*(R*H/G+R^2*sqrt(G*L))`, with uniform constants
before the localization interval. Its cutoff/logarithmic optimization,
including the literal source ceiling and derived width bounds,
is unchanged.

The new deduction constructs the length and bins. Put
`A=D0*H^a` and `L=(Y^2/(4*A))^2/G`. Then L>0 and

```text
sqrt(G*L) = Y^2/(4*A)
2*A*sqrt(G*L) <= Y^2.
```

The bin of t is `floor((t-H)/L)`. Its actual fiber is contained
in `[H+k*L,H+(k+1)*L]`; the bins partition W for
`0<=k<floor(H/L)+1`. This includes the terminal height 2H,
even when H/L is integral. Separation and every original source
range are inherited by each fiber.

On a fiber whose actual excess is at least Y, the packet inequality
and the proved absorption give `R<=2*A*H/(G*Y^2)`.
Summing the exact fiber cardinalities and paying the final bin gives

```text
card(W) <= 2*A*H/(G*Y^2) + 32*A^3*H^2/Y^6.
```

Choosing the packet exponent a=ν/3 and absorbing constants yields
the displayed global estimate. The exact positive-threshold
equivalence between excess≥Y and integral≥error+Y is proved,
then used on the actual filtered superlevel set.

Four root-reachable modules are installed:
`AtkinsonCardinalityAbsorption`, `AtkinsonHeightCover`,
`AtkinsonGlobalCardinality` and `AtkinsonLocalMeanCounting`.
All 17 new public theorems have named audits. The 27 new regressions
cover every public theorem type, exact chosen-length arithmetic,
empty fibers, unit/terminal bins, zero threshold geometry and the
complete source-consumer signatures. Earlier work remains installed.

ZLC is complete for constructed covering, absorption and actual
local-mean superlevel counting. This is not yet a pointwise zeta
large-value count: the entry from point values to these local
integrals, a compatible physical width choice, an occupancy-preserving passage
from unit-separated points to G-separated local windows, and the
remaining value-range reduction are still required. ZGB, ZAT, the genuine
critical twelfth moment ZTM, all unconditional Add-est conclusions,
EPZAE-21/37 and the full EPZAE-00–41 goal remain OPEN.

Preserve the original Lemma 62 counterexample byte-for-byte.
The corrected independent ρ/k and ρ*/k witnesses, independent
fifth coordinates and actual Heath–Brown application are unchanged.
Never restore false s-scaling or a third s-preserving witness.
Maintain and update `run_tao_trudgian_yang_build.bat` and its
backing implementation as needed; its exact inventory includes
all four new modules. Run it and `run_lake_build.bat` after
relevant changes. Keep the full goal active.

Verification (2026-09-21): both principal runners reached terminal
exit 0 with zero Lean errors, warnings, tactic suggestions and linter
failures. The target audited 2,847 declarations (2,842 discovered
target theorems plus five imported contracts); all 27 new regressions
passed. Exact commands, logs, hashes and coverage are in the current
Reproduction Manifest. This verifies local-integral superlevel counting,
not pointwise zeta large values, the twelfth moment or Add-est.

## Point-entry kernels and literal zeta overlap — preceding checkpoint

The preserved Lemma 62 counterexample and the proved corrected two-witness
powering/Heath–Brown chain are unchanged. EPZAE-21 now additionally proves
the Gamma-kernel and bounded-overlap components needed for point-value entry.

For every 0<δ≤1/4 and a,b independently chosen from {δ,-δ}, the
literal product

```text
P(a,b,u,w) = |Gamma(a+i*w)| |Gamma(b+i*(u-w))|
```

is integrable in w, and a single absolute C>0 gives
`integral P <= (C/δ)*exp(-|u|)`. The public consumer
`exists_pointMeanGammaProduct_integral_le` derives integrability and
uses both proved shifted-Gamma bounds and the numerical convolution.
Its height-linked companion
`exists_pointMeanGammaProduct_log_integral_le` substitutes
δ=1/log(t), derives 0<δ≤1/4 from t≥exp(4), and proves
`integral P <= C*log(t)*exp(-|u|)`. Both displacement signs and
zero ordinate are retained; no Gamma or convolution estimate is assumed.

For a unit-separated finite W, the actual exponential kernels satisfy
`sum_(t in W) exp(-|t-u|) <= 4`. The moving-window consumer
`sum_truncated_exp_kernel_zeta_sq_le_localSecondMoment` proves

```text
sum_(t in W) integral_(t-L)^(t+L)
  exp(-|t-u|) |zeta(1/2+i*u)|^2 du
 <= 4 * integral_(center-G)^(center+G) |zeta(1/2+i*u)|^2 du.
```

It assumes G,L≥0, W⊂[center-G/2,center+G/2],
G/2+L≤G and unit separation. It derives every interval enlargement
and finite integral interchange. The cost is the absolute factor four,
not the cluster occupancy or the physical width G.

The previously proved local-integral superlevel count remains:
`card <= D*H^ν*(H/(G*Y^2)+H^2/Y^6)`, with all original physical
width restrictions, actual source errors, positive thresholds and
uniform constant dependencies retained. This new overlap theorem does
not yet connect pointwise zeta largeness to that count.

Eight root-reachable modules are installed: `PointMeanDigamma`,
`PointMeanGammaShift`, `PointMeanGammaDecay`, `PointMeanGammaKernel`,
`PointMeanGammaConvolution`, `PointMeanExponentialOverlap`,
`PointMeanIntegralOverlap` and `PointMeanGammaProduct`.
All 38 public theorems have named audits; 46 new regressions cover
their exact types and shell endpoints, empty sets, zero ordinates,
and the negative displacement. Seven modules adapt inspected node-74
proofs to the existing target/native imports and actual
`zetaMomentCriticalNorm`; the eighth supplies new literal Gamma consumers.
No adjacent package, dependency pin, source archive, or frozen foundation
has been changed.

ZGK is complete only for the literal Gamma convolution and its
height-linked logarithmic bound. ZEO is complete only for the actual
exponential local-integral overlap. The complete contour proof of
Heath–Brown Lemma 3 is NOT yet installed in this target. Its residue,
displaced zeta bounds, horizontal edges, truncated tail and compact range
remain to be assembled. Pointwise large-value counting also still needs
occupancy-aware clustering, compatible G selection and the lower-value
reduction. ZGB, ZAT, ZTM, unconditional Add-est, EPZAE-21/37 and the full
EPZAE-00–41 completion contract remain OPEN.

Preserve `EnergyPoweringObstruction.lean` byte-for-byte. Never restore
false s-scaling or a third s-preserving witness. The independent ρ/k and
ρ*/k witnesses and actual Heath–Brown application remain intact.
Maintain and update `run_tao_trudgian_yang_build.bat` and its backing
implementation as needed, including all eight modules in the exact
inventory. Run it and `run_lake_build.bat` after relevant changes.
Keep the full goal active.

Verification (2026-09-21): both principal runners reached terminal
exit 0 with zero Lean errors, warnings, tactic suggestions or linter
failures. The target audited 2,890 declarations (2,885 discovered
target theorems plus five imported contracts); all 46 new regressions
passed. The foundation audit covered 14,290 declarations and its
manifest reports PASS with no failed stages. Exact logs and hashes
are in the current Reproduction Manifest. This verifies the Gamma
and overlap components, not the still-open pointwise zeta entry,
twelfth moment or unconditional Add-est.

## Heath–Brown point-to-local-mean entry — historical checkpoint

The original Lemma 62 counterexample is preserved byte-for-byte. The corrected
independent cardinality and energy witnesses, and their proved Heath–Brown
application, are unchanged. This checkpoint closes an analytic input to the
remaining zeta/Add-est branch; it does not change the frozen public outputs.

`heathBrownLemmaThree_native` now proves the complete source-shaped estimate:
one absolute C>0 works for every t≥10,

```text
|zeta(1/2+i*t)|^2
 <= C*log(t)*(1 + integral_(-log(t)^2)^(log(t)^2)
      exp(-|u|)*|zeta(1/2+i*(t+u))|^2 du).
```

The proposition and moment definitions unfold to this literal integral.
The proof derives the smoothed divisor Mellin identity, both pole residues,
the infinite shifts, both displaced-line estimates, the finite rectangle's
four edge bounds, the full-to-truncated tail estimate and the compact range.
The strong Gamma reserve makes the nested integral lose only δ⁻¹;
δ=1/log(t) is linked to the source height. None of these estimates is an
analytic hypothesis of the final theorem.

`heathBrown_equation44_native` consumes that theorem and the actual
factor-four exponential-overlap theorem. For R=card(W) it proves

```text
V^2*R <= C*log(T)*(R + 4*integral_(center-G)^(center+G)
                                  |zeta(1/2+i*u)|^2 du).
```

Here T≥10, V>0, G,L≥0; W is unit-separated and contained in
[center-G/2,center+G/2]⊂[10,T]; every t∈W has log(t)^2≤L;
G/2+L≤G; and every t∈W satisfies V≤|zeta(1/2+i*t)|.
All parameters follow the absolute constant. The final consumer has no
Lemma-3 hypothesis and does not discard cluster occupancy.

Nineteen additional production modules are root-reachable and included in
the exact inventory behind `run_tao_trudgian_yang_build.bat`.
There are 129 new public theorem audits and 136 new regressions, including
the unfolded literal source inequality and the endpoints t=10 and t=exp(4).
The adjacent node-74 proof bodies were inspected and adapted to existing
target/native imports; unrelated import chains were not added. No package
pin, source archive, counterexample or adjacent project was changed.

ZL3 is complete for the full source Lemma 3; ZQ44 is complete for its
literal finite peak-to-local-integral consumer. ZGB still needs constructed
occupancy-aware clusters, compatible physical width selection, absorption
of the actual local-source error, and the remaining value ranges.
The installed local-integral superlevel count still has its original
fourth-root width restrictions. ZAT, ZTM, unconditional Add-est,
EPZAE-21/37 and the full EPZAE-00–41 goal remain OPEN.

Keep the complete goal active. Preserve `EnergyPoweringObstruction.lean`
and the independent fifth coordinates; never reintroduce false s-scaling
or a third s-preserving witness. Maintain the principal
`run_tao_trudgian_yang_build.bat`, its backing implementation, root imports,
exact inventory, audits and regressions as the proof grows. After relevant
changes, run both it and the foundation's `run_lake_build.bat`.

Verification (2026-09-21): both principal scripts were polled to terminal
exit 0. The target reports `LEAN VERIFICATION PASS`, covering all 299
package files and 3,104 audited declarations (3,099 discovered target
theorems plus five imported contracts). All 129 new named audits and
136 new regressions pass. The foundation reports `PASS`, with 14,290
discovered theorems audited and all six stages passed. Neither final
evaluation has a Lean error, warning, tactic suggestion or linter failure.
Exact logs, hashes and the repaired intermediate comment-scan failure are
recorded in the current Reproduction Manifest. The counterexample hash is
unchanged. This verifies Lemma 3 and the finite point-entry consumer;
occupancy-aware counting, the genuine twelfth moment, unconditional Add-est
and the full goal remain open.

## Occupancy-preserving peak count and derived growth — historical checkpoint

The printed Lemma 62 counterexample is still byte-preserved. The proved
corrected two-witness powering, independent fifth coordinates and actual
Heath–Brown energy application are unchanged.

Three additional EPZAE-21 consumers are now proved:

- `exists_pointValue_card_le_with_width` counts the original unit-separated
  zeta peaks, retaining every cluster occupancy. Half-G floor bins keep
  occupied centers in [H,2H], including the terminal endpoint. Both parity
  classes are G-separated. The actual equation-(44) entry and Atkinson
  excess count bound each occupancy superlevel; exact layer-cake summation
  and the inverse-square sum recover all points with no factor G loss.
- `exists_pointValue_card_le_source_range` constructs
  G=V²/(K log(3H)²), absorbs the actual source error and derives all window
  and width conditions. For δ,κ,ν>0 with δ≤1/4, there are K,D>0 and H₀≥40000,
  chosen before H,V,W, such that for H≥H₀ and V>0,
  `K log(3H)² (2H)^(1/4+κ) ≤ V² ≤ K log(3H)² H^(1/2−δ)`,
  every unit-separated W⊂[H,2H] with |ζ(1/2+it)|≥V satisfies
  `card(W) ≤ D H^ν (H log(3H)^4/V^6 + H² log(3H)^6/V^12)`.
  The fourth-root margin is retained, not removed.
- `exists_zetaMomentCriticalNorm_lt_sixth_power` proves that for every ε>0
  there is H₀≥40000 such that H≥H₀ and H≤t≤2H imply
  |ζ(1/2+it)|<H^(1/6+ε). A singleton peak at H^(1/6+η),
  η=min(ε,1/48), satisfies the proved source range but its cardinality bound
  is eventually less than one. This derives the actual zeta growth estimate;
  it does not assume one or substitute a Dirichlet-block estimate.

The six modules `FiniteOccupancy`, `PointClusters`, `PointClusterEntry`,
`PointClusterCounting`, `PointValueWidth` and `PointValueGrowth` are covered
by the root and exact production inventory. Their 29 public theorems have
named audits, and 37 added regressions check every public type plus actual
endpoints, occupancy, parity and the unfolded zeta-growth conclusion.

Architecture nodes ZOC, ZVW and ZPG record these exact consumers as DONE.
ZGB remains OPEN for the remaining value-range reductions and their
moment-ready aggregation. ZAT's smaller-width/source-form bridge, the genuine
dyadic twelfth moment ZTM, all unconditional Add-est clauses, EPZAE-19/21/37
and the full EPZAE-00–41 goal remain OPEN. This critical-line growth result
does not complete the distinct exponent-pair-to-mu contract EPZAE-15.

Maintain `run_tao_trudgian_yang_build.bat` and its backing implementation as
needed: root imports, exact inventory, named/exhaustive audits and regressions
must grow together. Run both principal scripts after relevant changes.
Preserve the counterexample and do not restore false s-scaling or a third
s-preserving witness. No dependency pin, source archive or adjacent proof
was changed in this checkpoint.

Verification (2026-09-21): both principal runners reached terminal exit 0.
The target reports `LEAN VERIFICATION PASS`: 305 package files, 316 Lean
files in its integrity scan, 3,187 audited declarations (3,182 discovered
target theorems plus five imported contracts), all 29 new named audits and
all 37 added regressions passed. The foundation reports `PASS`: all six
stages passed and 14,290 discovered theorems audited. Both final evaluations
have zero Lean errors, warnings, tactic suggestions or linter failures.
The counterexample SHA256 is unchanged. Exact logs, hashes and repaired
focused-build diagnostics are recorded in the current Reproduction Manifest.
This verifies the occupancy/width consumers and actual critical-line growth,
not the genuine twelfth moment, unconditional Add-est or the full goal.

## High-value twelfth moment and fourth-moment reduction — historical checkpoint

The printed Lemma 62 counterexample is preserved byte-for-byte. Corrected
cardinality/energy powering, the independent ρ/k and ρ*/k witnesses with
independent fifth exponents, and the actual Heath–Brown energy application
remain unchanged.

The following actual-zeta consumers are now proved. Write
S(H,V)={t∈[H,2H] : |ζ(1/2+it)|≥V}. For every ε>0 and sufficiently large H,
uniformly for V≥H^(1/8+ε):

- `exists_pointValue_twelfth_weighted_card_le` gives
  card(W) V^12≤H^(2+ε) for every unit-separated W⊂S(H,V).
  There is no upper-amplitude hypothesis: the proved actual growth estimate
  controls that range, and the source-width and logarithmic margins are paid.
- `exists_volume_pointValueSuperlevel_le` gives
  volume(S(H,V))≤2H^(2+ε)/V^12. A maximal finite separated family is
  constructed from the proved cardinality bound; its closed unit balls
  cover the entire superlevel set, with the factor two accounted for.
- `exists_zeta_twelfth_high_integral_le` proves
  integral over S(H,H^(1/8+ε)) of |ζ(1/2+it)|^12≤H^(2+ε).
  The actual measure bound, actual height-cube bound for |ζ|^12 and exact
  logarithmic layer-cake integral are composed without analytic hypotheses.

`zeta_twelfth_integral_le_high_add_fourth` proves the exact low/high
reduction: the full twelfth moment on [H,2H] is at most the high-set
integral plus V^8 times the unweighted fourth moment on [H,2H].
`zeta_twelfth_dyadic_of_fourth` performs the full deduction but is
explicitly CONDITIONAL on the genuine upstream estimate

```text
for every η>0 there exist C≥0 and H₀, chosen before H, such that
H≥H₀ and H>0 imply integral_H^(2H) |ζ(1/2+it)|^4 dt ≤ C H^(1+η).
```

That unweighted fourth-moment instance is still OPEN. The foundation's
`twistedZetaFourthMoment_native` instead bounds the fourth power of a
short Möbius polynomial multiplied by ζ; its factor cannot simply be
removed. No mollified result is claimed to prove the unweighted estimate.

The six modules `PointValueRanges`, `PointValueMeasure`,
`TruncatedLayerCake`, `PointValueTailIntegral`,
`PointValueHighMoment` and `PointValueLowMoment` are in the root and exact
production inventory. All 24 public theorems have named audits; 30 new
regressions cover their exact signatures, boundary cases and the literal
high-value zeta integral. ZHR/ZHM and the reduction ZLF are DONE; ZGB now
identifies the missing genuine fourth-moment source theorem. ZTM, ZAT,
EPZAE-19/21/37, unconditional Add-est and the full EPZAE-00–41 goal remain OPEN.
No other frozen public output or acceptance test is weakened.

Maintain `run_tao_trudgian_yang_build.bat` and its backing implementation
as needed, including root imports, exact module coverage, named/exhaustive
audits and regressions. Run both principal scripts after relevant changes.
Preserve the counterexample, never restore false s-scaling or a third
s-preserving witness, and keep the full goal active. No source pin,
archive or adjacent/native proof was changed in this checkpoint.

Verification (2026-09-21): both principal scripts reached terminal exit 0.
The target reports `LEAN VERIFICATION PASS`: 311 package files, 322 Lean
files in its integrity scan, 3,232 audited declarations (3,227 discovered
target theorems plus five imported contracts). All 24 new named audits
and all 30 added regressions pass. The foundation reports `PASS`: all six
stages passed, with 14,290 discovered theorems audited. Both final
evaluations have zero Lean errors, warnings, tactic suggestions or linter
failures. The counterexample SHA256 is unchanged; source and runner hashes
were rechecked after both gates. Exact logs, hashes and repaired focused
diagnostics are in the current Reproduction Manifest. These gates verify
the high-value bound and explicitly conditional fourth-moment deduction,
not the missing fourth-moment instance, unconditional Add-est or full goal.

## Actual fourth-moment contour bounds and mixed-line truncation — historical checkpoint

The printed Lemma 62 counterexample is preserved byte-for-byte. The
authorized corrected cardinality/energy powering, independent ρ/k and
ρ*/k witnesses (with independent fifth exponents), and actual Heath–Brown
energy application remain unchanged. False s-scaling is not restored.

The new source is genuinely unweighted zeta. Write
J(t)=zetaSquareDivisorIntegral(-t)/zetaSquareGammaNormalization(t).
`zetaSquareNorm_eq_two_re_fourthRightPiece` proves
|ζ(1/2+it)|²=2 Re J(t), and `zeta_fourth_le_four_mul_rightPiece_sq`
proves |ζ|⁴≤4|J|². The actual Gamma quotient and pole factors are retained;
the native mollified fourth-moment theorem is not substituted.

`exists_norm_zetaFourthKernel_le` proves, for each c>0, a constant K_c>0
chosen before t and u such that t≥4 and t≥4c imply
|K(t,c+iu)|≤K_c t^c exp(-98u²) on the complete line. Near-height
Gronwall bounds and far-height Gamma bounds are both consumed.
A separate, height-dependent strip bound justifies holomorphy,
integrability and disappearing horizontal sides; it is not advertised
as the uniform moment bound.

`zetaFourthContribution_line_eq` proves equality of each actual
integrated ordinary-divisor contribution on any two positive lines.
`hasSum_zetaFourthContribution` transports the convergent integrated
series from c=1. This does NOT assert pointwise Dirichlet-series
convergence to the left of its half-plane.

For t≥0, a,b>0 and any finite S, the actual source now satisfies
J(t)=Prefix(t,a,S)+Tail(t,b,S). The prefix is proved equal to the
integral of the finite ordinary-divisor polynomial times the actual kernel.
For b>3/2, one constant K_b>0 works for all t≥max(4,4b) and all S:
|Tail|≤K_b t^b Σ_(n∉S) d(n)n^(-1/2-b).
The displayed positive tail is summable, not an assumed small error.
`exists_zeta_fourth_le_prefix_add_weightTail` consumes these results
to bound the literal |ζ|⁴ by eight times the squared prefix norm plus
eight times the squared displayed tail bound.

Twelve new `ZetaFourth*` modules are root-reachable and in the exact
production inventory; 53 public theorems have named dependency audits.
Sixty new regressions cover every signature, zero/empty/singleton cases,
different contour lines and literal critical-zeta consumers. The final
principal-runner evidence is recorded below.

Z4K (uniform kernel) and Z4C (actual mixed-line truncation) are supporting
results, not the unweighted fourth-moment theorem. ZGB still requires the
finite-polynomial mean square, quantitative cutoff-tail decay and their
integrated assembly. Thus ZGB/ZTM/ZAT, EPZAE-19/21/37, unconditional Add-est
and the full EPZAE-00–41 goal remain OPEN. No frozen public contract is
weakened, and no source pin, archive or adjacent/native proof is changed.

Maintain `run_tao_trudgian_yang_build.bat` and its backing implementation
as needed: exact module coverage, root imports, named/exhaustive audits and
regressions are part of the goal. Run it and `run_lake_build.bat` after
relevant changes; a passing audit establishes integrity, not completion
of the missing moment or of all advertised Add-est clauses.

Verification (2026-09-21): both principal scripts reached terminal exit 0.
The target reports `LEAN VERIFICATION PASS`: 323 package files, 334 Lean
files in its integrity scan, 3,296 audited declarations (3,291 discovered
target theorems plus five imported contracts). All 53 new named audits
and 60 added regressions pass. The foundation reports `PASS`: all six
stages passed and 14,290 discovered theorems audited. Both final
evaluations have zero Lean errors, warnings, tactic suggestions or linter
failures. The counterexample is byte-preserved; all source/runner hashes
were rechecked after both gates. Exact logs, hashes and the repaired
comment-scanner false positive are in the current Reproduction Manifest.
These gates verify the actual contour and truncation consumers, not the
missing fourth-moment integral, unconditional Add-est or the full goal.

## Unweighted moments and Add-est (i) — historical checkpoint

The printed Lemma 62 singleton counterexample is preserved byte-for-byte.
The corrected theorem still returns independent ρ/k and ρ*/k witnesses,
with independent existential fifth coordinates. No false s'/s scaling or
third s-preserving witness is restored.

`zeta_fourth_dyadic` now proves the genuine unweighted estimate: for every
η>0, constants C≥0 and H₀ are chosen before H, and H≥H₀, H>0 imply
integral_H^(2H) |ζ(1/2+it)|⁴ ≤ C H^(1+η).
It consumes the actual normalized divisor-contour source, not the native
mollified fourth moment and not an assumed fourth-moment bound.

The finite prefix is exactly {1,...,2^M}, including its first coefficient.
Unit-modulus endpoint twists prove a mean square uniform under every real
imaginary translation u, including the reflected phase u-t. The ordinary
divisor coefficient-square bound is derived from the native divisor bound.
Weighted Cauchy–Schwarz, product integrability and Fubini are proved for the
actual Gaussian kernel and complete finite polynomial.

The separate right line b=2+2/δ gives an actual bounded tail when
N≥H^(1+δ), uniformly for H≤t≤2H. A dyadic N between H^(1+q) and
2H^(1+q), with q=min(η,1)/20, pays the block-count loss. The exact exponent
1+5q+2q² is at most 1+7q≤1+η. Neither the cutoff error nor the polynomial
mean square remains a theorem parameter.

`zeta_twelfth_dyadic` applies the installed high/low decomposition to this
proved fourth moment. For every ε>0 it gives constants D≥0 and H₀ before H:
integral_H^(2H) |ζ(1/2+it)|¹² ≤ D H^(2+ε).
`zetaTwelfth_largeValueBound` and its short-height companion discharge
the actual Perron consumers: LV_ζ≤2τ−12(σ−1/2) for σ≥1/2, τ≥2,
and for σ≥3/4, τ≥3/2, respectively.

`add_est_i` in `NewAdditiveEnergy.lean` proves the literal printed clause on the entire
closed interval 3/4≤σ≤5/6:

```text
A*(σ)(1−σ) ≤ max((18−19σ)/(2(3σ−1)), 4(10−9σ)/(5(4σ−1))).
```

The actual declarations are `add_est_i`, `add_est_i_bound` and
`add_est_i_zero_energy` in `NewAdditiveEnergy.lean`.
The last exposes ∀ε>0 ∃C≥1 ∃δ>0 ∀T≥C, with the genuine shifted zero
energy at σ−δ, preserving analytic multiplicities and unit tolerance.
The epsilon--delta bound is proved first; the extended-real infimum
inequality is its consequence, not a substitute. At σ=3/4 the rate is
3/2 and A*≤6; at σ=5/6 the rate is 6/7 and A*≤36/7.

The dependency chain consumes corrected powering, the actual Heath–Brown
energy relation, certified general/zeta optimization, the proved twelfth
moment, and the proved endpoint-one zero-energy transfer. The separate
EPZAE-33 endpoint-two theorem is not assumed and remains open.

Seventeen new production modules are root-reachable and explicitly listed
in the batch runner's inventory. All 49 new public theorems have named
dependency audits. Sixty-one new regressions cover every public signature,
literal zeta integrals, coefficient/prefix endpoints, negative translated
intervals, both LV threshold boundaries and both printed energy endpoints.

ZGB, ZTM and clause (i)'s actual zeta/short-energy consumers are proved.
The other eight Add-est clauses, their remaining optimization certificates,
the separate sharp Atkinson source-form theorem, the other EPZAE-19/21
inputs, and the exponent-pair/density outputs remain OPEN. EPZAE-36/37 and
the full EPZAE-00–41 goal are not complete; the frozen contract is unchanged.

Keep `run_tao_trudgian_yang_build.bat` and its backing implementation
synchronized with root imports, exact inventory, named/exhaustive audits
and regressions. Run it and `run_lake_build.bat` after relevant changes.
This checkpoint's terminal gate evidence is recorded in the Reproduction
Manifest; earlier checkpoint PASS records are historical.

Verification (2026-09-21): both principal BAT scripts reached terminal
exit 0. The target reports LEAN VERIFICATION PASS: 340 package files,
351 integrity-scanned Lean files and 3,357 audited declarations
(3,352 discovered target theorems plus five imported contracts).
All 49 new named audits and all 61 new regressions pass.
The foundation reports PASS: all six stages passed, with 14,290
discovered theorems audited. Both final logs contain zero Lean errors,
warnings, tactic suggestions or linter failures. The counterexample
SHA256 is unchanged. Exact logs, source/runner hashes and repaired
focused diagnostics are recorded in the current Reproduction Manifest.
These gates verify the genuine moments and full-domain Add-est (i),
not clauses (ii)--(ix) or completion of the full goal.

## Add-est (ii): repaired powering to actual zero energy — verified checkpoint

Printed Lemma 62 remains disproved. Its singleton counterexample is
byte-preserved (SHA256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`).
The authorized replacement still uses independent cardinality-preserving
ρ/k and energy-preserving ρ*/k witnesses with independent existential fifth
coordinates. No false s'/s scaling or third witness is restored.

`add_est_ii`, `add_est_ii_bound`, and `add_est_ii_zero_energy` in
`NewAdditiveEnergy.lean` prove the complete second printed clause on
the closed interval 7/10 ≤ σ ≤ 3/4:

```text
A*(σ)(1−σ) ≤ max(5(18−19σ)/(2(5σ+3)), 2(45−44σ)/(2σ+15)).
```

The actual shifted-zero epsilon--delta bound is proved first, with analytic
multiplicity and unit-tolerance energy retained. The extended-real
infimum inequality follows from it. At σ=7/10 the rate is 47/26 and
A*≤235/39; at σ=3/4 the rate is 16/11 and A*≤64/11.
These endpoint checks supplement, not replace, the full interval proof.

For general patterns, `energyClauseTwo_general_bound` proves the rate on
2≤τ≤4. Actual mean-square and Guth--Maynard cardinality consumers use the
ρ/k witness at k and k+1. The actual Heath--Brown relation uses independent
energy witnesses at k and k−1, where k is two or three. All nine affine
branches are checked; the exceptional branches consume the first powered
energy inequality. Every height and coordinate is linked to its original
region point. Compactness promotes the region result to a uniform bound.

For zeta patterns, sixth-order decay is applied to the actual critical
Mellin integrand. Both the residue and the complete far tail
240 C₆ N^(11/2)/T⁴ are retained before absorption at T≥N^(11/8).
`zetaTwelfth_lower_short_largeValueBound` consumes the proved dyadic
twelfth moment and this entry bridge for σ≥7/10, τ≥7/5.
Actual cancellation gives eventual emptiness for 1≤τ<2σ on the clause
interval; mean-square powering and the twelfth-moment cap handle
2σ≤τ≤2 through nine exact branches with crossing τ=4σ−1.
`energyClauseTwo_short_zeta` therefore supplies all of [1,2].

`energyClauseTwo` composes the two uniform ranges with the already proved
endpoint-one bounded-range zero-energy transfer. The separate printed
endpoint-two transfer (EPZAE-33) is neither assumed nor marked complete.
Clause (i) remains proved. Clauses (iii)--(ix), the remaining optimization
projections, the source-form sharp Atkinson obligation, the other
EPZAE-19/21 inputs, and the exponent-pair/density/release outputs remain OPEN.
EPZAE-36/37 and the full EPZAE-00–41 objective are unchanged and incomplete.

Eleven new production modules are root-reachable and explicitly included
in the principal runner inventory. Eighty-four new public theorems have
named dependency audits; 92 added regressions cover all signatures and
literal physical/source endpoints. Keep `run_tao_trudgian_yang_build.bat`
and its backing inventory synchronized; run it and `run_lake_build.bat`
after relevant changes. Current gate evidence belongs in the Reproduction
Manifest; earlier PASS records are historical.

Verification (2026-09-21): both principal BATs reached terminal exit 0.
The target reports LEAN VERIFICATION PASS: 351 package files, 362
integrity-scanned Lean files and 3,504 audited declarations (3,499 discovered
target theorems plus five imported contracts). All 84 new named audits and
92 new regressions pass. The foundation reports PASS: all six stages passed
and all 14,290 discovered theorems were audited. Final logs contain zero
Lean errors, warnings, tactic suggestions or linter failures. The
counterexample and all 18 recorded source/runner hashes were rechecked.
Exact log paths and hashes appear in the current Reproduction Manifest.
These gates verify full-domain Add-est (ii), not the other seven clauses or
completion of the unchanged whole-proof goal.

## Jutila source entry and uniform powered moments — verified checkpoint

The printed Lemma 62 counterexample is preserved unchanged. Corrected
independent cardinality and energy witnesses remain the only powering
replacement. Full Add-est (i) and (ii) remain proved; (iii)--(ix) remain OPEN.

Four new production modules advance the missing EPZAE-19 Jutila input:
`JutilaGram`, `JutilaPatternEntry`, `JutilaPoweredMoments`, and
`JutilaReflectedEntry`. They do **not** yet prove Jutila's large-values
estimate or another Add-est clause.

`jutila_smooth_amplified_gram` proves actual phase-aligned smoothed duality,
removes the diagonal before Hölder, and gives, for every positive integer k,
either R V² ≤ 2N² or R² V^(4k) ≤ (2N)^(2k) times the actual off-diagonal
2k-th trace moment. No moment or cardinality bound is assumed.

`LargeValuePattern.jutila_gram_entry` consumes an actual source pattern.
Its fixed smoothed subfamily retains at least a third of the ordinates,
the exact threshold (V−1)/3, unit separation, the actual height, and
N/2 ≤ Q ≤ 2N. The spaced consumer keeps the explicit packing loss
6(2⌈δ⌉+1). `jutila_reflected_pattern_entry` then consumes complete native
reflection on that same subfamily, with one common dual cutoff M.
The main factor uses the actual |u−t|. Mellin truncation, omitted-frequency,
and zero-mode errors all remain in `jutilaReflectionEnvelope`.

`jutila_weighted_power_moment_uniform` proves the actual critical-line
2k-th ordered-difference moment bound. With U=2^k N^k and R=|W|, its RHS is
C (U^η)² T^ε (R² + R U + R^(5/4) T^(1/2)).
C and the height threshold depend only on k, ε, η, and are chosen before
N, T, W. The proof consumes the uniform divisor bound, actual powered
coefficients, dyadic decomposition, coefficient majorant, and the proved
native weighted Heath--Brown theorem. That second-moment theorem is an
input to this deduction, not a substitute for Jutila's large-values theorem.

Remaining: pass from complete reflected prefixes to uniformly bounded
powered difference moments, sum the reflected integrals with all errors,
and perform the local-to-global large-values optimization. Then establish
the actual region and uniform exponent consumers before using them in the
seven remaining energy optimizations. EPZAE-19, 33, 36, 37 and the full
EPZAE-00–41 goal remain open; the distinct endpoint-two transfer, source-form
sharp Atkinson obligation, and other exponent-pair/density/release tasks
are unchanged.

The four modules are included in the root and the exact production
inventory of `run_tao_trudgian_yang_build.bat`. Thirteen new public theorems
have named audits and sixteen regressions cover their exact signatures,
literal diagonal removal, the k=13 power, and all reflected error terms.
Keep that BAT and its backing inventory synchronized, and execute it and
`run_lake_build.bat` after relevant changes. Terminal verification evidence
for this checkpoint is recorded below and in the Reproduction Manifest.

Verification (2026-09-21): both principal BAT runners reached terminal exit 0.
The target reports LEAN VERIFICATION PASS: 355 package files, 366
integrity-scanned Lean files, and 3,530 audited declarations (3,525 discovered
target theorems plus five imported contracts). All 13 new named audits and
16 new regressions pass. The foundation reports PASS: all six stages passed
and all 14,290 discovered theorems were audited. Final logs contain zero
Lean errors, warnings, tactic suggestions, or linter failures. All eleven
recorded source/runner hashes were rechecked unchanged after the gates,
including the original counterexample. Repository scans found no forbidden
proof terms; the twelve raw postulate-pattern matches are the same ten
comments and two rational structure fields already reviewed. Git
`diff --check` passes (Git's LF/CRLF notices are not Lean diagnostics).
Exact commands, logs and hashes are in the Reproduction Manifest.
These gates verify the Jutila entry and powered-moment inputs, not the
remaining Jutila large-values theorem, other seven Add-est clauses, or
completion of the unchanged whole-proof goal.

## Jutila reflected-prefix moments and near/far assembly — verified history

The printed Lemma 62 counterexample is preserved unchanged. The corrected
independent cardinality and energy witnesses remain the only powering
replacement. Full Add-est (i) and (ii) remain proved; (iii)--(ix) remain OPEN.

Six new production modules advance EPZAE-19: `JutilaPolynomialMoments`,
`JutilaPrefixMoments`, `JutilaReflectionIntegrals`, `JutilaTraceBins`,
`JutilaBinnedPatterns`, and `JutilaHybridPatterns`.

`jutila_source_power_moment_uniform` handles arbitrary unit coefficients,
with constants chosen before their values and the physical length.
`jutila_reflected_prefix_moment_uniform` consumes the actual complete
reflected prefix, including n=1. With U=(2M)^k, R=|W|, and L=ceil(log₂ M),
its bound is C (L+1)^(2k) U (U^η)² T^ε
(R² + R U + R^(5/4) T^(1/2)). The constant is uniform in M, T, W and
the translation parameter. Neither the initial term nor a power of U is
discarded.

`jutila_reflected_bin_integral_moment_uniform` applies interval Jensen and
the proved full ordered-pair majorant before restricting to a difference
bin. Its extra interval factor is exactly (2H)^(2k).
`jutila_binned_pattern_bound` connects those estimates to the actual
source pattern, with bin-dependent positive dual lengths and all Mellin,
omitted-frequency, and zero-mode errors retained.

`jutila_hybrid_pattern_bound` additionally consumes native square-root
cancellation of the complete nonzero Poisson tail below the stationary
scale, keeping the separate zero-mode decay. Above that scale it uses the
actual ceiling length max(1,ceil(2^j H/Q)). The same subfamily retains
the packing loss 6(2 ceil(δ)+1), threshold (V−1)/3, N/2 ≤ Q ≤ 2N, the
actual height, and δ-separation. The condition 4H ≤ δ derives reflection
admissibility on occupied bins; it is not an independently assumed bin
estimate. The three new majorant definitions are notation, not proofs.

Remaining: bound this explicit near/far sum at source scale, absorb all
errors and logarithmic losses uniformly, perform the local-to-global
large-values optimization, and prove the exponent/energy-region consumers.
The target remains
LV(σ,τ) ≤ max(2−2σ, τ+4−2/k−(6−2/k)σ, τ+(6−8σ)k), k ≥ 1.
Only then can k=13 enter Add-est (iii) and the other remaining optimizations.
EPZAE-19, 33, 36, 37 and the full EPZAE-00–41 goal remain open. The distinct
endpoint-two transfer, sharp source-form Atkinson bridge, exponent-pair,
density, and release obligations are unchanged.

All six modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`. Seventeen new public theorems have
named audits; 23 regressions cover their exact signatures, the n=1 term at
k=13, zero interval width, the literal ceiling, and both schedule branches.
Both that BAT and `run_lake_build.bat` remain required evaluation gates.
This is finite-scale proof progress, not completion of Jutila or another
Add-est clause.

Verification (2026-09-21): both principal BAT runners reached terminal
exit 0. The target reports LEAN VERIFICATION PASS: 361 package files, 372
integrity-scanned Lean files, and 3,564 audited declarations (3,559 discovered
target theorems plus five imported contracts). All 17 new named audits and
23 regressions pass. The foundation reports PASS: all six stages passed,
with 14,290 discovered theorems audited. Final logs contain zero Lean
errors, warnings, tactic suggestions, or linter failures. All seventeen
recorded source/build hashes are unchanged after the gates, including the
original counterexample. Repository scans find no forbidden proof terms;
the twelve raw postulate-pattern matches are the previously reviewed ten
comments and two rational structure fields. Git `diff --check` passes.
Exact commands, logs, hashes, and the corrected initial scan failure are
recorded in the Reproduction Manifest. These checks certify the stated
finite-scale scope, not the remaining Jutila exponent, seven Add-est
clauses, or completion of the unchanged whole-proof goal.

## Jutila physical-scale smoothing and uniform pattern bounds — current checkpoint

The printed Lemma 62 counterexample remains byte-for-byte unchanged. The
authorized independent cardinality and energy witnesses remain the powering
replacement. Full Add-est (i) and (ii) remain proved; (iii)--(ix) remain OPEN.

Seven new production modules advance EPZAE-19: `JutilaDualScales`,
`JutilaPhysicalMain`, `JutilaPhysicalPatterns`, `JutilaSmoothingErrors`,
`JutilaSmoothingProfile`, `JutilaSmoothingLosses`, and
`JutilaSmoothedPatterns`.

`jutila_reflection_main_core_le` cancels each actual powered dual length
against its own displacement denominator before imposing the common cap.
`jutila_physical_pattern_bound` consumes the complete near/far pattern
theorem, retaining all main terms, logarithmic/divisor costs, and sharp
reflection errors. The common ceiling is used only for losses.

Native smoothing uses H=max(1,ceil(T^θ)) and derivative order
q=max(2,ceil(4/θ)+1). The zero mode and all three reflection errors are
controlled by proved native estimates, not assumed numerical certificates.
The smoothing-error bridge explicitly requires Q≤2T. The complete profile
is uniformly O(T^(2θ)); its full powered cost, including the bin count,
is O(T^((16k+3)θ)). The actual thinning cost is at most 108 T^θ.

`jutila_smoothed_pattern_bound` chooses positive B and T₀≥2 before every
actual `LargeValuePattern`. For scale≥30, V>1, T≥T₀, and **N≤T**, it
constructs a subset W of the reflected ordinates and Q with N/2≤Q≤2N.
Writing R=|W| and V'=(V−1)/3, the original count is at most B T^ν R,
W is 1-separated in the actual height interval, and either

- R (V')² ≤ 2Q²; or
- R² (V')^(4k) ≤ B T^ν (2Q)^(2k)
  (R²Q^k + R T^k + R^(5/4) T^(1/2) Q^k).

This holds for every k≥1 and ν>0. The choice of θ absorbs both losses
without changing the physical height or assuming the desired LV estimate.
The N≤T restriction derives Q≤2T and is not silently removed.

Remaining: solve the cardinality recurrence with its value threshold,
cover the complementary short-height range, perform the local-to-global
optimization, and prove the actual uniform LV and energy-region consumers.
The unchanged target is
LV(σ,τ) ≤ max(2−2σ, τ+4−2/k−(6−2/k)σ, τ+(6−8σ)k).
Only then can k=13 enter Add-est (iii) and the other seven-clause work.
EPZAE-19, 33, 36, 37 and the whole EPZAE-00–41 goal remain open. The
distinct endpoint-two transfer, sharp source-form Atkinson, exponent-pair,
density and release obligations are unchanged.

All seven modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`. Twenty-one new public theorems
have named audits. Twenty-seven regressions cover every exact signature
plus the actual k=13 source-pattern consumer, its three literal terms,
the empty-family boundary, ceiling padding, genuine zero-mode decay,
and the derived thinning cost. Both that BAT and `run_lake_build.bat`
remain mandatory; build integrity is separate from source completeness.
