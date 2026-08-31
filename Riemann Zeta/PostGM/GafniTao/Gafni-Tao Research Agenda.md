# Gafni-Tao research agenda

**Status:** active research and execution plan, not a proof claim.

**Suggested commit message:** `PostGM Gafni-Tao: prove endpoint-uniform sharp explicit formula`

Update the suggested commit message after every substantive proof milestone. Do not hard-code it inside `push_to_github.bat`.

---

# 1. Objective

Formalize the complete proof mechanism of Gafni-Tao Theorems 1.2 and 1.3 and the zero-density short-interval consequences of Theorem 1.1.

Then instantiate that mechanism with:

- the frozen Guth-Maynard zero-density theorem;
- the published Ford near-one zero-density input;
- the published Vinogradov-Korobov zero-free input;
- the exact published Pintz and Heath-Brown inputs needed for the paper's displayed Section 3 sample bounds.

The first principal public theorem should be the exact refined exceptional-set transfer.

The project quantifies the Lebesgue measure of exceptional short intervals.

It does not prove the Riemann Hypothesis.

---

# 2. Current proof state

The current imported and audited proof graph already contains most of the downstream Gafni-Tao transfer mechanism.

Use the following status vocabulary:

- `INTEGRATED`: represented by Lean declarations in the intended root dependency graph and present on the audit surface where appropriate.
- `CONDITIONAL`: downstream proof exists, but still accepts named source assumptions.
- `SOURCE OPEN`: the consumer bridge exists, but the published source theorem itself has not yet been proved natively.
- `PARTIAL`: substantial infrastructure exists but the exact acceptance contract is not yet closed.
- `OPEN`: intended theorem or consumer has not yet been constructed.
- `SYNC`: Lean has moved ahead of the project-control document.

---

# 3. Updated GT status ledger

| ID | Item | Current state | Acceptance remaining |
|---|---|---|---|
| GT-00 | Isolation and source freeze | INTEGRATED | Final release verification only |
| GT-01 | Exact paper-to-Lean crosswalk | SYNC | Crosswalk must be brought up to current Lean state |
| GT-02 | Asymptotic and exponent language | PARTIAL / heavily implemented | Finish any remaining exact converse interfaces required by final source theorem |
| GT-03 | Exact exceptional set | INTEGRATED | Final release verification |
| GT-04 | Multiplicity-weighted zero model | INTEGRATED | Final release verification |
| GT-05 | Zero additive energy `N*` and `A*` | INTEGRATED | Final release verification |
| GT-06 | Chebyshev/Mangoldt interval identity | INTEGRATED | Final release verification |
| GT-07 | Local cover and Brun-Titchmarsh localization | INTEGRATED | Documentation synchronization |
| GT-08 | Sharp truncated explicit formula | INTEGRATED / NATIVE | Remove redundant public hypothesis where possible |
| GT-09 | Vinogradov-Korobov zero-free region | SOURCE OPEN | Prove native source theorem |
| GT-10 | Near-one logarithmic zero density | SOURCE OPEN | Prove native Ford density theorem |
| GT-11 | Lemma 2.1 right-edge decay | CONDITIONAL | Discharge GT-09 and GT-10 |
| GT-12 | Lemma 2.2 `L-infinity` bound | INTEGRATED | Final source-statement comparison |
| GT-13 | Complex Fourier bump and coefficient decay | INTEGRATED | Final release verification |
| GT-14 | Lemma 2.3 second moment | INTEGRATED | Final release verification |
| GT-15 | Schur / energy bridge | INTEGRATED | Final release verification |
| GT-16 | Lemma 2.4 fourth moment | INTEGRATED | Final release verification |
| GT-17 | Finite strip assembly and equation (2.7) | INTEGRATED | Documentation synchronization |
| GT-18 | Limit and envelope assembly | INTEGRATED | Exact source theorem wrapper still required |
| GT-19 | Gafni-Tao Theorem 1.3 | CONDITIONAL | Remove source assumptions and export exact source statement |
| GT-20 | Theorems 1.2 and 1.1 | PARTIAL | Conditional 1.2 exists; exact 1.2 and 1.1 remain |
| GT-21 | Native ordinary-density GM consumer | INTEGRATED | Connect to final unconditional theorem once GT-19/20 close |
| GT-22 | Pintz and Heath-Brown exponent inputs | OPEN | Formalize pinned source segments |
| GT-23 | Published sample bounds | OPEN | Requires GT-19/20 and GT-22 |
| GT-24 | Certified Section 3 optimizer | OPEN | Requires source tables and exact finite-cell certification |
| GT-25 | Root imports, audit, release runner | ACTIVE | Final isolated build and actual axiom inspection required |
| GT-26 | Publication synchronization | SYNC | README updated; Architecture and Crosswalk still need current status |

---

# 4. Exact mathematical contract

For:

```text
0 < theta < 1
X > 1
delta > 0
```

model the exceptional set:

```text
E_delta(X,theta) = {
  x in [X,2X] :
  |sum_{x<n<=x+x^theta} Lambda(n) - x^theta|
    >= delta*x^theta
}.
```

Use Lebesgue measure, not a cardinality of sampled endpoints.

Define `mu_delta(theta)` as the infimum of exponents `xi` for which:

```text
|E_delta(X,theta)| <<_{delta,theta} X^xi
```

for all sufficiently large `X`.

Do not insert an epsilon loss into the definition of `mu_delta`.

Define:

```text
mu(theta) = sup_{delta>0} mu_delta(theta).
```

The extended-order construction must permit `-infinity` when the exceptional set is eventually empty.

Use `EReal` or an exactly equivalent extended-order formulation.

---

# 5. Zero-density contract

Let `N(sigma,T)` be the frozen analytic-multiplicity count for zeros satisfying:

```text
Re rho >= sigma
|Im rho| <= T.
```

Define `A(sigma)` in the source epsilon-loss sense.

Define:

```text
N*(sigma,T) =
  weighted number of ordered quadruples
  (rho1,rho2,rho3,rho4)
```

with:

```text
|gamma1 + gamma2 - gamma3 - gamma4| <= 1
```

and product analytic multiplicity.

Define `A*(sigma)` from this actual multiplicity-weighted count.

Do not replace `N*` with an unweighted energy of distinct ordinates.

---

# 6. Refined theorem contract

The exact refined source target retains the mandatory epsilon infimum.

Schematically:

```text
mu(theta)
  <= inf_{epsilon>0}
       sup_{
         0<=sigma<1,
         A(sigma)>=1/(1-theta)-epsilon
       }
       min(
         (1-theta)(1-sigma)A(sigma) + 2*sigma - 1,
         (1-theta)(1-sigma)A*(sigma) + 4*sigma - 3
       ).
```

The epsilon infimum is mandatory.

Do not delete it by silently assuming continuity of `A`.

The alternate:

```text
max(1-theta, ...)
```

form is useful but must remain a separately identified theorem unless exact equivalence to the paper's principal statement has been proved.

---

# 7. What is now implemented

## 7.1 Exceptional-set framework

The current project contains:

- `shortIntervalExceptionalSet`;
- Mangoldt short sums;
- exact discrepancy;
- measurability;
- finite measure;
- threshold antitonicity;
- `exceptionalExponentDelta`;
- `exceptionalExponent`;
- countable positive-threshold reduction;
- fixed-power and epsilon-exponent infrastructure.

This layer is no longer the active research bottleneck.

---

## 7.2 Zero multiplicity and additive energy

The project contains:

- analytic-multiplicity zero counts;
- occurrence counts;
- four-zero product multiplicities;
- actual `N*`;
- `A`;
- `A*`;
- ordinary and additive-energy envelopes;
- the density-to-energy comparison machinery used by the moment argument.

No distinct-zero surrogate is acceptable.

---

## 7.3 Local arithmetic entry

The project now contains:

- Mangoldt interval identities;
- prime-power tail control;
- local Brun-Titchmarsh estimates;
- replacement of `x^theta` by the local `x/tau` interval;
- local error ledgers;
- finite multiplicative covering.

GT-07 should no longer be treated as untouched.

---

## 7.4 Native sharp explicit formula

The sharp-Perron branch reaches:

```lean
GafniTao.sharpPsiTruncationBound_native
GafniTao.sharpTruncatedExplicitFormulaBound_native
```

with arbitrary real endpoints and the physical range required downstream.

GT-08 is complete at the current theorem level.

Remaining work is interface cleanup, not re-proving the sharp formula.

---

## 7.5 Fourier, second moment, and fourth moment

The current root and audit contain:

```lean
GafniTao.exists_complexifiedLogScaleBumpFourier_tenfold_decay
GafniTao.logarithmicZeroStripSecondMoment_eq_pair_sum
GafniTao.zeroStripPhysicalSecondMoment_epsilonBound
GafniTao.zeroPairPairDecaySum_le_zeroAdditiveEnergyCount
GafniTao.logarithmicZeroStripFourthMoment_eq_pair_sum
GafniTao.zeroStripPhysicalFourthMoment_epsilonBound
```

GT-13 through GT-16 are therefore implemented.

---

## 7.6 Equation (2.7)

The current project implements:

- half-open strip decomposition;
- upper-boundary accounting;
- no-zero-on-`Re=1` input;
- strip recombination;
- Markov bounds;
- small-density empty-event branch;
- right-edge branch;
- full zero-large-set measure bound.

Representative theorems include:

```lean
GafniTao.zerosInRect_eq_halfOpen_union_upperBoundary
GafniTao.sum_halfOpenStripIncrementSum_eq_full
GafniTao.equation27StripMeasure_epsilonBound_of_second_or_fourth
GafniTao.equation27StripMeasure_epsilonBound_of_exponent_upper_bounds
GafniTao.eventually_equation27StripLargeSet_eq_empty_of_rightEdge
GafniTao.equation27FullZeroMeasure_epsilonBound_of_nearOne_inputs
```

GT-17 is implemented at the downstream theorem level.

---

## 7.7 Limit and exceptional-cover assembly

The current project implements:

```lean
GafniTao.exists_refined_limit_witness
GafniTao.equation27FullZeroMeasure_fixedPowerBound_of_refined_lt
GafniTao.localExceptionalMeasure_fixedPowerBound_of_source_inputs
GafniTao.shortIntervalExceptionalSet_subset_local_union
GafniTao.exceptionalMeasure_fixedPowerBound_of_source_inputs
GafniTao.exceptionalExponentDelta_le_refined_max_of_source_inputs_all
```

GT-18 is therefore no longer merely planned.

---

## 7.8 Conditional theorem endpoints

Current endpoints include:

```lean
GafniTao.gafniTaoTheorem13_max_conditional
GafniTao.gafniTaoTheorem12_max_conditional
```

These are genuine downstream theorem assemblies.

They are not final unconditional source theorems.

Their remaining premises identify the current source frontier.

---

## 7.9 Frozen Guth-Maynard consumer

The current audit contains:

```lean
GafniTao.guthMaynard_zeroDensityEnvelope
GafniTao.zeroDensityExponent_le_guthMaynard
GafniTao.frozen_uniform_thirty_thirteenths_zeroDensityEnvelope
GafniTao.zeroDensityExponent_le_thirty_thirteenths
GafniTao.seventeen_thirtieths_eq_uniform_all_threshold
GafniTao.two_fifteenths_eq_uniform_almost_all_threshold
```

The ordinary `A0 = 30/13` bridge and the simple threshold arithmetic are therefore already present.

GT-21 should no longer be described as wholly open.

---

# 8. Active research front: Ford source closure

This is now the principal mathematical task.

`FordSource.lean` defines:

```lean
FordZetaGrowthBound
FordNearOneDensityEstimate
FordAsymptoticZeroFree
```

The consumer normalization is already implemented.

The project must now derive these source-facing propositions from the native Ford analytic machinery.

---

# 9. Native Ford infrastructure already present

The imported root currently contains a large Ford branch including:

```text
FordTrigonometric
FordFourierKernel
FordEulerProduct
FordLemma51
FordZetaBasic
FordZeroDetectorKernel
FordZeroDetectorResidues
FordCotangentPositivity
FordCotangentCorrection
FordZeroDetectorCenter
FordZeroDetectorZetaResidues
FordZeroDetectorDifferentiability
FordZeroDetectorRectangle
FordZeroDetectorFinite
FordZeroDetectorFiniteEdges
FordZeroDetectorHorizontalDecay
FordLogNormDerivative
FordZeroDetectorVerticalParts
FordZeroDetectorVerticalLog
FordZeroDetectorPhysicalEdges
FordLeftLine
FordLeftLineIntegral
FordKFiniteResidues
FordKFiniteRectangle
FordLaplaceInversion
FordLaplaceSource
FordKFiniteEdges
FordKHorizontal
FordKRightLine
FordKSourceSeries
FordKZeroSeries
FordKInfiniteRectangle
FordKLeftBound
FordKFormula
FordZeroDetectorEdges
FordZetaConvex
FordZetaBasicExplicit
FordLogDerivative
```

The audit surface includes native Ford theorems through the K-formula and detector-edge layers.

This is substantial source infrastructure.

It is not yet equivalent to proving the final Ford source outputs.

---

# 10. Ford acceptance sequence

## 10.1 Integrate only intended source modules

Files that merely exist do not count.

For each Ford module that is part of the proof path:

1. import it from the intended root;
2. ensure it builds with the isolated package;
3. put source-sensitive endpoints on `Audit.lean`;
4. remove probes and temporary scaffolding from the claimed dependency path.

Do not count experimental source files toward completion until they are actually integrated.

---

## 10.2 Close the Ford zeta-growth source theorem

The source-facing proposition:

```lean
FordZetaGrowthBound
```

must eventually have a native proof or a theorem from an explicitly accepted pinned dependency.

A suitable native endpoint may be named along the lines of:

```lean
fordZetaGrowthBound_native
```

The exact theorem name is secondary.

The proof dependency is what matters.

---

## 10.3 Close the Ford / Vinogradov-Korobov zero-free output

Produce a native proof of:

```lean
FordAsymptoticZeroFree
```

or an equivalent theorem strong enough to instantiate it without introducing another project-level assumption.

Then use the already proved path:

```text
FordAsymptoticZeroFree
        |
        v
VinogradovKorobovPointwiseZeroFree
        |
        v
VinogradovKorobovRectangleZeroFree
        |
        v
VinogradovKorobovCountVanishing
```

Do not accept `VinogradovKorobovCountVanishing` directly as a new unrelated assumption.

---

## 10.4 Close the near-one density theorem

Produce explicit witnesses `K` and `T0` with:

```lean
FordNearOneDensityEstimate K T0
```

from the intended Ford / Halasz-Turan / Montgomery source chain.

Preserve the logarithmic factor.

Do not replace it with a generic `T^epsilon` loss.

The already implemented normalization will then yield:

```lean
NearOneLogDensityBound 58.05 16 ...
```

---

## 10.5 Package native near-one inputs

Once both source outputs are proved, construct a theorem structurally equivalent to:

```text
exists c T1 T2,
  0 < c
  and VinogradovKorobovCountVanishing c T1
  and NearOneLogDensityBound 58.05 16 T2.
```

At that point the right-edge branch should cease to be conditional on external project assumptions.

---

# 11. Remove already-resolved assumptions from final assembly

The current conditional theorem interface still accepts:

```lean
hFormula : SharpTruncatedExplicitFormulaBound
```

even though:

```lean
GafniTao.sharpTruncatedExplicitFormulaBound_native
```

already exists.

Create a cleaner wrapper that supplies the native explicit formula internally.

Likewise, if the required smooth cutoff can be constructed from the frozen foundation without a new analytic assumption, provide it internally or through a clearly named existence theorem.

The top-level Gafni-Tao theorem should expose only genuinely unresolved premises.

---

# 12. Export exact Theorem 1.3

After source closure, prove the paper's exact refined statement.

Required properties:

1. actual `A`;
2. actual `A*`;
3. mandatory epsilon infimum;
4. empty-supremum behavior preserved in `EReal`;
5. no continuity assumption;
6. no unnecessary `max(1-theta, ...)` inserted into the principal source theorem;
7. all source inputs discharged by native or accepted pinned theorems.

The existing:

```lean
gafniTaoTheorem13_max_conditional
```

should remain available as a useful corollary or intermediate theorem.

It should not be silently renamed into the final source theorem.

---

# 13. Export exact Theorem 1.2

After Theorem 1.3 closes:

1. discard the fourth-moment improvement exactly;
2. retain the source epsilon-infimum structure;
3. prove the exact ordinary theorem;
4. separately retain the max-form corollary.

Current infrastructure already contains:

```lean
ordinaryFixedEpsilonExponent
ordinaryExceptionalUpperExponent
refinedFixedEpsilonExponent_le_ordinary
refinedExceptionalUpperExponent_le_ordinary
gafniTaoTheorem12_max_conditional
```

The missing work is final source-theorem closure.

---

# 14. Prove Theorem 1.1

For a uniform density bound:

```text
A(sigma) <= A0
```

derive the source's two threshold statements:

```text
all intervals:
theta > 1 - 1/A0
```

and:

```text
almost all intervals:
theta > 1 - 2/A0.
```

The meaning of "almost all" must be connected to:

```text
mu(theta) < 1
```

using the actual exceptional-set measure framework.

The frozen GM `A0 = 30/13` envelope and elementary threshold arithmetic already exist and should be consumed here rather than re-created.

---

# 15. Section 3 published inputs

After the general theorem is unconditional, formalize the exact external segments needed for the displayed numerical consequences.

## 15.1 Pintz ordinary density segment

Formalize the exact segment used for the paper's:

```text
sigma <= 23/24
```

cutoff.

Verify:

- original source convention;
- `T` convention;
- multiplicity;
- exponent normalization;
- endpoints.

---

## 15.2 Heath-Brown four-zero energy segment

Formalize the exact `A*` input needed near:

```text
sigma = 7/10.
```

The source normalization must agree with the project's multiplicity-weighted `N*`.

Do not insert a separately defined surrogate energy.

---

# 16. First published numerical sample

Prove exactly:

```text
mu(17/30) <= 7/12.
```

This proof should consume:

- the completed refined Gafni-Tao theorem;
- the frozen GM ordinary-density input where required;
- the pinned Heath-Brown `A*` input;
- exact rational arithmetic;
- all limiting margins.

No floating-point calculation should be part of the proof term.

---

# 17. Second published numerical sample

Prove the quantified statement corresponding to:

```text
for sufficiently small Delta > 0
```

with:

```text
mu(2/15 + Delta) <= 1 - 9*Delta/13.
```

The theorem must contain an explicit sufficiently-small quantifier.

It must consume the actual Pintz cutoff rather than a hand-inserted numerical restriction.

---

# 18. Optional full Section 3 optimizer

If the full Figure 4 envelope is claimed:

1. pin the exact ANTEDB / Tao-Trudgian-Yang source snapshot;
2. record hashes;
3. translate every relevant piecewise segment;
4. prove endpoint compatibility;
5. reduce the optimization to finitely many exact cells;
6. certify every relevant cell in Lean;
7. use rational or algebraic endpoints wherever possible.

A floating-point plot may accompany the formal result.

It may not establish it.

---

# 19. Audit discipline

The isolated audit file is:

```text
Extension/GafniTao/Audit.lean
```

Every public or source-sensitive theorem must be considered for explicit `#print axioms` inclusion.

At release time run:

```bash
lake build
lake env lean GafniTao/Audit.lean
```

and inspect the output.

Also run:

```bash
rg -n '\bsorry\b|\badmit\b|\bnative_decide\b|^\s*(axiom|opaque|unsafe)\b' --glob '*.lean' .
```

A theorem compiling is not enough.

A theorem appearing in `Audit.lean` is not enough.

The actual dependency output must be inspected.

---

# 20. Root-import discipline

`Extension/GafniTao.lean` defines the intended integrated package surface.

Temporary probe files, abandoned experiments, and unimported source files must not be counted as completed proof work.

A proof milestone is integrated only when:

1. its intended module is imported;
2. the package builds;
3. the endpoint is reachable from the root;
4. the source-sensitive endpoint is audited;
5. the result is used by the intended downstream theorem or is clearly marked as infrastructure.

---

# 21. Documentation synchronization

The Lean development has moved ahead of the older project-control status tables.

The following must be synchronized after the current Ford milestone:

```text
README.md
Gafni-Tao Research Agenda.md
Gafni-Tao Architecture.md
Gafni-Tao Crosswalk.md
Gafni-Tao Shitlist.md
```

In particular:

- GT-07 is no longer wholly open;
- GT-17 is no longer wholly open;
- GT-18 is no longer wholly open;
- conditional Theorems 1.2 and 1.3 exist;
- the frozen GM `30/13` bridge and threshold arithmetic exist;
- the Ford source branch is now much larger than the old planning documents indicate.

Documentation status must never override actual Lean dependencies.

---

# 22. Current execution order

The current order should be:

```text
1. Ford source integration and cleanup
2. Native Ford zero-free closure
3. Native Ford near-one density closure
4. Package unconditional near-one inputs
5. Remove redundant sharp-formula premise
6. Close exact Theorem 1.3
7. Close exact Theorem 1.2
8. Prove Theorem 1.1
9. Formalize Pintz input
10. Formalize Heath-Brown A* input
11. Prove the two displayed sample bounds
12. Optional full Section 3 optimizer
13. Final isolated audit
14. Synchronize all public documentation
```

Do not divert major effort back into already-implemented Section 2 infrastructure unless a genuine defect is found.

---

# 23. Stop conditions

Do not mark the full project complete while any of the following remains true:

- `FordNearOneDensityEstimate` is only an assumed proposition;
- `FordAsymptoticZeroFree` is only an assumed proposition;
- the final theorem still exposes avoidable already-proved analytic premises;
- the exact source Theorem 1.3 has not been exported;
- the exact source Theorem 1.2 has not been exported;
- Theorem 1.1 has not been exported;
- claimed Section 3 results rely on unformalized Pintz or Heath-Brown inputs;
- `Audit.lean` has not been executed and inspected;
- project-level `sorry`, `admit`, unsafe shortcuts, or disguised target axioms remain;
- public documentation materially disagrees with the actual root and audit surfaces.

---

# 24. Success condition

The general Gafni-Tao phase succeeds when Lean can derive the exact source theorem through a dependency path of the form:

```text
frozen Guth-Maynard foundation
             |
             +----------------------------+
             |                            |
             v                            v
native sharp explicit formula     native Ford/VK inputs
             |                            |
             +--------------+-------------+
                            |
                            v
                  local arithmetic entry
                            |
                            v
                 finite zero-strip sums
                            |
               +------------+------------+
               |            |            |
               v            v            v
           L-infinity      L2            L4
               |            |            |
               +------------+------------+
                            |
                            v
                     equation (2.7)
                            |
                            v
                  finite-strip limiting
                            |
                            v
                 local exceptional bound
                            |
                            v
                  multiplicative cover
                            |
                            v
                       mu_delta
                            |
                            v
                          mu
                            |
                            v
               exact Gafni-Tao Theorem 1.3
```

with every source-sensitive dependency accounted for.

The numerical-consumer phase succeeds only after the required Pintz and Heath-Brown source inputs and the paper's displayed sample bounds are also kernel-checked.

---

# 25. Repository workflow

`push_to_github.bat` is the owner-operated publication step.

It is not proof verification.

The public repository is the latest deliberately pushed snapshot and may lag local work.

Agents must not push unless separately instructed.

After the next substantive Ford milestone, use a commit message appropriate to the actual result.

Examples:

```bat
push_to_github.bat "PostGM Gafni-Tao: close Ford asymptotic zero-free input"
```

or:

```bat
push_to_github.bat "PostGM Gafni-Tao: close Ford near-one density input"
```

Do not use those messages before the corresponding source theorem is genuinely proved.

---

# 26. Immediate task

Continue the Ford source branch.

The next meaningful milestone is not another downstream wrapper.

It is a native theorem that removes one of the two remaining Ford source assumptions:

```lean
FordAsymptoticZeroFree
```

or:

```lean
FordNearOneDensityEstimate K T0
```

for explicit witnesses `K` and `T0`.

Whichever closes first should immediately be:

1. imported through the intended root;
2. added to the audit surface;
3. wired into the existing consumer bridge;
4. reflected in the Crosswalk and Architecture;
5. given a truthful milestone commit message.

That is now the shortest path toward turning the existing conditional Gafni-Tao theorem machine into an unconditional formalization of the published theorem.