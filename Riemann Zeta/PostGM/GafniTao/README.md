# Gafni-Tao exceptional intervals

## Status

**Active isolated formalization.**

The project has progressed well beyond foundational scaffolding.

The main Section 2 zero-density-to-exceptional-set transfer mechanism is now implemented in Lean, including:

- the exact Mangoldt short-interval exceptional set;
- Lebesgue-measure exceptional exponents;
- multiplicity-weighted zero counting;
- the four-zero additive-energy quantity `N*` and exponent `A*`;
- the local multiplicative cover;
- Brun-Titchmarsh localization and replacement estimates;
- a native sharp truncated explicit formula;
- finite zero strips;
- the physical `L-infinity`, `L2`, and `L4` zero-sum estimates;
- Markov conversion;
- the equation (2.7) strip decomposition;
- the right-edge, small-density, second-moment, and fourth-moment branches;
- epsilon and finite-strip limiting machinery;
- local-to-global exceptional-measure assembly;
- conditional assembled forms of Gafni-Tao Theorems 1.2 and 1.3;
- the frozen Guth-Maynard `30/13` ordinary-density envelope and associated threshold arithmetic.

The active mathematical frontier is now much narrower.

The principal unresolved work is to derive the published Ford near-one zero-density and Vinogradov-Korobov zero-free inputs from the growing native Ford source development, then remove those assumptions from the final Gafni-Tao theorem interface.

The complete Gafni-Tao formalization is **not yet claimed**.

---

## Purpose

This directory is the isolated post-Guth-Maynard program for formalizing Ayla Gafni and Terence Tao's paper:

*On the number of exceptional intervals to the prime number theorem in short intervals*

arXiv:2505.24017v1.

The target is the paper's actual zero-density-to-exceptional-set argument, including the fourth-moment refinement and its published numerical consequences.

The intended endpoint is not merely a theorem with the same numerical shape. The objective is to formalize the mathematical dependency chain used by the paper closely enough that the final public theorem can be audited directly against the source argument.

This work does not prove the Riemann Hypothesis, and nothing in this directory should be described as doing so.

---

# Current mathematical state

The implemented downstream architecture is approximately:

```math
\mathrm{zeta\ zeros}
\longrightarrow
N(\sigma,T),\,N^{\ast}(\sigma,T)
\longrightarrow
A(\sigma),\,A^{\ast}(\sigma)
```

```math
\longrightarrow
L^{\infty},\,L^{2},\,L^{4}
\ \mathrm{zero\text{-}sum\ bounds}
```

```math
\longrightarrow
\mathrm{equation\ (2.7)\ strip\ alternatives}
```

```math
\longrightarrow
\mathrm{local\ exceptional\text{-}measure\ bounds}
```

```math
\longrightarrow
\mathrm{finite\text{-}strip\ and\ }\varepsilon\mathrm{\ limits}
```

```math
\longrightarrow
\mathrm{meas}\,E_{\delta}(X,\theta)
\ll
X^{\xi}
```

```math
\longrightarrow
\mu_{\delta}(\theta)
\longrightarrow
\mu(\theta)
```

Most of this transfer machinery is now represented by Lean theorems on the isolated audit surface.

The remaining conditionality is concentrated primarily in the near-one analytic source inputs.

---

# Current status by proof layer

| Proof layer | Current state |
|---|---|
| Exact exceptional set | Implemented |
| `mu_delta` / `mu` framework | Implemented through the current downstream consumer interfaces |
| Multiplicity-weighted `N` | Implemented |
| Multiplicity-weighted `N*` | Implemented |
| `A` / `A*` exponent machinery | Implemented through the current consumer interfaces |
| Chebyshev/Mangoldt interval identities | Implemented |
| Local multiplicative cover | Implemented |
| Brun-Titchmarsh replacement | Implemented |
| Sharp truncated explicit formula | Native theorem implemented |
| Complex Fourier bump | Implemented |
| Second moment | Implemented |
| Fourth moment | Implemented |
| Finite half-open strip assembly | Implemented |
| Equation (2.7) | Implemented |
| Right-edge consumer | Implemented conditional on near-one source inputs |
| Limit assembly | Implemented |
| Global exceptional cover | Implemented |
| Refined Theorem 1.3 max-form | Implemented conditionally |
| Ordinary Theorem 1.2 max-form | Implemented conditionally |
| Frozen GM `30/13` consumer | Implemented |
| Ford source theorem closure | Active |
| Vinogradov-Korobov source theorem closure | Active |
| Exact unconditional Theorem 1.3 | Open |
| Exact unconditional Theorem 1.2 | Open |
| Theorem 1.1 | Open |
| Pintz / Heath-Brown Section 3 inputs | Open |
| Published sample bounds | Open |
| Certified Section 3 optimizer | Open |
| Final release audit | Open |

---

# Implemented theorem spine

## 1. Exceptional sets

The formalization defines the actual Mangoldt short-interval exceptional set rather than a sampled or finite proxy.

The mathematical object is:

```math
E_{\delta}(X,\theta)
=
\left\{
x\in[X,2X]:
\left|
\psi\!\left(x+x^{\theta}\right)-\psi(x)-x^{\theta}
\right|
\ge
\delta x^{\theta}
\right\}
```

The project then defines the corresponding fixed-threshold exceptional exponent:

```math
\mu_{\delta}(\theta)
```

and the global exceptional exponent:

```math
\mu(\theta)
```

The implementation includes measurability, finite-measure facts, threshold monotonicity, fixed-power bounds, and countable positive-threshold reduction.

---

## 2. Zero counting and multiplicity

The project contains native infrastructure for the nontrivial zeros of the Riemann zeta function and the multiplicity-weighted zero counts required by the paper.

This includes:

```math
N(\sigma,T)
```

and the four-zero additive-energy quantity:

```math
N^{\ast}(\sigma,T)
```

The four-zero object uses ordered zero occurrences with analytic multiplicity.

It is not replaced by the additive energy of a set of distinct ordinates.

The associated exponent interfaces `A` and `A*` feed the ordinary and refined moment arguments.

---

## 3. Local arithmetic entry

The local entry into the Gafni-Tao argument now includes:

- the Mangoldt interval identity;
- decomposition of prime and prime-power contributions;
- local Brun-Titchmarsh control;
- replacement of the variable interval length by the local `x/tau` scale;
- explicit error ledgers;
- the finite multiplicative cover of `[X,2X]`.

The local cover and replacement machinery now connects directly to the later equation (2.7) exceptional event.

---

## 4. Native sharp truncated explicit formula

The sharp explicit-formula branch has a native endpoint:

```lean
GafniTao.sharpTruncatedExplicitFormulaBound_native
```

The supporting sharp-Perron development includes:

- finite Mangoldt Perron identities;
- logarithmic derivative expansions;
- scalar Perron kernels;
- contour decomposition;
- residue assembly;
- zero shells with analytic multiplicity;
- right, left, upper, and lower contour estimates;
- selected good heights;
- low-height handling;
- arbitrary real endpoints;
- transition terms near integral cutoffs;
- the full physical range required downstream.

The target range includes:

```math
2 \le T \le x
```

The sharp explicit formula is therefore no longer part of the main unresolved analytic frontier.

One remaining cleanup item is to stop exposing an explicit-formula hypothesis in final public Gafni-Tao wrappers when the native theorem can be supplied internally.

---

## 5. Second and fourth moments

The second- and fourth-moment branches are implemented at the intended multiplicity-sensitive level.

The second moment uses the actual zero count.

The fourth moment uses the actual tolerance-one four-zero additive-energy count and therefore genuinely retains the `A*` improvement.

The audit surface includes the physical moment bounds and the exact epsilon-exponent versions consumed by the strip argument.

---

## 6. Equation (2.7)

The half-open strip decomposition is implemented.

The relevant development includes:

- exact strip indexing;
- treatment of upper strip boundaries;
- exclusion of zeros on the line `Re rho = 1`;
- full-zero-sum reconstruction from half-open strips;
- large-set covering by strip large sets;
- the small-`A` eventually-empty branch;
- second-moment Markov bounds;
- fourth-moment Markov bounds;
- right-edge bounds;
- assembly of the complete equation (2.7) exceptional measure.

Representative audit entries include:

```lean
GafniTao.zerosInRect_eq_halfOpen_union_upperBoundary
GafniTao.sum_halfOpenStripIncrementSum_eq_full
GafniTao.equation27StripMeasure_second_epsilonBound
GafniTao.equation27StripMeasure_fourth_epsilonBound
GafniTao.eventually_equation27StripLargeSet_eq_empty_of_rightEdge
GafniTao.equation27FullZeroMeasure_epsilonBound_of_nearOne_inputs
```

Equation (2.7) should therefore no longer be described as merely planned.

---

## 7. Limit and local-to-global assembly

The project now contains the limiting machinery needed to move from finite strips and epsilon-dependent estimates to fixed-power exceptional-measure bounds.

Representative theorems include:

```lean
GafniTao.exists_refined_limit_witness
GafniTao.equation27FullZeroMeasure_fixedPowerBound_of_refined_lt
GafniTao.localExceptionalMeasure_fixedPowerBound_of_source_inputs
GafniTao.exceptionalMeasure_fixedPowerBound_of_source_inputs
```

The local result is then promoted through the finite multiplicative cover to the original exceptional set on `[X,2X]`.

This means the downstream Section 2 transfer mechanism now reaches the actual exceptional exponent.

---

# Conditional Gafni-Tao endpoints

## Refined theorem

The current assembled refined endpoint is:

```lean
GafniTao.gafniTaoTheorem13_max_conditional
```

It proves a bound of the form:

```math
\mu(\theta)
\le
\max
\left\{
1-\theta,\,
\mathcal{R}(\theta)
\right\}
```

where the refined term retains both `A` and `A*`.

The theorem currently accepts:

- a Guth-Maynard smooth cutoff object;
- a sharp explicit-formula hypothesis;
- a near-one logarithmic density bound;
- a Vinogradov-Korobov count-vanishing input.

The downstream exceptional-set deduction is therefore assembled, but the theorem is still conditional.

The exact source formulation of Theorem 1.3 remains to be exported without unnecessary already-proved premises and with the source epsilon-infimum statement matched exactly.

---

## Ordinary theorem

The current ordinary endpoint is:

```lean
GafniTao.gafniTaoTheorem12_max_conditional
```

It follows from the refined theorem by discarding the fourth-moment improvement.

Schematically:

```math
\mu(\theta)
\le
\max
\left\{
1-\theta,\,
\mathcal{O}(\theta)
\right\}
```

The ordinary epsilon-infimum expression itself is represented in Lean by:

```lean
GafniTao.ordinaryExceptionalUpperExponent
```

The exact unconditional source theorem and Theorem 1.1 remain open.

---

# Frozen Guth-Maynard consumer

The frozen Guth-Maynard density theorem is now connected to the Gafni-Tao exponent language.

The audit surface includes:

```lean
GafniTao.guthMaynard_zeroDensityEnvelope
GafniTao.zeroDensityExponent_le_guthMaynard
GafniTao.frozen_uniform_thirty_thirteenths_zeroDensityEnvelope
GafniTao.zeroDensityExponent_le_thirty_thirteenths
GafniTao.seventeen_thirtieths_eq_uniform_all_threshold
GafniTao.two_fifteenths_eq_uniform_almost_all_threshold
```

Thus the ordinary `A0 = 30/13` bridge and the corresponding threshold arithmetic are no longer merely future tasks.

The later Section 3 numerical conclusions still require their additional published inputs.

---

# Active analytic frontier

## Ford source closure

`FordSource.lean` currently records three source-facing propositions:

```lean
GafniTao.FordZetaGrowthBound
GafniTao.FordNearOneDensityEstimate
GafniTao.FordAsymptoticZeroFree
```

It already proves the normalization bridge:

```lean
GafniTao.nearOneLogDensityBound_of_fordNearOneDensityEstimate
```

which converts the coefficient-bearing estimate into the exact downstream logarithmic-density input:

```math
N(1-\eta,T)
\le
T^{58.05\,\eta^{3/2}}
(\log T)^{16}
```

without spending a `T^epsilon` loss.

It also proves:

```lean
GafniTao.exists_nearOne_inputs_of_ford_outputs
```

which packages genuine Ford zero-free and density outputs into the pair consumed by the Gafni-Tao right-edge argument.

The missing step is therefore no longer the downstream normalization.

The missing step is to prove the Ford source propositions themselves.

---

## Native Ford development now present

The imported Ford development has grown into a substantial analytic branch.

The isolated root currently imports modules covering, among other things:

- Ford trigonometric positivity;
- Fourier kernels;
- Euler-product and prime-power expansions;
- Ford Lemma 5.1;
- basic explicit zeta bounds;
- logarithmic-derivative estimates;
- cotangent detector kernels;
- cotangent corrections;
- zero-detector residues;
- finite detector rectangles;
- detector edge identities;
- left-line estimates;
- Laplace inversion;
- K-function finite rectangles;
- K-function zero series;
- infinite-rectangle limits;
- left-line bounds;
- native K-formula assembly.

The audit surface includes native results such as:

```lean
GafniTao.ford_lemma_5_1
GafniTao.ford_zeta_basic_upper
GafniTao.ford_zeta_basic_logDerivative
GafniTao.fordK_infinite_rectangle_native
GafniTao.fordK_formula_native
GafniTao.fordK_formula_with_log_error_native
GafniTao.fordZetaDetector_rectangleIntegral_eq_residue_sum
GafniTao.fordZetaDetector_rightEdge_eq_explicit_add_edges
```

This is now the active source-theorem construction program.

The existence of supporting lemmas is not itself a proof of `FordNearOneDensityEstimate` or `FordAsymptoticZeroFree`.

Those source statements remain the acceptance boundary.

---

## Vinogradov-Korobov consumer bridge

The source-facing Vinogradov-Korobov layer is already structured correctly.

The project defines a pointwise zero-free region, proves the required denominator monotonicity, upgrades the pointwise statement to a rectangle-uniform statement, and converts that into the multiplicity-weighted zero-count vanishing used downstream.

The dependency shape is:

```text
pointwise Vinogradov-Korobov theorem
                |
                v
rectangle-uniform zero-free region
                |
                v
VinogradovKorobovCountVanishing
                |
                v
Gafni-Tao right-edge argument
```

What remains is the native proof of the actual source theorem feeding the first node.

---

# Section 3 and numerical consequences

The later published numerical consequences are not yet complete.

The first principal target is:

```math
\mu\!\left(\frac{17}{30}\right)
\le
\frac{7}{12}
```

The second is the quantified sufficiently-small-Delta result corresponding to the paper's second displayed sample bound.

These require additional published analytic inputs, including the relevant:

- Pintz ordinary zero-density segment;
- Heath-Brown four-zero additive-energy segment;
- endpoint and normalization compatibility;
- exact limiting arithmetic.

The full Figure 4 envelope, if pursued, also requires a certified finite optimizer over the pinned source tables.

Floating-point numerical plots may be used for checking but not as the proof of the final Lean theorem.

---

# Audit surface

The isolated package contains:

```text
Extension/GafniTao/Audit.lean
```

`Audit.lean` explicitly lists source-sensitive and public theorem dependencies using `#print axioms`.

The audit surface now includes:

- exceptional-set definitions;
- `EReal` exponent machinery;
- multiplicity bridges;
- Ford source infrastructure;
- Vinogradov-Korobov consumer bridges;
- right-edge decay machinery;
- local cover and Brun-Titchmarsh localization;
- second and fourth moments;
- finite half-open strips;
- equation (2.7);
- refined limiting assembly;
- local-to-global exceptional cover;
- conditional Theorems 1.2 and 1.3;
- the complete native sharp-Perron branch;
- the frozen GM consumer.

A declaration appearing in `Audit.lean` means it has been placed on the explicit dependency-audit surface.

It does **not** by itself prove that the complete isolated release audit has been freshly executed and inspected.

---

# Verification

Run from:

```text
Riemann Zeta/PostGM/GafniTao/Extension
```

The package is intentionally separate from the frozen Guth-Maynard source tree.

A release-quality verification should include:

```bash
lake build
lake env lean GafniTao/Audit.lean
```

and a scan for unfinished or unsafe declarations:

```bash
rg -n '\bsorry\b|\badmit\b|\bnative_decide\b|^\s*(axiom|opaque|unsafe)\b' --glob '*.lean' .
```

The actual `#print axioms` output must be inspected.

Compilation alone is not sufficient evidence that the intended dependency boundary has been respected.

Files that merely exist in the working tree do not count as integrated proof infrastructure unless they are brought into the intended root dependency graph and, where source-sensitive, onto the audit surface.

---

# Isolation boundary

This project is intentionally isolated from the completed Guth-Maynard foundation.

- Frozen foundation commit:

```text
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be
```

- Frozen foundation tag:

```text
gm-foundation-freeze-v1.0.1
```

- Lean version:

```text
v4.30.0
```

The isolated extension also pins its external analytic dependencies in `lakefile.toml`.

All Gafni-Tao Lean development belongs below:

```text
PostGM/GafniTao/Extension/
```

Do not modify the frozen `RiemannZeta/` foundation merely to make the Gafni-Tao extension easier to prove.

Do not weaken frozen public contracts.

Do not import this experimental extension back into:

```text
RiemannZeta.lean
```

The dependency direction is one-way:

```text
Frozen Guth-Maynard foundation
              |
              v
      Gafni-Tao extension
```

not the reverse.

---

# Acceptance standard

A source theorem is not DONE merely because a downstream implication has been formalized.

For a source result to be accepted, establish all applicable items below:

1. The statement matches the pinned source theorem and parameter range.
2. Analytic multiplicities are represented correctly.
3. Endpoint conventions match the source.
4. Constants and logarithmic factors are accounted for.
5. No prohibited `T^epsilon` loss is inserted into the near-one density estimate.
6. No project-level `axiom`, `sorry`, `admit`, unsafe shortcut, or disguised restatement supplies the intended result.
7. The theorem is integrated into the intended root import graph.
8. The theorem appears on the audit surface where appropriate.
9. The isolated package builds.
10. The actual axiom output is inspected.
11. The Crosswalk, Architecture, Research Agenda, and README agree with the Lean source.
12. Public theorem names do not claim more than their hypotheses justify.

---

# Claim discipline

The strongest safe summary of the repository at present is:

> A substantial part of the Gafni-Tao exceptional-interval argument has been formalized in Lean. The exact exceptional-set framework, multiplicity-sensitive zero counts, local arithmetic entry, native sharp truncated explicit formula, second- and fourth-moment machinery, equation (2.7), limiting assembly, local-to-global covering argument, frozen Guth-Maynard consumer, and conditional max-forms of Theorems 1.2 and 1.3 are implemented. A large native Ford source-development branch is also present. The complete Gafni-Tao theorem is not yet claimed because the Ford near-one zero-density and Vinogradov-Korobov source outputs have not yet been discharged, the exact unconditional theorem interfaces remain open, and the later Section 3 published inputs and sample bounds remain unfinished.

Do not shorten this to:

```text
Gafni-Tao is proved in Lean.
```

That statement is not currently justified.

Likewise, do not describe:

```lean
GafniTao.gafniTaoTheorem13_max_conditional
GafniTao.gafniTaoTheorem12_max_conditional
```

as unconditional final source theorems.

---

# Documents

The directory contains the project-control documents used to keep the formalization synchronized with the source.

- [Gafni-Tao Sources.md](Gafni-Tao%20Sources.md)

  Source references, hashes, external inputs, and reusable Lean infrastructure.

- [Gafni-Tao Architecture.md](Gafni-Tao%20Architecture.md)

  Numbered dependency graph and module architecture.

- [Gafni-Tao Research Agenda.md](Gafni-Tao%20Research%20Agenda.md)

  Current execution plan and acceptance order.

- [Gafni-Tao Crosswalk.md](Gafni-Tao%20Crosswalk.md)

  Source-to-Lean theorem mapping.

- [Gafni-Tao Shitlist.md](Gafni-Tao%20Shitlist.md)

  Detailed acceptance checklist.

- [Gafni-Tao Goal Prompt.md](Gafni-Tao%20Goal%20Prompt.md)

  Persistent implementation objective for coding agents.

These documents are project-control artifacts, not proof objects.

When documentation and Lean disagree about implementation status, inspect the Lean source and audit surface, then update the documentation.

---

# Near-term execution order

## 1. Close the Ford source statements

Convert the existing Ford analytic development into native proofs of the source-facing propositions required by `FordSource.lean`.

The desired endpoint is structurally:

```text
native Ford analytic machinery
              |
              +--------------------+
              |                    |
              v                    v
FordNearOneDensityEstimate   FordAsymptoticZeroFree
              |                    |
              +---------+----------+
                        |
                        v
             exact near-one inputs
```

## 2. Remove resolved premises from top-level consumers

Use the native sharp explicit formula internally.

Construct or supply the required cutoff internally where the frozen foundation already provides the necessary object.

The public Gafni-Tao wrapper should expose only genuinely unresolved source assumptions.

## 3. Export the exact source Theorem 1.3

Prove the exact refined epsilon-infimum statement required by the paper.

Keep the alternate `max(1-theta, ...)` theorem as a separate corollary.

## 4. Export exact Theorem 1.2 and Theorem 1.1

Derive the ordinary second-moment theorem and then the all-interval / almost-all interval consequences.

## 5. Complete Section 3

Formalize the Pintz and Heath-Brown source segments and prove the paper's displayed sample bounds.

## 6. Complete final audit and documentation synchronization

Run the isolated package, inspect every source-sensitive axiom dependency, update the Architecture and Crosswalk to match the actual proof state, and make the final completion claim only after all release gates pass.

---

# Repository workflow

`push_to_github.bat` is an owner-operated publication step.

It is separate from proof verification.

A GitHub push means a selected local snapshot was published. It does not by itself establish that the isolated package was freshly built or audited.

Agents must not push unless separately instructed.

After a substantive milestone, update the suggested commit message in the Research Agenda and pass an appropriate message to the push script, for example:

```bat
push_to_github.bat "PostGM Gafni-Tao: close Ford near-one source inputs"
```

---

# Completion condition

The project should be called a completed formalization of the intended Gafni-Tao theorem only when the dependency graph has the form:

```text
accepted Lean / Mathlib foundation
             |
             v
frozen Guth-Maynard foundation
             |
             +------------------------------+
             |                              |
             v                              v
native sharp explicit formula      native Ford/VK source inputs
             |                              |
             +---------------+--------------+
                             |
                             v
                  Section 2 moment machinery
                             |
                             v
                     equation (2.7)
                             |
                             v
                  exceptional-set measure
                             |
                             v
                   exceptional exponent
                             |
                             v
               exact Gafni-Tao Theorem 1.3
                             |
                             v
               Theorems 1.2 and 1.1
                             |
                             v
              published numerical consumers
```

with no unresolved project-level analytic assumptions hidden inside the claimed dependency path.

Until then:

**formalization in progress, with most of the Section 2 transfer mechanism implemented and the active mathematical front concentrated in native Ford/Vinogradov-Korobov source closure.**