# Gafni-Tao exceptional intervals

## Status

**Active isolated formalization.**

The project has progressed beyond foundational scaffolding. The main Section 2 zero-density-to-exceptional-set transfer mechanism is now implemented in Lean, including:

- the exact Mangoldt short-interval exceptional set;
- Lebesgue-measure exceptional exponents;
- zero counting with multiplicity;
- the multiplicity-weighted four-zero quantity `N*` and exponent `A*`;
- second- and fourth-moment zero-sum estimates;
- finite zero strips;
- Markov conversion;
- the equation (2.7) exceptional-set reduction;
- epsilon and finite-strip limiting machinery;
- finite multiplicative covering from local intervals back to the global exceptional set;
- a native sharp truncated explicit formula;
- conditional assembled forms of Gafni-Tao Theorems 1.2 and 1.3.

The principal remaining analytic frontier is the unconditional construction of the published near-one zero-density and Vinogradov-Korobov zero-free inputs required by the Gafni-Tao argument.

The complete Gafni-Tao formalization is **not yet claimed**.

---

## Purpose

This directory is the isolated post-Guth-Maynard program for formalizing Ayla Gafni and Terence Tao's paper:

*On the number of exceptional intervals to the prime number theorem in short intervals*

arXiv:2505.24017v1.

The target is the paper's actual zero-density-to-exceptional-set argument, including the fourth-moment refinement and the numerical consequences obtained after supplying the required density and additive-energy inputs.

The intended endpoint is not merely a theorem with the same numerical shape. The goal is to formalize the mathematical dependency chain used by the paper closely enough that the final public theorem can be audited against the source argument.

This work does not prove the Riemann Hypothesis, and nothing in this directory should be described as doing so.

---

# Current mathematical state

The implemented proof architecture is now approximately:

$$
\text{zeta zeros}
\longrightarrow
N(\sigma,T),\,N^*(\sigma,T)
\longrightarrow
A(\sigma),\,A^*(\sigma)
$$

$$
\longrightarrow
L^\infty,\ L^2,\ L^4
\text{ zero-sum bounds}
$$

$$
\longrightarrow
\text{equation (2.7) large-value set}
$$

$$
\longrightarrow
\text{local exceptional-measure bounds}
$$

$$
\longrightarrow
\text{finite-strip and }\varepsilon\text{ limits}
$$

$$
\longrightarrow
\mathrm{meas}\,E_\delta(X,\theta)
\ll
X^\xi
$$

$$
\longrightarrow
\mu_\delta(\theta)
\longrightarrow
\mu(\theta).
$$

Most of this transfer machinery now exists as Lean theorems.

The major remaining conditionality lies upstream in the published near-one analytic inputs.

---

# Implemented theorem spine

## 1. Exceptional sets

The formalization defines the actual Mangoldt short-interval exceptional set rather than a proxy quantity.

The basic object has the mathematical form

$$
E_\delta(X,\theta)
=
\left\{
x\in[X,2X]:
\left|
\psi(x+x^\theta)-\psi(x)-x^\theta
\right|
\ge
\delta x^\theta
\right\}.
$$

The project then defines the corresponding measure exponent

$$
\mu_\delta(\theta)
$$

and the limiting exceptional exponent

$$
\mu(\theta).
$$

The implementation includes measurability, finite-measure facts, monotonicity in the exceptional threshold, fixed-power bounds, and the countable reduction needed to pass from the threshold-dependent exponent to the final exceptional exponent.

---

## 2. Zero counting and multiplicity

The project contains native infrastructure for the nontrivial zeros of the Riemann zeta function and the multiplicity-weighted zero counts required by the paper.

This includes the formal counterparts of quantities such as

$$
N(\sigma,T)
$$

and the four-zero additive-energy count

$$
N^*(\sigma,T).
$$

The four-zero object is treated with zero occurrences and multiplicity rather than silently replacing the paper's quantity by a set cardinality.

The associated exponent interfaces `A` and `A*` provide the bridge from zero-density estimates to the moment calculations used later in the proof.

---

## 3. Second and fourth moments

The Section 2 second- and fourth-moment branches have been formalized at the intended multiplicity-sensitive level.

The fourth-moment route feeds the `A*` contribution into the refined exceptional exponent, rather than reducing the argument to the ordinary zero-density exponent `A`.

This is the branch responsible for the refinement distinguishing Theorem 1.3 from the ordinary second-moment envelope.

---

## 4. Sharp truncated explicit formula

A native sharp explicit-formula branch is now present.

The main endpoint is:

```lean
GafniTao.sharpTruncatedExplicitFormulaBound_native
```

The supporting development includes a substantial sharp-Perron chain:

- finite Mangoldt Perron identities;
- logarithmic derivative expansions;
- Perron kernels;
- contour decomposition;
- horizontal and vertical edge estimates;
- residue contributions;
- cutoff-error estimates;
- treatment of integral and half-integral endpoint geometry;
- selected good heights;
- conversion to the sharp truncation estimate.

The target range includes arbitrary real endpoints and the full regime

$$
2 \le T \le x.
$$

This means the sharp explicit formula should no longer be regarded as one of the principal unresolved source inputs.

---

## 5. Equation (2.7) reduction

The formalization now contains the actual exceptional-set reduction corresponding to the central large-zero-sum step in Section 2.

The theorem chain includes results of the form:

```lean
eventually_localExceptionalSet_subset_equation27
eventually_localExceptionalMeasure_le_equation27
localExceptionalMeasure_fixedPowerBound_of_equation27
```

This connects failure of the prime number theorem in a short interval to an appropriately large truncated zero sum.

This is an important transition in the formalization because the measure-theoretic exceptional set is no longer disconnected from the zero-density machinery.

---

## 6. Local-to-global assembly

The project now contains the finite multiplicative covering argument required to pass from local exceptional-set estimates to the full interval.

Relevant theorems include:

```lean
shortIntervalExceptionalSet_subset_local_union
exceptionalMeasure_le_sum_local
exceptionalMeasure_fixedPowerBound_of_local
exceptionalMeasure_fixedPowerBound_of_source_inputs
```

The local source estimates therefore feed an actual fixed-power bound for the measure of the original short-interval exceptional set.

---

## 7. Finite strips and limiting argument

The finite-strip decomposition and limiting machinery needed to remove the auxiliary discretization parameters are implemented.

This includes the selection of sufficiently fine strip parameters relative to the competing exponent margins and the conversion from epsilon-dependent bounds to fixed-power measure estimates.

The resulting machinery feeds directly into the exceptional exponent.

This part of the proof should now be regarded as implemented rather than merely planned.

---

# Conditional Gafni-Tao theorem interfaces

## Refined theorem

The current assembled refined endpoint is:

```lean
GafniTao.gafniTaoTheorem13_max_conditional
```

It yields a bound of the schematic form

$$
\mu(\theta)
\le
\max
\left\{
1-\theta,\,
\mathcal R(\theta)
\right\},
$$

where $\mathcal R(\theta)$ is the refined expression obtained from the zero-density and four-zero additive-energy exponents after the epsilon and strip limits.

This is a genuine assembled theorem, but it remains conditional on named analytic source inputs.

It must therefore **not** yet be advertised as an unconditional formalization of Gafni-Tao Theorem 1.3.

There is also a theorem-statement issue still to close: the exact relation between this `max` formulation and the principal formulation stated in the source paper must be made explicit before the corresponding acceptance item is closed.

---

## Ordinary theorem

The current ordinary endpoint is:

```lean
GafniTao.gafniTaoTheorem12_max_conditional
```

This follows from the refined theorem by replacing the fourth-moment improvement by the ordinary density envelope.

Schematically,

$$
\mu(\theta)
\le
\max
\left\{
1-\theta,\,
\mathcal O(\theta)
\right\}.
$$

Again, this theorem is real Lean output, but it remains conditional and should not yet be labelled as the final unconditional source theorem.

---

# Remaining analytic frontier

The largest unresolved mathematical work is now concentrated in the near-one zero theory required by Lemma 2.1 and related arguments.

## Ford near-one zero density

The project exposes a source-facing proposition representing the required Ford-type near-one zero-density estimate.

The normalization layer converts the source estimate into the downstream form required by the Gafni-Tao proof, including a bound of the shape

$$
N(1-\eta,T)
\le
T^{58.05\,\eta^{3/2}}
(\log T)^{16}.
$$

The normalization and consumer bridge exist.

What remains is to derive the required source theorem itself from sufficiently primitive analytic results inside the trusted Lean dependency chain.

The active Ford development already includes substantial supporting infrastructure, including:

- trigonometric identities and positivity;
- Fourier kernels;
- beta and hyperbolic-function integral identities;
- Euler-product and logarithmic zeta expansions;
- prime-power series;
- integral and summability arguments;
- Ford Lemma 5.1 infrastructure;
- logarithmic-derivative estimates;
- right-edge zero weights and cumulative zero counts;
- zero-detection machinery.

The intended endpoint is an unconditional Lean witness for the near-one density input consumed by the Gafni-Tao theorem spine.

---

## Vinogradov-Korobov zero-free region

The project contains the consumer-facing Vinogradov-Korobov interface and proves the bridge from a suitable rectangle zero-free theorem to the exact count-level vanishing statement used downstream.

The remaining task is therefore not to invent the downstream interface.

It is to construct the required zero-free theorem from the accepted source mathematics.

The desired dependency direction is:

$$
\text{Vinogradov-Korobov source theorem}
$$

$$
\Downarrow
$$

$$
\text{rectangle zero-free statement}
$$

$$
\Downarrow
$$

$$
\mathrm{VinogradovKorobovCountVanishing}
$$

$$
\Downarrow
$$

$$
\text{Gafni-Tao near-one machinery}.
$$

---

# Present dependency frontier

At a high level, the project is approaching the following structure:

```text
FROZEN GUTH-MAYNARD FOUNDATION
             |
             v
     zero-density inputs
             |
             +----------------------+
             |                      |
             v                      v
       second moment          fourth moment / N*
             |                      |
             +----------+-----------+
                        |
                        v
                equation (2.7)
                        |
                        v
              finite-strip bounds
                        |
                        v
              local exceptional set
                        |
                        v
             multiplicative covering
                        |
                        v
                 mu_delta(theta)
                        |
                        v
                    mu(theta)
```

with a second analytic branch:

```text
Ford near-one density --------+
                              |
Vinogradov-Korobov ------------+--> near-one source inputs
                              |
native sharp explicit formula -+
                              |
                              v
                   assembled GT theorem
```

The sharp explicit-formula branch is now implemented.

The main open source branches are Ford near-one density and Vinogradov-Korobov.

---

# Section 3 and numerical consequences

The later numerical consequences of the paper are not yet complete.

Outstanding work includes the relevant published numerical inputs and optimization steps associated with results such as

$$
\theta > \frac{17}{30}
$$

and the short-interval threshold

$$
\theta > \frac{7}{12}.
$$

The project also still needs the appropriate Pintz and Heath-Brown source inputs, the required small-$\Delta$ arguments, and a certified optimization layer where numerical minimization or maximization enters the final result.

These numerical consumers should remain downstream work.

The current priority is to close the analytic inputs to the general Gafni-Tao transfer theorem before building additional conditional numerical layers on top of it.

---

# Audit surface

The isolated package contains:

```text
Extension/GafniTao/Audit.lean
```

`Audit.lean` explicitly lists the public and source-sensitive theorem surface using `#print axioms`.

The audit currently covers, among many other results:

```lean
GafniTao.sharpPsiTruncationBound_native
GafniTao.sharpTruncatedExplicitFormulaBound_native

GafniTao.eventually_localExceptionalSet_subset_equation27
GafniTao.localExceptionalMeasure_fixedPowerBound_of_source_inputs
GafniTao.exceptionalMeasure_fixedPowerBound_of_source_inputs

GafniTao.exceptionalExponentDelta_le_refined_max_of_source_inputs
GafniTao.gafniTaoTheorem13_max_conditional
GafniTao.gafniTaoTheorem12_max_conditional

GafniTao.nearOneLogDensityBound_of_fordNearOneDensityEstimate
GafniTao.vinogradovKorobovCountVanishing_of_rectangleZeroFree
GafniTao.exists_nearOne_inputs_of_ford_outputs
```

and the growing Ford source-development theorem surface.

The existence of a theorem in `Audit.lean` means it has been placed on the explicit dependency-audit surface. It does **not**, by itself, certify that the complete isolated release audit has been freshly executed successfully.

Before any final release claim, run the isolated package and inspect the actual axiom output.

---

# Verification

Run commands from:

```text
Riemann Zeta/PostGM/GafniTao/Extension
```

The package is intentionally separate from the frozen Guth-Maynard source tree.

A release-quality verification should include at least:

```bash
lake build
lake env lean GafniTao/Audit.lean
```

and a source scan for unfinished or unsafe declarations.

For example:

```bash
rg -n '\bsorry\b|\badmit\b|\bnative_decide\b|^\s*(axiom|opaque|unsafe)\b' --glob '*.lean' .
```

Interpret the results carefully.

A source-level `axiom` or opaque placeholder in the project is not acceptable merely because downstream theorems compile.

Likewise, the output of `#print axioms` must be inspected rather than assuming that compilation implies the intended dependency boundary.

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

- Foundation Lean version:

```text
v4.30.0
```

- Planning commit at creation of this directory:

```text
3e1eff79810846335386c2f4bc0ec1957272e301
```

All Gafni-Tao Lean development belongs below:

```text
PostGM/GafniTao/Extension/
```

in its separate Lake package pinned to the frozen foundation.

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

A theorem is not considered complete merely because a downstream implication has been formalized.

For a source result to be marked DONE, the project should establish all of the following where applicable:

1. The statement matches the source theorem with the required parameter range.
2. Multiplicities are represented correctly.
3. Endpoint conventions match the source argument.
4. Constants and logarithmic factors are accounted for.
5. The proof does not rely on a project-level `axiom`, `sorry`, `admit`, unsafe shortcut, or disguised restatement of the desired result.
6. The theorem appears on the audit surface.
7. The isolated package builds.
8. The actual `#print axioms` output is inspected.
9. The crosswalk and architecture documents are synchronized with the implementation.
10. The public README describes the theorem no more strongly than the Lean development warrants.

---

# Claim discipline

The strongest truthful summary of the repository at present is:

> A substantial part of the Gafni-Tao exceptional-interval argument has been formalized in Lean. The exact exceptional-set framework, multiplicity-sensitive zero counts, second- and fourth-moment machinery, equation (2.7) reduction, finite-strip and limiting assembly, local-to-global covering argument, and a native sharp truncated explicit formula are implemented. Conditional assembled forms of Theorems 1.2 and 1.3 exist. The full Gafni-Tao theorem is not yet claimed because the required published near-one zero-density and Vinogradov-Korobov source inputs, exact final theorem closure, later numerical consumers, and final isolated audit remain unfinished.

Do not shorten that to:

```text
Gafni-Tao is proved in Lean.
```

That statement is not currently justified.

Likewise, do not describe the conditional theorems

```lean
gafniTaoTheorem13_max_conditional
gafniTaoTheorem12_max_conditional
```

as the final source theorems without stating their remaining hypotheses.

---

# Documents

The directory contains the project-control documents used to keep the formalization synchronized with the paper.

- [Gafni-Tao Sources.md](Gafni-Tao%20Sources.md)

  Authoritative source references, reusable Lean infrastructure, and identified source gaps.

- [Gafni-Tao Architecture.md](Gafni-Tao%20Architecture.md)

  Numbered dependency graph and module architecture.

- [Gafni-Tao Research Agenda.md](Gafni-Tao%20Research%20Agenda.md)

  Mathematical execution route and active implementation order.

- [Gafni-Tao Crosswalk.md](Gafni-Tao%20Crosswalk.md)

  Source-to-Lean theorem mapping and implementation status.

- [Gafni-Tao Shitlist.md](Gafni-Tao%20Shitlist.md)

  Detailed acceptance checklist.

- [Gafni-Tao Goal Prompt.md](Gafni-Tao%20Goal%20Prompt.md)

  Persistent implementation objective for coding agents.

These documents are project-control artifacts, not proof objects.

When documentation and Lean disagree about implementation status, inspect the Lean source and audit surface and then repair the documentation.

---

# Near-term execution order

The recommended order from the current state is:

## 1. Close the Ford source theorem

Continue the active Ford development until the project can construct the near-one logarithmic density input without assuming the source estimate as a hypothesis.

Target direction:

```text
Ford analytic lemmas
        |
        v
FordNearOneDensityEstimate
        |
        v
NearOneLogDensityBound
```

## 2. Close Vinogradov-Korobov

Construct the required zero-free region internally and feed it through the already implemented bridge:

```text
Vinogradov-Korobov theorem
        |
        v
rectangle zero-free
        |
        v
VinogradovKorobovCountVanishing
```

## 3. Remove resolved hypotheses from the public GT endpoint

The native sharp explicit formula already exists.

The final theorem interface should therefore be refactored so that an analytic hypothesis that has already been proved internally does not remain exposed unnecessarily at the top level.

## 4. Close the exact theorem-statement correspondence

Prove the exact relation between the current `max` formulations and the principal Gafni-Tao theorem statements.

Only then should Theorems 1.2 and 1.3 be marked DONE in the project crosswalk.

## 5. Complete the numerical consumers

After the general theorem is unconditional, formalize the remaining Pintz, Heath-Brown, small-$\Delta$, and optimization inputs required for the paper's explicit numerical corollaries.

## 6. Final audit

Run the isolated build, execute `Audit.lean`, inspect every nonstandard axiom dependency, scan for unfinished declarations, synchronize the project documents, and only then make a completion claim.

---

# Repository workflow

`push_to_github.bat` is an owner-operated publication step.

It is deliberately separate from proof verification.

A GitHub push means that a chosen local snapshot was published. It does not, by itself, mean that the Gafni-Tao package was freshly built or audited.

The project owner controls pushes.

Agents must not push unless separately instructed.

After a substantive milestone, update the suggested commit message in the research agenda and pass an appropriate message to the push script, for example:

```bat
push_to_github.bat "PostGM Gafni-Tao: close Ford near-one density input"
```

---

# Completion condition

This project should be considered a completed formalization of the intended Gafni-Tao result only when the dependency graph has the form:

```text
accepted Lean / Mathlib foundation
             |
             v
frozen Guth-Maynard results
             |
             v
native explicit formula
             |
             +-----------------------------+
             |                             |
             v                             v
Ford near-one density          Vinogradov-Korobov
             |                             |
             +--------------+--------------+
                            |
                            v
                 Section 2 moment machinery
                            |
                            v
                    equation (2.7)
                            |
                            v
                  exceptional measure
                            |
                            v
                  exceptional exponent
                            |
                            v
             exact Gafni-Tao theorem
```

with no unresolved project-level analytic assumptions hiding inside that path.

After that, the numerical consequences can be audited as consumers of the completed general theorem.

Until then:

**formalization in progress, with the principal Section 2 transfer mechanism already substantially implemented.**