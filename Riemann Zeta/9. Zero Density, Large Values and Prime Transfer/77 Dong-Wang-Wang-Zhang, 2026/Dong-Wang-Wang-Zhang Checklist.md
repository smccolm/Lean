# Dong–Wang–Wang–Zhang checklist

4 October 2026. **PLANNING ONLY. Proof acceptance: 0/20.** All items below are OPEN and unstarted. Research/scaffold preparation is separate from proof acceptance. Module names in the crosswalk are proposals, not existing Lean declarations.

| ID | Status | Required acceptance result |
|---|---|---|
| DWWZ-01 | OPEN | Select one compatible Lean/Mathlib/PNT graph, create the isolated package only after authorization, verify source dependencies and maintain both BAT interfaces. |
| DWWZ-02 | OPEN | Freeze exact Lean types of T1/T2 with all source quantifiers, constants, ranges and multiplicities; exact-type regressions import actual public results. |
| DWWZ-03 | OPEN | Actual finite zeta sum, floor/positive-index convention, unit norm, conjugation, complete multiplicativity, and shifted Dirichlet-series identity. |
| DWWZ-04 | OPEN | Actual nontrivial-zero disk/window counts and infinite weighted sums; prove multiplicity, finiteness, conjugation, rectangle and divisor-index bridges. |
| DWWZ-05 | OPEN | Analytic mean-value, twist comparison and Lipschitz inputs of Lemma 2.1, at least at the faithful specialization consumed by Lemma 2.2; no citation-as-axiom. |
| DWWZ-06 | OPEN | Lemma 2.2: actual maximizing twist, absolute displacement bound, M bound, all-real-y 1/3 continuity and x/(log x)^(3/4) comparison error with uniform constants. |
| DWWZ-07 | OPEN | Lemma 3.1, uniform for 0<λ≤1/2 and every real v, from an actual Euler–Maclaurin/Abel continuation with the pole displayed. |
| DWWZ-08 | OPEN | Entire xi factorization, zero-divisor summability and real log-derivative identities; import genuine consumers, not an assumed product. |
| DWWZ-09 | OPEN | Lemma 3.2 with the exact 2λ² zero kernel and absolute prefactor O(1/λ), including small heights and gamma/pole factors. |
| DWWZ-10 | OPEN | Lemma 3.3: exact Gaussian transform with its positive pole-residue term; integrability, Fubini, normalization and contour limiting steps proved. |
| DWWZ-11 | OPEN | Lemma 3.4: uniform zero-sum upper bound (1/2)log(2+a+|v|)+1/a+O(1) for every a>0, |v|≥2. |
| DWWZ-12 | OPEN | Proposition 4.1 from the actual large sum: Gaussian lower bound, negligible residue, both frequency tails, an actual η, conjugation and weighted-zero lower bound. |
| DWWZ-13 | OPEN | Actual zero-measure near/far split, far contribution ≤5(log x)/36, near contribution ≥(log x)/9 and open-disk multiplicity count; exact linked scale choices. |
| DWWZ-14 | OPEN | Public T1 consumes the original sum and all preceding analytic outputs, with one center before every L; no additional analytic assumption. |
| DWWZ-15 | OPEN | Lemma 5.1: absolute O(x T^(-1/13)) for every x≥sqrt T, both signs, dyadic final subintervals, and the x>|t| first-derivative tail. |
| DWWZ-16 | OPEN | Public T2 on the whole T^ε≤x≤T^A range; derive admissible L, window inclusion and strict 1/360 versus 1/400 contradiction, then assemble large x. |
| DWWZ-17 | OPEN | Semantic regressions cover boundary/sign/zero/pole/normalization/constant-dependence cases and any discovered counterexamples or source repairs. |
| DWWZ-18 | OPEN | All production modules imported, filesystem inventory complete, explicit and exhaustive transitive dependency audits, no shortcuts, zero project Lean diagnostics. |
| DWWZ-19 | OPEN | Paper proof BAT and foundation BAT pass sequentially from a reproducible pinned checkout; record exact commands, status, exit codes, logs and hashes. |
| DWWZ-20 | OPEN | README, contract, crosswalk, architecture, checklist, agenda, errata and reproduction manifest agree with actual public theorem dependencies and tested scope. |

A gate becomes DONE only when its exact consumer is kernel-checked, audited, integrated and semantically matched. An installed source, a proposition definition, a clean unrelated package, or a proof that returns its own hypothesis is not completion. Source errors do not disappear on changing a checklist description.
