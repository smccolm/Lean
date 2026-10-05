# Dong–Wang–Wang–Zhang checklist

4 October 2026. **ACTIVE DEVELOPMENT. Proof acceptance: 7/20.** DWWZ-01 and DWWZ-03 pass their exact acceptance requirements, including the paper and foundation BATs. Actual maximizing-twist existence, prime-phase estimates and the phase-specialized source comparison (2.2) are proved. Lemma 2.2's displacement, prime distance and reversed comparison are proved at the same witness. DWWZ-05/06 are DONE after combined BAT/audit acceptance of full Lemma 2.2; full hybrid (2.1) is not claimed. Both main theorems remain open.

| ID | Status | Required acceptance result |
|---|---|---|
| DWWZ-01 | DONE | Select one compatible Lean/Mathlib/PNT graph, create the isolated package only after authorization, verify source dependencies and maintain both BAT interfaces. |
| DWWZ-02 | OPEN | Freeze exact Lean types of T1/T2 with all source quantifiers, constants, ranges and multiplicities; exact-type regressions import actual public results. |
| DWWZ-03 | DONE | Actual finite zeta sum, floor/positive-index convention, unit norm, conjugation, complete multiplicativity, and shifted Dirichlet-series identity. |
| DWWZ-04 | OPEN | Actual nontrivial-zero disk/window counts and infinite weighted sums; prove multiplicity, finiteness, conjugation, rectangle and divisor-index bridges. |
| DWWZ-05 | DONE | Analytic mean-value, twist comparison and Lipschitz inputs of Lemma 2.1, at least at the faithful specialization consumed by Lemma 2.2; no citation-as-axiom. |
| DWWZ-06 | DONE | Lemma 2.2: actual maximizing twist, absolute displacement bound, M bound, all-real-y 1/3 continuity and x/(log x)^(3/4) comparison error with uniform constants. |
| DWWZ-07 | DONE | Lemma 3.1, uniform for 0<λ≤1/2 and every real v, from an actual Euler–Maclaurin/Abel continuation with the pole displayed. |
| DWWZ-08 | DONE | Entire xi factorization, zero-divisor summability and real log-derivative identities; import genuine consumers, not an assumed product. |
| DWWZ-09 | OPEN | Lemma 3.2 with the exact 2λ² zero kernel and absolute prefactor O(1/λ), including small heights and gamma/pole factors. |
| DWWZ-10 | DONE | Lemma 3.3: exact Gaussian transform with its positive pole-residue term; integrability, Fubini, normalization and contour limiting steps proved. |
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

DWWZ-10's `source_gaussian_identity` now compiles with the exact normalization,
sign, shifted zeta and positive pole term. Both source integrals are absolutely
convergent. Five new regressions retain the analytic continuation, full-strip
transform, zero-twist residue, convergence and exact identity. Combined BAT/audit
and semantic acceptance passed. No source statement or acceptance text is changed.

DWWZ-08's actual xi divisor, inverse-square convergence, multiplicity-preserving
reflection and real logarithmic-derivative consumers compile. The exact
zeta/gamma decomposition has no factorization or zero-sum premise. Seven
regressions retain these contracts; both BATs, dependency and semantic audits pass.
DWWZ-04's remaining disk/window/rectangle and conjugation bridges stay OPEN.

DWWZ-07's exact uniform consumer is kernel-checked with constant 8, including
zero height and the closed half endpoint. Its explicit-pole continuation and
four regressions are integrated and passed both BATs with zero Lean diagnostics.

Further Lipschitz-path inputs now proved: the difference-factor Poisson identity/transport, including initial damping, and actual ordinary/weighted dilation Laplace transforms. `TwoPointEuler` proves the actual reciprocal-prime cosine estimate with coefficient `75/113<2/3`, two-point zeta repulsion, and the same-maximizer off-frequency bound with an internally chosen PNT scale. The optimized dilation-factor bound and its same-maximizer rightward transport are proved. The actual weighted-difference Parseval identity and full near/far mean square are now proved in `DilationMeanSquare`, consuming the optimized factor. `DilationSmoothing` proves actual difference smoothing with active-cutoff floor control, and the mean-square consumer now retains `min(M_A+16,4/δ)`. `DilationAssembly` proves damping-parameter assembly and uniform power-loss evaluation. `DilationLipschitz` now proves scalar absorption to `1/3`, all-real cutoff assembly and the full same-witness Lemma 2.2. Combined BAT/audit acceptance passed. This closes the faithful consumed specialization, not GS03's optimal `2/π` estimate.

The ordinary pointwise smoothing sub-obligation is proved by installed Brun–Titchmarsh on quartic cells, exact Mangoldt convolution and Abel summation, with explicit absolute constants and no PNT premise. Damping-parameter assembly is proved, including Fubini, weighted Cauchy–Schwarz and evaluation of the minimum integral. Its Euler substitution proves ordinary prime-distance control. `exists_large_sum_twist_bounds` consumes the exact distance clause and (2.2), proving `|t₀|≤4N`, the source M bound and reversed comparison error `≤4x/(log x)^(3/4)` at one actual source maximizer. Uniform Lipschitz and full Lemma 2.2 are kernel-checked; DWWZ-05/06 are DONE after both BATs and the semantic audit passed. The full hybrid (2.1) is still an unproved reference target, not an assumed input.

Additional DWWZ-05 progress: actual ordinary/weighted Laplace/Fourier/Parseval identities, the uniform von Mangoldt mean square and the actual-maximizer near-frequency bound are proved. In addition to retained individual-block estimates, Gaussian Gram averaging and dominated convergence prove the sharp **full-series** derivative mean square and two-sided far tail, including both coefficient summability bounds. Half-plane Poisson reproduction transports the original maximizer rightward and supplies a full weighted-summatory mean square with the same maximizer. The one-point Euler bound, reciprocal-prime upper bound and distance-form source comparison are proved and consumed by the ordinary distance theorem above. These inputs are consumed by the accepted DWWZ-05/06 chain. The proved ordinary full-series route needs no smooth-number adapter. The Gaussian averaging is not DWWZ-10's residue-bearing transform.
