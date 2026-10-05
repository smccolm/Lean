# Dong–Wang–Wang–Zhang checklist

5 October 2026. **PROJECT COMPLETE. Proof acceptance: 20/20.** DWWZ-01 and DWWZ-03 pass their exact acceptance requirements, including the paper and foundation BATs. Actual maximizing-twist existence, prime-phase estimates and the phase-specialized source comparison (2.2) are proved. Lemma 2.2's displacement, prime distance and reversed comparison are proved at the same witness. DWWZ-05/06 are DONE after combined BAT/audit acceptance of full Lemma 2.2; full hybrid (2.1) is not claimed. T1 now compiles at its frozen type, with both BATs and exact semantic acceptance passed. T2 and Lemma 5.1 now compile, with exact-type regressions; combined BAT/audit and semantic acceptance passed.

| ID | Status | Required acceptance result |
|---|---|---|
| DWWZ-01 | DONE | Select one compatible Lean/Mathlib/PNT graph, create the isolated package only after authorization, verify source dependencies and maintain both BAT interfaces. |
| DWWZ-02 | DONE | Freeze exact Lean types of T1/T2 with all source quantifiers, constants, ranges and multiplicities; exact-type regressions import actual public results. |
| DWWZ-03 | DONE | Actual finite zeta sum, floor/positive-index convention, unit norm, conjugation, complete multiplicativity, and shifted Dirichlet-series identity. |
| DWWZ-04 | DONE | Actual nontrivial-zero disk/window counts and infinite weighted sums; prove multiplicity, finiteness, conjugation, rectangle and divisor-index bridges. |
| DWWZ-05 | DONE | Analytic mean-value, twist comparison and Lipschitz inputs of Lemma 2.1, at least at the faithful specialization consumed by Lemma 2.2; no citation-as-axiom. |
| DWWZ-06 | DONE | Lemma 2.2: actual maximizing twist, absolute displacement bound, M bound, all-real-y 1/3 continuity and x/(log x)^(3/4) comparison error with uniform constants. |
| DWWZ-07 | DONE | Lemma 3.1, uniform for 0<λ≤1/2 and every real v, from an actual Euler–Maclaurin/Abel continuation with the pole displayed. |
| DWWZ-08 | DONE | Entire xi factorization, zero-divisor summability and real log-derivative identities; import genuine consumers, not an assumed product. |
| DWWZ-09 | DONE | Lemma 3.2 with the exact 2λ² zero kernel and absolute prefactor O(1/λ), including small heights and gamma/pole factors. |
| DWWZ-10 | DONE | Lemma 3.3: exact Gaussian transform with its positive pole-residue term; integrability, Fubini, normalization and contour limiting steps proved. |
| DWWZ-11 | DONE | Lemma 3.4: uniform zero-sum upper bound (1/2)log(2+a+|v|)+1/a+O(1) for every a>0, |v|≥2. |
| DWWZ-12 | DONE | Proposition 4.1 from the actual large sum: Gaussian lower bound, negligible residue, both frequency tails, an actual η, conjugation and weighted-zero lower bound. |
| DWWZ-13 | DONE | Actual zero-measure near/far split, far contribution ≤5(log x)/36, near contribution ≥(log x)/9 and open-disk multiplicity count; exact linked scale choices. |
| DWWZ-14 | DONE | Public T1 consumes the original sum and all preceding analytic outputs, with one center before every L; no additional analytic assumption. |
| DWWZ-15 | DONE | Lemma 5.1: absolute O(x T^(-1/13)) for every x≥sqrt T, both signs, dyadic final subintervals, and the x>|t| first-derivative tail. |
| DWWZ-16 | DONE | Public T2 on the whole T^ε≤x≤T^A range; derive admissible L, window inclusion and strict 1/360 versus 1/400 contradiction, then assemble large x. |
| DWWZ-17 | DONE | Semantic regressions cover boundary/sign/zero/pole/normalization/constant-dependence cases and any discovered counterexamples or source repairs. |
| DWWZ-18 | DONE | All production modules imported, filesystem inventory complete, explicit and exhaustive transitive dependency audits, no shortcuts, zero project Lean diagnostics. |
| DWWZ-19 | DONE | Paper proof BAT and foundation BAT pass sequentially from a reproducible pinned checkout; record exact commands, status, exit codes, logs and hashes. |
| DWWZ-20 | DONE | README, contract, crosswalk, architecture, checklist, agenda, errata and reproduction manifest agree with actual public theorem dependencies and tested scope. |

The full `large_zeta_sum_forces_zero_disk` consumer and its actual near/far count now compile. Four modules and five new regressions are integrated; DWWZ-13/14 are DONE after both BATs and exact semantic review passed. T2's actual public result and exact regression are now integrated. DWWZ-02/15/16/17/18/19/20 are DONE after the combined verification, exact consumer review and synchronized documentation. All twenty original acceptance descriptions are unchanged.

A gate becomes DONE only when its exact consumer is kernel-checked, audited, integrated and semantically matched. An installed source, a proposition definition, a clean unrelated package, or a proof that returns its own hypothesis is not completion. Source errors do not disappear on changing a checklist description.

DWWZ-12's full `exists_large_sum_weighted_zero_forcing` consumer now
compiles from the original large sum, with one maximizing twist before
every admissible scale, actual η, summability and the exact lower bound.
The four-module Gaussian/forcing chain and ten new regressions are
integrated. Both BATs and exact semantic acceptance passed; DWWZ-12 is DONE.

DWWZ-09's exact `exists_source_zero_repulsion` consumer now compiles for
every real height, with summability and the exact quadratic zero kernel.
Six regressions and all supporting modules are integrated; both BATs
and the exact semantic acceptance passed.

DWWZ-11's exact `exists_source_zero_sum_upper` consumer now compiles for
all positive a and both closed height endpoints, with convergence and one
absolute remainder constant. Its five regressions and all three quantitative
modules are integrated; both BATs and the exact semantic acceptance passed.

DWWZ-10's `source_gaussian_identity` now compiles with the exact normalization,
sign, shifted zeta and positive pole term. Both source integrals are absolutely
convergent. Five new regressions retain the analytic continuation, full-strip
transform, zero-twist residue, convergence and exact identity. Combined BAT/audit
and semantic acceptance passed. No source statement or acceptance text is changed.
The accepted alternate route discharges the analytic continuation obligation by
regularized Mellin continuation and Gaussian Fubini; it does not claim a separate
moving-contour proof. The original contour-limiting wording above records the
planned route, while the exact source identity and all convergence obligations
are proved by this alternate route.

DWWZ-08's actual xi divisor, inverse-square convergence, multiplicity-preserving
reflection and real logarithmic-derivative consumers compile. The exact
zeta/gamma decomposition has no factorization or zero-sum premise. Seven
regressions retain these contracts; both BATs, dependency and semantic audits pass.
DWWZ-04's disk/window/rectangle and conjugation bridges now compile, with eight new regressions and explicit audits. Both BATs and exact semantic acceptance passed; DWWZ-04 is DONE.

DWWZ-07's exact uniform consumer is kernel-checked with constant 8, including
zero height and the closed half endpoint. Its explicit-pole continuation and
four regressions are integrated and passed both BATs with zero Lean diagnostics.

Further Lipschitz-path inputs now proved: the difference-factor Poisson identity/transport, including initial damping, and actual ordinary/weighted dilation Laplace transforms. `TwoPointEuler` proves the actual reciprocal-prime cosine estimate with coefficient `75/113<2/3`, two-point zeta repulsion, and the same-maximizer off-frequency bound with an internally chosen PNT scale. The optimized dilation-factor bound and its same-maximizer rightward transport are proved. The actual weighted-difference Parseval identity and full near/far mean square are now proved in `DilationMeanSquare`, consuming the optimized factor. `DilationSmoothing` proves actual difference smoothing with active-cutoff floor control, and the mean-square consumer now retains `min(M_A+16,4/δ)`. `DilationAssembly` proves damping-parameter assembly and uniform power-loss evaluation. `DilationLipschitz` now proves scalar absorption to `1/3`, all-real cutoff assembly and the full same-witness Lemma 2.2. Combined BAT/audit acceptance passed. This closes the faithful consumed specialization, not GS03's optimal `2/π` estimate.

The ordinary pointwise smoothing sub-obligation is proved by installed Brun–Titchmarsh on quartic cells, exact Mangoldt convolution and Abel summation, with explicit absolute constants and no PNT premise. Damping-parameter assembly is proved, including Fubini, weighted Cauchy–Schwarz and evaluation of the minimum integral. Its Euler substitution proves ordinary prime-distance control. `exists_large_sum_twist_bounds` consumes the exact distance clause and (2.2), proving `|t₀|≤4N`, the source M bound and reversed comparison error `≤4x/(log x)^(3/4)` at one actual source maximizer. Uniform Lipschitz and full Lemma 2.2 are kernel-checked; DWWZ-05/06 are DONE after both BATs and the semantic audit passed. The full hybrid (2.1) is still an unproved reference target, not an assumed input.

Additional DWWZ-05 progress: actual ordinary/weighted Laplace/Fourier/Parseval identities, the uniform von Mangoldt mean square and the actual-maximizer near-frequency bound are proved. In addition to retained individual-block estimates, Gaussian Gram averaging and dominated convergence prove the sharp **full-series** derivative mean square and two-sided far tail, including both coefficient summability bounds. Half-plane Poisson reproduction transports the original maximizer rightward and supplies a full weighted-summatory mean square with the same maximizer. The one-point Euler bound, reciprocal-prime upper bound and distance-form source comparison are proved and consumed by the ordinary distance theorem above. These inputs are consumed by the accepted DWWZ-05/06 chain. The proved ordinary full-series route needs no smooth-number adapter. The Gaussian averaging is not DWWZ-10's residue-bearing transform.

## Final semantic acceptance (5 October 2026)

The full TeX statements and public types were compared, not inferred from audit
counts. T1's original sum, both height signs, every input boundary, common
center before all L, open disk and multiplicities match exactly. T2's actual
closed-window hypothesis, strict epsilon, full polynomial cutoff range and
constant order match exactly. Neither theorem accepts an analytic certificate
for its own conclusion.

| Gates | Actual closing consumers/evidence |
|---|---|
| 01,18,19 | One unchanged Lean/Mathlib/PNT graph; 44 root-imported production modules, two verification modules; exhaustive inventory; explicit and transitive audit; sequential foundation and paper BAT receipts. |
| 02,14 | `large_zeta_sum_forces_zero_disk` and `SemanticRegression.exactTheoremOneSourceContract`. |
| 03,04 | `zetaSum_eq_sum_exp`, shifted series, conjugation; `zeroCountIn_eq_sum_multiplicities`, rectangle equality, finite disk/window indices and count transfer. |
| 05,06 | `norm_normalized_mean_comparison_le`, actual mean-value and dilation consumers, `exists_large_sum_maximizing_twist`; the accepted faithful phase specialization, not generic hybrid Halász. |
| 07–11 | `norm_zeta_left_strip_le`, genuine xi/Hadamard and real derivative consumers, `exists_source_zero_repulsion`, `source_gaussian_identity` with positive residue and convergence, `exists_source_zero_sum_upper`. |
| 12,13 | `exists_large_sum_weighted_zero_forcing`, `source_disk_count_of_weighted_forcing`, `exists_source_linked_resolvent_upper`; actual input and linked scales consumed. |
| 15 | `exists_large_x_zeta_sum_bound`: absolute constants, both signs, every real x≥sqrt T, all prefixes and the first-derivative tail. |
| 02,16 | `local_zero_windows_force_zeta_sum_cancellation` and `SemanticRegression.exactTheoremTwoSourceContract`; derives L, inclusion and the strict count contradiction, then consumes the all-large-x bound. |
| 17 | 135 kernel-checked regressions, including exact main contracts, source large-x form, poles, signs, multiplicities, Gaussian normalization and boundaries. No source repair or counterexample was needed. |
| 20 | Current documentation and diagram agree on 20/20; historical receipts and the frozen specification are explicitly distinguished. |

The proof BAT's release mode is a verification label for this internal
formalization, not independent semantic review, a published paper, or a clean
committed release. The tested checkout is deliberately DIRTY; no synchronization
command was run.
