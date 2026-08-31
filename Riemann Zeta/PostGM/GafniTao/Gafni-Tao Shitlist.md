# Gafni-Tao Shitlist

Status: implementation in progress. This list is the exhaustive completion contract
for the isolated Gafni-Tao program.

An item may be crossed out only when its exact public theorem is kernel-checked,
its immediate source/dependency edge is demonstrated, its axiom audit is clean,
and the isolated warning-failing runner covers its module.

- [ ] **GT-00 — Isolation and source freeze.** Create the separate Lake
  package under `PostGM/GafniTao/Extension`, pin the frozen GM tag/commit and
  exact toolchain, save/hash Gafni-Tao v1 and all source snapshots, and prove
  that no frozen `RiemannZeta/` file is modified.

- [ ] **GT-01 — Exact source crosswalk.** Map Definitions 1.1, `A`, `N*`,
  `A*`, Theorems 1.1-1.3, equations (2.1)-(2.7), Lemmas 2.1-2.4, and the two
  Section 3 sample computations to exact Lean declarations, including every
  endpoint, normalization, quantifier, and constant dependency.

- [ ] **GT-02 — Asymptotic/exponent language.** Implement source-faithful
  `EReal` least/supremum exponents plus usable envelope predicates: fixed-power
  eventual big-O for `mu_delta`, epsilon-power bounds for `A` and `A*`. Prove
  both directions of every interface, empty-supremum behavior, the countable
  `delta` diagonalization, and limiting lemmas. Completion test: no continuity
  of `A` is assumed or smuggled in, and no epsilon loss is inserted into the
  definition of `mu_delta`.

- [ ] **GT-03 — Exceptional set.** Define the exact Mangoldt discrepancy on
  `(x,x+x^theta]`, its subset of `[X,2X]`, Lebesgue measurability, finite
  measure, `mu_delta`, and `mu`. Completion test: the public definition is not
  a sampled/cardinality proxy.

- [ ] **GT-04 — Multiplicity-weighted zero model.** Bridge the frozen
  `zeroCountRect`/`N` to finite zero sums weighted by
  `analyticVanishingOrder`; prove strip, symmetry, monotonicity, and local unit
  count interfaces with exact boundary conventions.

- [ ] **GT-05 — Exact `N*` and `A*`.** Define the four-zero tolerance-one
  additive energy with product multiplicity, prove finiteness and equivalence
  to a multiset count, and define its least exponent. Completion test: no set
  of distinct ordinates and no unrelated `Finset.addEnergy` stands in for
  `N*`.

- [ ] **GT-06 — Chebyshev interval bridge.** Prove the exact equality between
  the real-endpoint von Mangoldt interval sum and a difference of
  `Chebyshev.psi`, including floors, equality endpoints, and prime powers.

- [ ] **GT-07 — Local cover and Brun-Titchmarsh replacement.** Formalize the
  finite cover of `[X,2X]`, `tau=X^(1-theta)`, replacement of `x^theta` by
  `x/tau`, and the uniform `delta/J` loss.

- [x] **GT-08 — Sharp truncated explicit formula.** Prove the paper's exact
  formula at `T=J log(X)^2 tau`, including nontrivial-zero multiplicities,
  sign convention, pole/trivial-zero/boundary terms, and
  `O(x log^2(x)/T)`. Derive equations (2.3)-(2.4) with the real exceptional
  set.

- [ ] **GT-09 — Vinogradov-Korobov zero-free region.** Formalize a published
  theorem strong enough to imply equation (2.6), with low-height cases and
  constants explicit.

- [ ] **GT-10 — Near-one logarithmic zero density.** Formalize
  `N(1-eta,T) <= T^(C eta^(3/2)) log(T)^B` over the exact uniform range.
  Completion test: no `T^epsilon` theorem is substituted.

- [ ] **GT-11 — Lemma 2.1.** Assemble the fundamental-theorem/partial-
  summation estimate, GT-09, and GT-10 into the exact exponential right-edge
  decay, with `eta0` depending only as in the paper.

- [ ] **GT-12 — Lemma 2.2.** Prove the exact `L-infinity` exponent for a strip
  `[sigma_-,sigma_+]`, consuming the actual zero count and physical
  `T,tau,X` relations.

- [x] **GT-13 — Fourier-bump infrastructure.** Construct the fixed
  nonnegative bump, lower bound it on `[0,log 2]`, define its complexified
  Fourier transform, prove uniform tenfold decay, and prove the exact
  `c_rho` bound and expansion.

- [x] **GT-14 — Lemma 2.3.** Prove the normalized `L2` integral estimate via
  GT-13, local zero counts, and `A(sigma_-)`, with all multiplicities and
  `o(1)`/epsilon losses explicit.

- [x] **GT-15 — Smoothed quadruple-to-energy bridge.** Define `F(t)`, prove
  the double-counting identities and Schur estimate, and bound the integral by
  the actual GT-05 `N*` with exact tolerance and constants.

- [x] **GT-16 — Lemma 2.4.** Prove the normalized `L4` integral estimate,
  consuming GT-15 and `A*(sigma_-)` rather than an abstract energy variable.

- [ ] **GT-17 — Equation (2.7).** Prove the exact finite `J` strip
  pigeonhole and its three cases: right edge, small-`A` empty event, and
  `L2`/`L4` Markov alternatives. Account for half-open strip endpoints and the
  absence of zeros on `Re s=1`.

- [ ] **GT-18 — Limit assembly.** Prove the complete exponent ledger and pass
  from the finite estimate `mu+4/J+o(1)` to the epsilon-infimum source
  statement in the correct order, without a continuity hypothesis.

- [ ] **GT-19 — Gafni-Tao Theorem 1.3.** Export the exact refined bound for
  the actual `mu`, `A`, and `A*`. Completion test: unfold the conclusion and
  show the proof term transitively consumes GT-03, GT-08, GT-11, GT-12,
  GT-14, GT-16, GT-17, and GT-18.

- [ ] **GT-20 — Theorems 1.2 and 1.1.** Derive the exact general bound, the
  alternate `max(1-theta,...)` form, and the all/almost-all short-interval
  consequences for a uniform ordinary density exponent.

- [ ] **GT-21 — Native GM consumer.** Instantiate the actual frozen
  `guthMaynardZeroDensity_published_native` at `A0=30/13` and derive the strict
  thresholds `theta>17/30` and `theta>2/15`. A conjoined theorem or repackaged
  GM hypothesis is not completion.

- [ ] **GT-22 — Published exponent inputs.** Formalize the required Pintz
  ordinary-density segment giving the source's `sigma<=23/24` cutoff and the
  Heath-Brown piecewise `A*` bounds with exact ranges, multiplicity, and
  endpoints. If the complete best-known envelope is claimed, also formalize
  every ordinary and additive-energy Tao-Trudgian-Yang segment used by the
  pinned ANTEDB snapshot.

- [ ] **GT-23 — Exact native sample bounds.** Prove
  `mu(17/30)<=7/12` and a fully quantified sufficiently-small-positive-`Delta`
  theorem `mu(2/15+Delta)<=1-9*Delta/13`, consuming GT-19, GT-21, and GT-22.

- [ ] **GT-24 — Section 3 certification.** Pin ANTEDB, reproduce its relevant
  table formulas, and, if publishing the full curve, kernel-check an exact
  piecewise optimizer. Completion test: floats/plots are display only and all
  theorem endpoints are exact.

- [ ] **GT-25 — Integrity and coverage.** Import every production module from
  the isolated root; audit every public/agenda-critical theorem; run focused
  builds, forbidden-token scans, and an isolated principal runner with zero
  errors, warnings, or linter diagnostics. Confirm the frozen GM worktree
  boundary is unchanged.

- [ ] **GT-26 — Documentation and reproduction.** Synchronize this Shitlist,
  architecture, agenda, source hashes, theorem crosswalk, README, exposition,
  audit report, and exact command logs. Update the suggested commit message,
  but do not run `push_to_github.bat` without explicit owner instruction.

## Overall completion test

The program is complete only when GT-00 through GT-26 are all crossed out and
the exact public Theorems 1.1-1.3 plus the two native Section 3 sample bounds
are kernel-checked in the isolated package. Infrastructure, a conditional
wrapper, a numerical plot, a focused build, or one native corollary is not the
whole proof.
