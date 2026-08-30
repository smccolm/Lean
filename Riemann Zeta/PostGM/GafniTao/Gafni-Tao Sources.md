# Gafni-Tao source and resource ledger

Research snapshot: 30 August 2026.

This ledger distinguishes mathematical sources, reusable Lean code, and
computational cross-checks. A citation or executable database is not proof
evidence in Lean. Every mathematical dependency must end in a kernel-checked
theorem in the isolated extension.

## Authoritative mathematical source

1. **A. Gafni and T. Tao, _On the number of exceptional intervals to the
   prime number theorem in short intervals_.**
   [arXiv abstract](https://arxiv.org/abs/2505.24017),
   [versioned HTML](https://arxiv.org/html/2505.24017v1),
   [versioned PDF](https://arxiv.org/pdf/2505.24017v1).

   Pin arXiv version `2505.24017v1`. Before implementation begins, save the
   PDF or source archive under `PostGM/GafniTao/Sources/`, record its SHA-256,
   and use that frozen copy for equation and page references. The proof target
   is Theorems 1.1-1.3, with the full Section 2 argument and the two explicit
   sample corollaries in Section 3. The plotted numerical envelope is a
   reproducibility artifact, not a substitute for these theorems.

2. **Tao's expository announcement.**
   [What's new, 2 June 2025](https://terrytao.wordpress.com/2025/06/02/on-the-number-of-exceptional-intervals-to-the-prime-number-theorem-in-short-intervals/).

   This is useful for checking the conceptual interpretation of `mu(theta)`,
   `A(sigma)`, and `A*(sigma)`. The paper remains authoritative when wording or
   notation differs.

## Published inputs cited by the proof

3. **L. Guth and J. Maynard, _New large value estimates for Dirichlet
   polynomials_.** [arXiv:2405.20552v2](https://arxiv.org/abs/2405.20552).

   The frozen repository already exposes the multiplicity-weighted symmetric
   zero count `RiemannZeta.GuthMaynard.N` and the publication-facing theorem
   `guthMaynardZeroDensity_published_native`. The new project must import that
   theorem from the frozen tag; it must not restate its conclusion as a new
   assumption.

4. **D. R. Heath-Brown, _Zero density estimates for the Riemann zeta-function
   and Dirichlet L-functions_, J. London Math. Soc. (2) 19 (1979), 221-232.**
   [DOI](https://doi.org/10.1112/jlms/s2-19.2.221).

   Sections 2-3 are the source behind the second/fourth moment estimates and
   the classical piecewise bounds on `A*`. Exact source statements and endpoint
   conventions must be cross-walked before formalization.

5. **T. Tao, T. Trudgian, and A. Yang, _New exponent pairs, zero density
   estimates, and zero additive energy estimates: a systematic approach_.**
   [arXiv:2501.16779](https://arxiv.org/abs/2501.16779).

   This supplies later piecewise `A*` improvements used in the paper's current
   numerical table. These are optional for the two displayed exact sample
   corollaries but required before claiming the whole best-known numerical
   envelope has been reproduced. The rendered Gafni-Tao v1 bibliography
   currently labels this item with `arXiv:2405.20552`, which is the Guth-
   Maynard identifier; the title/authors resolve to `2501.16779`. Record this
   source-level bibliographic mismatch in the implementation crosswalk rather
   than silently following the wrong identifier.

6. **K. Ford, _Vinogradov's integral and bounds for the Riemann zeta
   function_, Proc. London Math. Soc. 85 (2002), 565-633.**
   [author PDF](https://www.ford126.web.illinois.edu/wwwpapers/zetabd.pdf),
   [DOI](https://doi.org/10.1112/S0024611502013655).

   This is a modern explicit source for the Vinogradov-Korobov zero-free
   region used by Gafni-Tao Lemma 2.1 and for a substantially improved constant
   in the Halasz-Turan near-one estimate. The paper also invokes a near-one density
   bound of the shape
   `N(1-eta,T) <= T^(C eta^(3/2)) log(T)^O(1)`. A generic `T^epsilon` loss is
   explicitly insufficient here, so the existing ordinary GM epsilon-power
   estimate cannot replace this input.

7. **P. Turan, _On a New Method of Analysis and its Applications_, Theorem
   38.2.**

   This is the source explicitly cited by Gafni-Tao for the original
   logarithmic near-one density estimate (with a large absolute constant).
   Ford and later work improve the constant, but the proof only needs a finite
   constant and a sufficiently small `eta0`.

8. **J. Pintz, _Density theorems for Riemann's zeta-function near the line
   Re s = 1_, Acta Arith. 208 (2023), 1-13.**
   [journal page](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/208/1/115159/density-theorems-for-riemann-s-zeta-function-near-the-line-rm-re-s-1),
   [DOI](https://doi.org/10.4064/aa210824-10-5).

   The paper's ordinary-density Table 1 uses Pintz segments near one. In
   particular, the `sigma <= 23/24` restriction invoked in the second sample
   calculation cannot be credited to the uniform GM bound alone.

9. **H. Davenport, _Multiplicative Number Theory_, Chapter 17.**

   Gafni-Tao cite this for the sharp truncated explicit formula. Formalization
   must retain the exact interval `(x, x+x/tau]`, truncation height
   `T = J log(X)^2 tau`, zero multiplicities, endpoint terms, prime powers,
   pole/trivial-zero terms, and the `O(x log^2 x / T)` error.

10. **Bazzanella-Perelli and Bazzanella.** These are historical sources for the
   exceptional-set method. Gafni-Tao identify an incomplete range in the older
   argument. Do not import the disputed bound as a theorem; formalize the
   corrected Gafni-Tao inequalities and range checks.

## Lean repositories and usable APIs

11. **Frozen Riemann Zeta / Guth-Maynard repository.**
   [repository](https://github.com/smccolm/Lean), tag
   `gm-foundation-freeze-v1.0.1`, commit
   `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`.

   Reusable declarations include:

   - `RiemannZeta.GuthMaynard.zeroCountRect` and `N` in
     `RiemannZeta/GuthMaynard/ZeroCount.lean`;
   - `EpsilonPowerBound` in `RiemannZeta/GuthMaynard/Asymptotics.lean`;
   - `guthMaynardZeroDensity_published_native` and the combined density
     theorem in `RiemannZeta/PublicationContract.lean`;
   - local-zero-count, Mellin, contour, Gamma, Fourier, and finite-energy
     infrastructure already audited by the foundation.

   The existing finite approximate-energy helpers are useful combinatorics,
   but they are not definitionally the zeta-zero quantity `N*(sigma,T)`. A new
   multiplicity-preserving bridge is mandatory.

12. **Mathlib 4.** [repository](https://github.com/leanprover-community/mathlib4).

    Frozen foundation revision:
    `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

    Relevant APIs in the pinned foundation include:

    - `Chebyshev.psi`, `psi_eq_sum_Icc`, and von Mangoldt arithmetic in
      `Mathlib/NumberTheory/Chebyshev.lean`;
    - `ArithmeticFunction.vonMangoldt`;
    - Lebesgue measure, measurable sets, interval integrals, Markov/Chebyshev
      inequalities, `EReal`/`ENNReal`, filters, and asymptotics;
    - Fourier transforms, integration by parts, Schwartz/bump functions, and
      convolution;
    - `Finset.addEnergy` in `Mathlib/Combinatorics/Additive/Energy.lean`.

    Repository and documentation searches found no existing Lean
    formalization of the Gafni-Tao theorem, Vinogradov-Korobov zero-free
    region, or the required zeta-zero additive-energy estimate.

13. **PrimeNumberTheoremAnd (PNT+).**
    [repository](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).

    Frozen foundation revision:
    `4ecb950126c4290293c5662dfe0e884123171df5`.

    The frozen dependency contains useful Mellin, zeta, contour, residue, and
    `Chebyshev.psi` infrastructure. Its theorem `MediumPNT` gives only an
    `exp(-c log(x)^(1/10))` error. In the pinned revision the advertised
    `StrongPNT` conclusion remains a blueprint comment rather than a theorem.
    Neither fact supplies the Vinogradov-Korobov/near-one input automatically.
    Import only audited modules without admitted experimental dependencies.

14. **ANTEDB.** [repository](https://github.com/teorth/expdb),
    [generated blueprint](https://teorth.github.io/expdb/blueprint.pdf).

    This is the authoritative computational cross-check for the piecewise
    exponent tables and the numerical optimization in Section 3. It is
    Python/TeX infrastructure, not Lean proof evidence. Pin a commit, export
    exact rational formulas, and prove every bound used in a public Lean
    corollary.

15. **Anthropic Zeta23 / related Lean zeta work.**
    [Zeta23 repository](https://github.com/anthropics/zeta-23-lean).

    Its explicit-formula and zero-multiplicity design may inform interfaces,
    but it uses a different toolchain and theorem package. Reuse requires a
    source/type crosswalk and a pinned compatibility layer; do not copy a
    theorem name or comment as evidence.

## Research verdict

No public Lean repository located in this search already proves Gafni-Tao
Theorem 1.3 or its essential analytic inputs. The shortest faithful route is:

1. reuse the frozen GM zero-count and density theorem;
2. build the exceptional-set and exact explicit-formula layer over Mathlib and
   audited PNT+ infrastructure;
3. formalize the two moment arguments directly from the paper;
4. define and bridge the genuine multiplicity-weighted zero energy `N*`;
5. formalize only the published `A*` segments needed for each claimed native
   numerical corollary, expanding to the full ANTEDB table only when claiming
   the plotted best-known envelope.

The near-one Lemma 2.1 is the highest-risk analytic dependency. It must be
started early, not left as a final “classical” placeholder.
