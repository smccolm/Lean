# Prime Shell Source Ledger

Snapshot date: 2026-08-29. Remote commit identifiers were queried directly; mathematical claims below are tied to primary papers or upstream project documentation.

## Pinned Lean repositories

| Resource | Pin / toolchain | Use | Caveat |
|---|---|---|---|
| [Anthropic formal-math / Zeta23](https://github.com/anthropics/formal-math/tree/main/zeta23) | release tag `v1.0`; tag object `82ee6340d6fb15d51fc73ba1ba7b8cac672a7bba`; commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`; Lean `v4.33.0-rc2`; Mathlib `51e6992efd06126df61a496bebf8f49482a4e129` | Exact prime-side trace, Weil-form compression, linear algebra, zero-side assembly, and Comparator contracts | Static artifact; do not work from moving `main` (`2bafb8c88f177284a2123b5fefa2ff84e2365eb6` at snapshot). PairCeiling has no Comparator topic and carries displayed enclosure input. |
| [Lean Comparator](https://github.com/leanprover/comparator) | `master` at `8d84e678dc9954b12db91f7f3167a169b309e0c8` at snapshot | Independent statement-equivalence and permitted-axiom checks | Pin before use; Comparator verifies the supplied statement boundary, not source-theorem semantics by itself. |
| [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | upstream `main` at `47fa48680663df41146704d02a5b092d792bd5b9`; frozen GM project uses older pin `4ecb950126c4290293c5662dfe0e884123171df5` | Zeta, explicit formula, Mellin, PNT and zero-free infrastructure | The Prime Shell arithmetic transfer is not present and must be proved. Do not silently change the frozen project's pin. |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | frozen GM pin `c5ea00351c28e24afc9f0f84379aa41082b1188f`; Zeta23 pin `51e6992efd06126df61a496bebf8f49482a4e129` | Analysis, finite sums, asymptotics, Fourier and linear algebra APIs | The pin mismatch is real; a cross-toolchain bridge or later port requires an explicit decision. |
| [Palomar](https://palomar-registry.org/) | pin the evaluator/template when release work begins | Public challenge/solution packaging | Publication tooling, not mathematical evidence. |

## Primary papers

1. [Alpoge-Furman, *More than two thirds of the zeta zeros are simple and on the critical line*, arXiv:2608.13637v2](https://arxiv.org/html/2608.13637v2). Use Sections 2, 5, 6, and 7. In particular: equation (5.10), Proposition 5.4, Theorem 5.7, and the explicit statement in Section 7.2 that `X >> T` requires prime-pair information.
2. [Guth-Maynard, *New large value estimates for Dirichlet polynomials*, arXiv:2405.20552v2](https://arxiv.org/html/2405.20552v2). Use Corollary 1.4 and its proof in Section 13.2. The proof ledger must include the near-one logarithmic density input, Vinogradov-Korobov zero-free region, explicit formula, and mean-square step.
3. [Matomaki-Radziwill-Tao, *Correlations of the von Mangoldt and higher divisor functions I. Long shift ranges*, arXiv:1707.01315](https://arxiv.org/html/1707.01315). Theorem 1.3(i) supplies the fallback almost-all shifted von Mangoldt asymptotic for `H >= X^(8/33+epsilon)`.
4. [Montgomery, *The pair correlation of zeros of the zeta function* (1973)](https://doi.org/10.1090/pspum/024/9944). Foundational equivalence between extended support and prime-pair information; source context, not a first formalization target.
5. [Goldston-Montgomery, *Pair correlation of zeros and primes in short intervals* (1987)](https://www.impan.pl/shop/en/publication/transaction/download/product/83512). Source context for the prime-pair/zero-pair equivalence and scale interpretation.
6. [Baluyot-Goldston-Suriajaya-Turnage-Butterbaugh, *An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta-function*](https://doi.org/10.4064/aa230612-20-3), Acta Arithmetica 214 (2024). Relevant to the existing support-one input cited by Alpoge-Furman; it does not supply the proposed Prime Shell input.

## Exact upstream code areas to inspect

- `Zeta23/PrimeSideA/`
- `Zeta23/PrimeSideB/`
- `Zeta23/Poisson.lean`
- `Zeta23/Taper/`
- `Zeta23/LinAlg/`
- `Zeta23/Assembly/`
- `Zeta23/PairCeiling/`
- `Challenge.lean`, `Solution.lean`, and Comparator configurations

The paper's labels in Zeta23 docstrings are intended as a source crosswalk. The next goal must replace this directory-level list with exact declaration names and theorem types.

## Research findings that constrain the plan

- Zeta23's current prime-side theorem uses a Dirichlet polynomial of length at most `T`; the paper itself says the off-diagonal becomes a prime-pair problem beyond that point.
- GM Corollary 1.4 is an almost-all interval theorem. It naturally yields cumulative information in the shift variable after a nontrivial `pi`-to-`psi` transfer; it does not directly give a fixed-shift singular-series asymptotic.
- MRT gives almost-all fixed-shift asymptotics, but only at the farther `8/33` shift threshold.
- The candidate support thresholds `15/13` and `33/25` are algebraic overlap points with the resonant scale, not proved trace ranges.
- The `0.6818287` PairCeiling value depends on a displayed `EnclOK` enclosure input whose external certificate reproduction is not part of the release Comparator. It must not be described as an internally discharged unconditional ceiling.
