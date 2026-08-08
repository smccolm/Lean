# Polynomial Power Expansion Notes

This note preserves the useful part of the removed `scratch_pow.lean` experiment. It records a future proof obligation and does not claim that the expansion is proved.

## Canonical Definitions

`RiemannZeta/GuthMaynard/PolynomialPowers.lean` defines:

- `powPoly N k s T := (detectPoly N s T) ^ k`; and
- `powCoeff N k m T` as the sum of products of detector coefficients over functions `p : Fin k → ℕ` whose values lie in `(N, 2N]` and whose product is `m`.

The removed scratch file introduced `powCoeff_alt` with exactly the same expression and proved only the definitional identity `powCoeff_alt = powCoeff` by reflexivity. It also proposed the explicit finite sum

```lean
∑ m ∈ Finset.Icc (N ^ k) ((2 * N) ^ k),
  powCoeff N k m T * (m : ℂ) ^ (-s)
```

as the desired coefficient expansion of `powPoly`.

## Required Theorem

The substantive missing result is an equality of the following form:

```lean
powPoly N k s T =
  ∑ m ∈ Finset.Icc (N ^ k) ((2 * N) ^ k),
    powCoeff N k m T * (m : ℂ) ^ (-s)
```

The proof must expand the finite power, regroup tuples by their product, justify the support interval, and reconcile the complex-power product with the product of the individual terms. Boundary cases, especially `k = 0`, must be checked explicitly. The existing `polynomial_power_identity` proves only the definitional structural identity `powPoly = detectPoly ^ k`; it does not prove this coefficient expansion.

## Likely Lean Route

1. Express the `k`-th power of the finite detector sum as a sum over `Fin k → ℕ`.
2. Restrict every coordinate to `Finset.Ioc N (2 * N)`.
3. Regroup the tuple sum by `m = ∏ i, p i` using a finite fiber decomposition.
4. Prove that every product lies in `Finset.Icc (N ^ k) ((2 * N) ^ k)` under the necessary hypotheses on `N` and `k`.
5. identify each fiber sum with `powCoeff N k m T`.
6. prove the required complex-power multiplicativity for the positive natural factors.

This obligation remains part of Shitlist #10 and is a prerequisite for the F-07 polynomial-power step in Shitlist #14.
