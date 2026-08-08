# Polynomial Power Expansion Proof Notes

This note records the completed implementation of the finite coefficient expansion in `RiemannZeta/GuthMaynard/PolynomialPowers.lean`. It originated as the useful part of the removed `scratch_pow.lean` experiment; the canonical result is now a kernel-checked production theorem.

## Canonical Definitions

- `powPoly N k s T := (detectPoly N s T) ^ k`.
- `powCoeff N k m T` sums products of detector coefficients over functions `p : Fin k → ℕ` whose values lie in `(N, 2N]` and whose product is `m`.

## Proved Expansion

`polynomial_power_identity` proves, for every `N`, `k`, `s`, and `T`,

```lean
powPoly N k s T =
  ∑ m ∈ Finset.Icc (N ^ k) ((2 * N) ^ k),
    powCoeff N k m T * (m : ℂ) ^ (-s)
```

The proof:

1. applies `Finset.sum_pow'` to expand the `k`-th power over tuples indexed by `Fin k`;
2. separates the product of detector coefficients from the product of complex powers;
3. uses `prod_natCast_cpow_eq`, based on `Complex.natCast_mul_natCast_cpow`, to identify the latter with the complex power of the tuple product;
4. uses `powCoeff_product_mem_support` to place every product in `[N^k, (2N)^k]`; and
5. applies `Finset.sum_fiberwise_of_maps_to` to regroup tuples by their natural-number product, producing exactly `powCoeff`.

The support lemma and expansion include `k = 0`: both tuple products are empty products equal to one, and the support interval is `[1,1]`.

## Honest Remaining Boundary

The expansion itself is unconditional and audited. The coefficient-growth theorem remains conditional on the separate classical propositions `DivisorCountBoundProp` and `FactorizationCountBoundProp`. Proving those epsilon-power counting estimates is Goal C work; it is not hidden inside the expansion theorem.
