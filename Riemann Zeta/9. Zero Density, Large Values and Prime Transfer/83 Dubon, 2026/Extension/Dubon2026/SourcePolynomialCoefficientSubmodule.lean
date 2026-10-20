/-
Copyright 2026 Reuven Hodges
Licensed under the Apache License, Version 2.0; see the archived RS-LICENSE.txt.

Modified for Project 83 from rhodges-math/rs-counterexample at
8fb1989aa7342e9e1db97f25dd8f5eda9c6353c6, GLRep/Borel/BorelStabilityDifferential.lean.
Only coefficient extraction is retained and checked against pinned Mathlib.
The external polynomial-representation framework is not imported.
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Polynomial.Roots

/-! Coefficient extraction for the actual source finite exponential.
This recovers the source differential from the original elementary group
orbits and will identify actual group-invariant subspaces as Lie submodules.
-/

namespace Dubon2026
noncomputable section
open Module Polynomial
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- **Coefficient extraction**: if `Σ_k t^k v_k ∈ U` for every `t` in an infinite field, every
`v_k` lies in `U`. -/
theorem sourcePolynomial_coeff_mem_of_values_mem [Infinite K] (U : Submodule K W) {N : ℕ} (v : ℕ → W)
    (h : ∀ t : K, ∑ k ∈ Finset.range N, t ^ k • v k ∈ U) {k : ℕ} (hk : k < N) : v k ∈ U := by
  rw [← Submodule.Quotient.mk_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff K _).mp fun f => ?_
  let q : K[X] := ∑ j ∈ Finset.range N, monomial j (f (U.mkQ (v j)))
  have hq : q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot q (Set.infinite_univ.mono fun t _ => ?_)
    have h0 : f (U.mkQ (∑ j ∈ Finset.range N, t ^ j • v j)) = 0 := by
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr (h t), map_zero]
    rw [map_sum, map_sum] at h0
    simp only [map_smul, smul_eq_mul] at h0
    simp only [IsRoot, q, eval_finsetSum, eval_monomial]
    rw [← h0]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h1 := congrArg (coeff · k) hq
  simp only [q, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', Finset.mem_range, hk,
    ite_true, coeff_zero] at h1
  exact h1

end
end Dubon2026
