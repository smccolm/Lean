import Dubon2026.SourceRationalPrincipalDivisor
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> original Frobenius/inertia -> residue principal divisors ->
rational-function base of Galois descent. Over closed constants, native
polynomial factorization into actual linear factors and the proved divisor
product law give degree zero. This avoids classifying all rational places. -/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial

theorem rational_polynomial_linear_nonzero (K : Type*) [Field K] (c : K) :
    algebraMap K[X] (RatFunc K) (X - C c) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero c)

theorem rational_polynomial_linear_value (K : Type*) [Field K] (c : K) :
    algebraMap K[X] (RatFunc K) (X - C c) = RatFunc.X - algebraMap K (RatFunc K) c := by
  rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rfl

theorem degree_rationalPrincipalDivisor_linear_product (K : Type*) [Field K] (s : Multiset K) :
    algebraMap K[X] (RatFunc K) ((s.map fun c => X - C c).prod) ≠ 0 ∧
      Divisor.degree (rationalPrincipalDivisor K
        (algebraMap K[X] (RatFunc K) ((s.map fun c => X - C c).prod))) = 0 := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, map_one]
    refine ⟨one_ne_zero, ?_⟩
    have h := rationalPrincipalDivisor_const K 1
    rw [map_one] at h
    rw [h, map_zero]
  | cons c s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul]
    have hc := rational_polynomial_linear_nonzero K c
    refine ⟨mul_ne_zero hc ih.1, ?_⟩
    rw [rationalPrincipalDivisor_mul K hc ih.1, map_add, ih.2,
      rational_polynomial_linear_value, degree_rationalPrincipalDivisor_linear, zero_add]

theorem degree_rationalPrincipalDivisor_polynomial (K : Type*) [Field K] [IsAlgClosed K]
    (p : K[X]) : Divisor.degree (rationalPrincipalDivisor K (algebraMap K[X] (RatFunc K) p)) = 0 := by
  by_cases hp : p = 0
  · subst p
    rw [map_zero]
    have h := rationalPrincipalDivisor_const K 0
    rw [map_zero] at h
    rw [h, map_zero]
  have hc : algebraMap K[X] (RatFunc K) (C p.leadingCoeff) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp))
  have hs := degree_rationalPrincipalDivisor_linear_product K p.roots
  conv in algebraMap K[X] (RatFunc K) p => rw [(IsAlgClosed.splits p).eq_prod_roots]
  rw [map_mul, rationalPrincipalDivisor_mul K hc hs.1, map_add, hs.2,
    RatFunc.algebraMap_C]
  change Divisor.degree (rationalPrincipalDivisor K (algebraMap K (RatFunc K) p.leadingCoeff)) + 0 = 0
  rw [rationalPrincipalDivisor_const, map_zero, zero_add]

end
end Dubon2026.SourceCurve
