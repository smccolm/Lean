import Dubon2026.SourceEllipticRationalDegree
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic

/-! Integrality over the actual polynomial ring in a rational quotient coordinate.
A monic numerator of larger degree gives a monic relation for the original
coordinate. This replaces a pole-based integrality prerequisite for the odd
quotient field map on the DUB-17/18 dependency chain. -/

open Polynomial

namespace Dubon2026.SourceEllipticFunctionField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- Polynomials over the original field preserve integrality over a subalgebra. -/
theorem isIntegral_aeval_over_subalgebra (A : Subalgebra F L) {x : L}
    (hx : IsIntegral A x) (p : F[X]) : IsIntegral A (aeval x p) := by
  have hi : IsIntegral A (aeval x (p.map (algebraMap F A))) := by
    rw [← mem_integralClosure_iff]
    exact adjoin_le_integralClosure hx (Polynomial.aeval_mem_adjoin_singleton A x)
  simpa only [Polynomial.aeval_map_algebraMap] using hi

/-- A monic numerator of larger degree makes the original coordinate integral over its quotient. -/
theorem isIntegral_coordinate_over_ratio {x : L} {p q : F[X]} (hp : p.Monic)
    (hdeg : q.natDegree < p.natDegree) (hq : aeval x q ≠ 0) :
    IsIntegral (Algebra.adjoin F {aeval x p / aeval x q}) x := by
  let r := aeval x p / aeval x q
  let A := Algebra.adjoin F {r}
  let ar : A := ⟨r, Algebra.subset_adjoin rfl⟩
  have hd : (C ar * q.map (algebraMap F A)).degree < (p.map (algebraMap F A)).degree := by
    refine lt_of_le_of_lt (degree_le_of_natDegree_le
      ((natDegree_C_mul_le _ _).trans natDegree_map_le)) ?_
    rw [degree_eq_natDegree (hp.map _).ne_zero, hp.natDegree_map]
    exact_mod_cast hdeg
  refine ⟨p.map (algebraMap F A) - C ar * q.map (algebraMap F A),
    (hp.map _).sub_of_left hd, ?_⟩
  change aeval x (p.map (algebraMap F A) - C ar * q.map (algebraMap F A)) = 0
  simp only [map_sub, map_mul, aeval_C, Polynomial.aeval_map_algebraMap]
  change aeval x p - (aeval x p / aeval x q) * aeval x q = 0
  rw [div_mul_cancel₀ _ hq, sub_self]

/-- Bézout makes the inverse denominator integral over the actual polynomial quotient ring. -/
theorem isIntegral_inverse_denominator_over_ratio {x : L} {p q : F[X]}
    (hp : p.Monic) (hdeg : q.natDegree < p.natDegree) (hq : aeval x q ≠ 0)
    (hc : IsCoprime p q) :
    IsIntegral (Algebra.adjoin F {aeval x p / aeval x q}) (aeval x q)⁻¹ := by
  let r := aeval x p / aeval x q
  let A := Algebra.adjoin F {r}
  have hx : IsIntegral A x := isIntegral_coordinate_over_ratio hp hdeg hq
  have hr : IsIntegral A r :=
    isIntegral_algebraMap (x := (⟨r, Algebra.subset_adjoin rfl⟩ : A))
  obtain ⟨a, b, hab⟩ := hc
  have hpq : aeval x p = r * aeval x q := (div_mul_cancel₀ _ hq).symm
  have hval : (aeval x a * r + aeval x b) * aeval x q = 1 := by
    have he := congrArg (aeval x) hab
    simp only [map_add, map_mul, map_one] at he
    rw [hpq] at he
    linear_combination he
  have hinv : (aeval x q)⁻¹ = aeval x a * r + aeval x b := by
    apply mul_right_cancel₀ hq
    rw [inv_mul_cancel₀ hq, hval]
  rw [hinv]
  exact ((isIntegral_aeval_over_subalgebra A hx a).mul hr).add
    (isIntegral_aeval_over_subalgebra A hx b)

end Dubon2026.SourceEllipticFunctionField
