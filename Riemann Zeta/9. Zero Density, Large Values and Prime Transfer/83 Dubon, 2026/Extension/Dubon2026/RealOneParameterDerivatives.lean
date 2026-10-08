import Dubon2026.RealLiftInfinitesimal

/-! # Genuine one-parameter curves and their iterated right derivatives -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The literal original upper unipotents satisfy their additive group law. -/
theorem realUpperUnipotent_add (s t : ℝ) :
    realUpperUnipotent (s + t) = realUpperUnipotent s * realUpperUnipotent t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realUpperUnipotent, coe_mul, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The actual geodesic matrices satisfy their additive group law. -/
theorem realGeodesicCurve_add (s t : ℝ) :
    realGeodesicCurve (s + t) = realGeodesicCurve s * realGeodesicCurve t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R, coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_exp,
      Real.exp_add, Real.sqrt_mul (Real.exp_nonneg s), mul_comm]

/-- The actual right derivative along a displayed real matrix curve. -/
def realRightDerivative (c : ℝ → SL(2, ℝ)) (Φ : SL(2, ℝ) → ℂ) (g : SL(2, ℝ)) : ℂ :=
  deriv (fun t : ℝ => Φ (g * c t)) 0

/-- For an actual one-parameter subgroup, iterated right differentiation is the literal second derivative of its original orbit. -/
theorem realRightDerivative_twice (c : ℝ → SL(2, ℝ))
    (hc : ∀ s t, c (s + t) = c s * c t) (Φ : SL(2, ℝ) → ℂ) (g : SL(2, ℝ)) :
    realRightDerivative c (realRightDerivative c Φ) g =
      deriv (deriv (fun t : ℝ => Φ (g * c t))) 0 := by
  unfold realRightDerivative
  congr 1
  funext t
  simp_rw [mul_assoc, ← hc]
  simpa [add_comm] using deriv_comp_add_const (fun r : ℝ => Φ (g * c r)) t 0

end
end Dubon2026
