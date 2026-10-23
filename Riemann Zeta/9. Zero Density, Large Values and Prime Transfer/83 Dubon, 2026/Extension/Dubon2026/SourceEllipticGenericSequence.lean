import Dubon2026.SourceEllipticPolynomialSpecialization

/-! Actual specialization and nonvanishing of generic division
polynomials. Specialization at the integral cusp certifies nonzero generic
denominators without restricting the characteristic of later point
specializations. This serves DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 through
the point multiplication formula, actual torsion count, finite exceptional
fibers, reverse genus and good reduction. Adapted from the Apache-2.0
anthropics/fermats-last-theorem EDSEngine at
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceEllipticUniversal
open WeierstrassCurve Polynomial Dubon2026.SourceEllipticDivision
open Dubon2026.SourceEllipticSequence
open scoped Polynomial.Bivariate
noncomputable section
variable {n : ℤ}

/-- The actual division polynomial evaluated at the generic point. -/
abbrev ψᵤ (n : ℤ) : FunctionField := polyToField (curve.ψ n)

theorem ψᵤ_eq_normEDS :
    ψᵤ = normEDS
      (polyToField curve.ψ₂) (polyToField <| C curve.Ψ₃) (polyToField <| C curve.preΨ₄) := by
  ext; rw [← map_normEDS]; rfl

theorem isEllSequence_ψᵤ : IsEllSequence ψᵤ := by rw [ψᵤ_eq_normEDS]; exact normalized_isEllSequence _ _ _
theorem net_ψᵤ (p q r s) : Dubon2026.SourceEllipticSequence.net ψᵤ p q r s = 0 := by rw [ψᵤ_eq_normEDS]; apply normalized_net

theorem ψᵤ_ne_zero (h0 : n ≠ 0) : ψᵤ n ≠ 0 := fun h ↦ by
  rw [ψᵤ, polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_ψ, map_zero] at h
  exact h0 h

theorem polyToField_φ_ne_zero : polyToField (curve.φ n) ≠ 0 := fun h ↦ by
  rw [polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_φ, map_zero] at h
  exact one_ne_zero h

theorem polyToField_ψ₂Sq : polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2 := by
  rw [← map_pow, ψ_two, ψ₂_sq, map_add, map_mul, polyToField_polynomial, mul_zero, add_zero]


end
end Dubon2026.SourceEllipticUniversal
