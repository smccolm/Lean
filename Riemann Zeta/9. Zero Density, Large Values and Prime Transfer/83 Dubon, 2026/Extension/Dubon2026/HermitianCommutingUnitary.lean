import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.Group

/-! # A Hermitian unitary element from commuting conjugate factors

For the source split-place bridge in DUB-17's unitary auxiliary levels,
a matrix supported at one place commutes with its Hermitian adjoint,
which is supported at the distinct CM-conjugate place. This identity
then makes their quotient genuinely unitary for the specified form.
-/

namespace Dubon2026

/-- Commuting with the Hermitian adjoint makes the quotient by that adjoint preserve the original Hermitian form. -/
theorem hermitian_unitary_of_commute_adjoint
    {G : Type*} [Group G] [StarMul G]
    (h a : G) (hh : star h = h) (hc : Commute a (h⁻¹ * star a * h)) :
    star (a * (h⁻¹ * star a * h)⁻¹) * h * (a * (h⁻¹ * star a * h)⁻¹) = h := by
  let b := h⁻¹ * star a * h
  change Commute a b at hc
  have hb : star b = h * a * h⁻¹ := by
    simp only [b, star_mul, star_inv, hh, star_star]
    group
  change star (a * b⁻¹) * h * (a * b⁻¹) = h
  calc
    _ = h * a⁻¹ * b * a * b⁻¹ := by
      rw [star_mul, star_inv, hb]
      dsimp [b]
      group
    _ = h * a⁻¹ * (b * a) * b⁻¹ := by group
    _ = h := by
      rw [hc.eq.symm]
      group

end Dubon2026
