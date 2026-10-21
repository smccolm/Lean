import Dubon2026.SourceCurveDivisors

/-! DUB-17/18 -> function-field Riemann--Roch -> local quotient dimensions.
The literal finite residue-weighted degree is additive and nonnegative
on effective divisors; a single place contributes its actual residue degree.
-/
namespace Dubon2026.SourceCurve.Divisor
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum_support (D : Divisor K F) :
    degree D = ∑ v ∈ D.support, D v * (Module.finrank K v.ResidueField : ℤ) := by
  rw [degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  rfl

theorem degree_nonneg_of_nonneg {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) :
    0 ≤ degree D := by
  rw [degree_eq_sum_support]
  exact Finset.sum_nonneg fun v _ => mul_nonneg (hD v) (Int.natCast_nonneg _)

theorem degree_single (v : Place K F) (n : ℤ) :
    degree (Finsupp.single v n) = n * (Module.finrank K v.ResidueField : ℤ) := by
  simp [degree]

end
end Dubon2026.SourceCurve.Divisor
