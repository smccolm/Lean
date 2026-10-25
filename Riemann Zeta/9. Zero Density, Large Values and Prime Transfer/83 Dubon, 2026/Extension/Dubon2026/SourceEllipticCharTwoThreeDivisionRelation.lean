import Dubon2026.SourceEllipticThreeTorsionFlex
import Dubon2026.SourceEllipticTorsionDivisionRoot

/-! DUB-17/18 -> characteristic-two weighted census -> full inertia image.
The exact eighth-power factorization is adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo.
Existing monic integrality, flex and division-polynomial proofs replace repeated
valuation growth and affine doubling calculations. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve WeierstrassCurve.Affine Polynomial IsLocalRing
noncomputable section
variable {M : Type*} [Field M]

theorem psi3_of_order_three [CharP M 2] [DecidableEq M] {t x₀ y₀ : M}
    (hP : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    t * x₀ ≠ 0 ∧ x₀ ^ 4 + t ^ 2 * x₀ ^ 3 + t ^ 7 = 0 ∧
      y₀ ^ 2 + t * x₀ * y₀ = x₀ ^ 3 + t ^ 5 := by
  have h2 : (2 : M) = 0 := CharP.cast_eq_zero M 2
  have htx := (SourceEllipticDeuring.flex_of_order_three _ hP h3P).1
  change 2 * y₀ + t * x₀ + 0 ≠ 0 at htx
  rw [h2, zero_mul, zero_add, add_zero] at htx
  have heq : y₀ ^ 2 + t * x₀ * y₀ = x₀ ^ 3 + t ^ 5 := by
    simpa only [zero_mul, add_zero] using (equation_iff x₀ y₀).mp hP.1
  have hψ := (SourceEllipticDivisionField.nsmul_eq_zero_iff_division_eval _ hP 3).mp h3P
  rw [Nat.cast_ofNat, ΨSq_three, eval_pow, sq_eq_zero_iff] at hψ
  simp only [Ψ₃, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat,
    b₂, b₄, b₆, b₈, zero_mul, mul_zero, add_zero, sub_zero] at hψ
  refine ⟨htx, ?_, heq⟩
  linear_combination hψ + (-x₀ ^ 4 - 6 * t ^ 5 * x₀) * h2

end
end Dubon2026.SourceEllipticCharTwo
