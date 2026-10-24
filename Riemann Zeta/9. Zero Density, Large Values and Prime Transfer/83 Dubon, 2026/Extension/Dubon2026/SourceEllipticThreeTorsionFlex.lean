import Dubon2026.SourceEllipticPointMultiplication

/-! DUB-17/18 -> characteristic-two good models -> faithful inertia.
The exact Deuring coordinate and flex argument is adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_variableChange_eq_deuring_of_isUnit_three.
The actual field and torsion inputs remain for the subsequent consumer. -/
namespace Dubon2026.SourceEllipticDeuring
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
variable {M : Type*} [Field M]

section Flex

variable [DecidableEq M] (E : WeierstrassCurve M)

lemma flex_of_order_three {x₀ y₀ : M} (hP : E.toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    2 * y₀ + E.a₁ * x₀ + E.a₃ ≠ 0 ∧
      ((3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ - E.a₁ * y₀) / (2 * y₀ + E.a₁ * x₀ + E.a₃)) ^ 2 +
        E.a₁ * ((3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ - E.a₁ * y₀) / (2 * y₀ + E.a₁ * x₀ + E.a₃)) -
        E.a₂ = 3 * x₀ := by
  have h3 : Point.some x₀ y₀ hP + Point.some x₀ y₀ hP + Point.some x₀ y₀ hP = 0 := by
    rw [← h3P, show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul]
  have h2P : Point.some x₀ y₀ hP + Point.some x₀ y₀ hP = -Point.some x₀ y₀ hP :=
    eq_neg_of_add_eq_zero_left h3
  have hnegY : E.toAffine.negY x₀ y₀ = -y₀ - E.a₁ * x₀ - E.a₃ := rfl
  have hy : y₀ ≠ E.toAffine.negY x₀ y₀ := by
    intro hy
    have h0 : Point.some x₀ y₀ hP + Point.some x₀ y₀ hP = 0 := Point.add_self_of_Y_eq hy
    rw [h0] at h2P
    exact Point.some_ne_zero _ (neg_eq_zero.mp h2P.symm)
  have hD : y₀ - E.toAffine.negY x₀ y₀ = 2 * y₀ + E.a₁ * x₀ + E.a₃ := by rw [hnegY]; ring
  have hd : 2 * y₀ + E.a₁ * x₀ + E.a₃ ≠ 0 := by rw [← hD]; exact sub_ne_zero.mpr hy
  refine ⟨hd, ?_⟩
  rw [Point.add_self_of_Y_ne hy, Affine.Point.neg_some] at h2P
  have hX := (Point.some.inj h2P).1
  rw [Affine.slope_of_Y_ne rfl hy, hD, Affine.addX] at hX
  have e1 : E.toAffine.a₁ = E.a₁ := rfl
  have e2 : E.toAffine.a₂ = E.a₂ := rfl
  have e4 : E.toAffine.a₄ = E.a₄ := rfl
  rw [e1, e2, e4] at hX
  linear_combination hX

end Flex

end
end Dubon2026.SourceEllipticDeuring
