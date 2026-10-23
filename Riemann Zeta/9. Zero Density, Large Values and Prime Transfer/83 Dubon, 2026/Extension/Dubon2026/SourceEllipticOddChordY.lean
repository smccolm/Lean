import Dubon2026.SourceEllipticOddChordIdentities

/-! The actual paired chord y-coordinate equals the literal Velu correction.
This algebraic identity is the required bridge from subgroup translation sums
to the explicit odd quotient y-coordinate. The existing native addition formulas
and both actual Weierstrass equations supply its proof in every characteristic. -/

namespace Dubon2026.SourceEllipticVelu.OddDiscriminant

open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- Pairing the translations by Q and -Q yields the literal y-correction term. -/
theorem chord_y_sum {x₁ y₁ x₂ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) +
      W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) =
    -W.a₁ * x₂ - W.a₃ -
      (veluU W x₂ y₂ * (2 * y₁ + W.a₁ * x₁ + W.a₃) / (x₁ - x₂) ^ 3 +
       veluT W x₂ y₂ * (W.a₁ * (x₁ - x₂) + y₁ - y₂) / (x₁ - x₂) ^ 2 +
       (W.a₁ * veluU W x₂ y₂ - veluGx W x₂ y₂ * veluGy W x₂ y₂) / (x₁ - x₂) ^ 2) := by
  have e₁ := (Affine.equation_iff (W := W.toAffine) x₁ y₁).mp h₁
  have e₂ := (Affine.equation_iff (W := W.toAffine) x₂ y₂).mp h₂
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx]
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY,
    veluT, veluU, veluGx, veluGy, toAffine]
  field_simp
  linear_combination (norm := ring_nf)
    (-2 * y₁ - 2 * x₁ * W.a₁ + x₂ * W.a₁ - W.a₃) * e₁ +
    (2 * y₁ + 2 * x₁ * W.a₁ - x₂ * W.a₁ + W.a₃) * e₂

end Dubon2026.SourceEllipticVelu.OddDiscriminant
