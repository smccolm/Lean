import Dubon2026.SourceEllipticVeluCoefficients

/-! Coordinate identities on the required odd-degree quotient
discriminant chain: actual quotient ellipticity -> odd-prime quotient maps
and products -> cyclic-subgroup root interpretation -> inertia census ->
reverse genus and good reduction -> DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
The native affine addition formulas are retained. Adapted from the selected
odd-order quotient discriminant proof, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
The doubling numerator is supplied separately by the already proved actual
division-polynomial multiplication formula, omitting its duplicate certificate. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F)
omit [DecidableEq F] in
theorem equation_b (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0) {x y : F}
    (h : W.toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  rw [Affine.equation_iff, ha1, ha3] at h
  linear_combination h

theorem chord_prod (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0) {x₁ y₁ x₂ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)
      * W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))
      = ((x₁ * x₂ - W.a₄) ^ 2 - 4 * W.a₆ * (x₁ + x₂ + W.a₂)) / (x₁ - x₂) ^ 2 := by
  have e₁ := equation_b W ha1 ha3 h₁
  have e₂ := equation_b W ha1 ha3 h₂
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx]
  simp only [Affine.addX, Affine.negY, toAffine, ha1, ha3]
  field_simp
  linear_combination (norm := ring_nf)
    (y₁ ^ 2 - 2 * y₂ ^ 2 - 2 * x₂ ^ 3 + 2 * x₁ * x₂ ^ 2 + 2 * x₁ ^ 2 * x₂ - x₁ ^ 3 + W.a₆
        + W.a₄ * x₁ - 2 * W.a₂ * x₂ ^ 2 + 4 * W.a₂ * x₁ * x₂ - W.a₂ * x₁ ^ 2) * e₁
      + (y₂ ^ 2 - x₂ ^ 3 + 2 * x₁ * x₂ ^ 2 + 2 * x₁ ^ 2 * x₂ - 4 * x₁ ^ 3 - W.a₆ + W.a₄ * x₂
        - 2 * W.a₄ * x₁ - W.a₂ * x₂ ^ 2 + 4 * W.a₂ * x₁ * x₂ - 4 * W.a₂ * x₁ ^ 2) * e₂

theorem chord_sum' {x₁ y₁ x₂ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)
      + W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))
      = 2 * x₂ + veluT W x₂ y₂ / (x₁ - x₂) + veluU W x₂ y₂ / (x₁ - x₂) ^ 2 := by
  have e₁ := (Affine.equation_iff (W := W.toAffine) x₁ y₁).mp h₁
  have e₂ := (Affine.equation_iff (W := W.toAffine) x₂ y₂).mp h₂
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx]
  simp only [Affine.addX, Affine.negY, veluT, veluU, veluGx, veluGy, toAffine]
  field_simp
  linear_combination (norm := ring_nf) 2 * e₁ - 2 * e₂


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
