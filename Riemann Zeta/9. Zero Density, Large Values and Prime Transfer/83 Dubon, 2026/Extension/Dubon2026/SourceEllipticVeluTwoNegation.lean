import Dubon2026.SourceEllipticVeluTwoKernel

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> continuation -> good
reduction -> reverse genus -> elliptic inertia census -> cyclic-quotient root
interpretation -> actual degree-two quotient group homomorphism.
This step proves negation compatibility and invariance under translation by
the kernel generator. Full additivity, including secant and tangent cases,
remains a required obligation. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
section Field

variable {F : Type*} [Field F] {W : WeierstrassCurve F} {x₀ y₀ : F}

theorem velu2Y_negY (hgy : veluGy W x₀ y₀ = 0) (x y : F) :
    velu2Y W x₀ y₀ x (W.toAffine.negY x y)
      = (veluQuotient2 W x₀ y₀).toAffine.negY (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y) := by
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  by_cases hx : x = x₀
  ·
    subst hx
    simp only [velu2Y, velu2X, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, div_zero, sub_zero, add_zero, WeierstrassCurve.Affine.negY, veluQuotient2_a₁, veluQuotient2_a₃]
  ·
    have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
    simp only [velu2Y, velu2X, WeierstrassCurve.Affine.negY, veluQuotient2_a₁, veluQuotient2_a₃]
    field_simp
    linear_combination veluGx W x₀ y₀ * hord

variable [DecidableEq F]
variable (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0)
  (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0)

omit [DecidableEq F] in

private theorem v2neg_some_congr {W' : WeierstrassCurve.Affine F} {x y₁ y₂ : F}
    {h₁ : W'.Nonsingular x y₁} {h₂ : W'.Nonsingular x y₂} (hy : y₁ = y₂) :
    WeierstrassCurve.Affine.Point.some x y₁ h₁ = WeierstrassCurve.Affine.Point.some x y₂ h₂ := by
  subst hy; rfl

include hQ hgy hΔ in

theorem veluPointMap2_neg (P : W.toAffine.Point) :
    veluPointMap2 hQ hgy hΔ (-P) = -veluPointMap2 hQ hgy hΔ P := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    by_cases hx : x = x₀
    · rw [veluPointMap2_some_of_eq hQ hgy hΔ _ hx,
        veluPointMap2_some_of_eq hQ hgy hΔ h hx]
      rfl
    · rw [veluPointMap2_some_of_ne hQ hgy hΔ _ hx,
        veluPointMap2_some_of_ne hQ hgy hΔ h hx, WeierstrassCurve.Affine.Point.neg_some]
      exact v2neg_some_congr (velu2Y_negY hgy x y)

end Field


end
end Dubon2026.SourceEllipticVelu
