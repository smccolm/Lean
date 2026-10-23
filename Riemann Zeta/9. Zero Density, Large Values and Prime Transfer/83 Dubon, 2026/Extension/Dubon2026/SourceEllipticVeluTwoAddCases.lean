import Dubon2026.SourceEllipticVeluTwoTangentYRelations

/-! Remaining coordinate and case analysis for the actual degree-two Velu
group homomorphism. The dependency is DUB-17 / DUB-18 -> continuation -> good
reduction -> reverse genus -> elliptic inertia census -> cyclic-quotient root
interpretation -> quotient homomorphisms with their actual cyclic kernels.
Compatibility predicates in intermediate lemmas describe explicit secant and
tangent coordinate obligations; the final consumer must derive them all.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2. All source option
changes and irrelevant logical anchors are omitted. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} (x₀ y₀ : F)

variable (W) in
/-- Explicit coordinate compatibility condition, discharged by the final additivity proof. -/
abbrev KwVeluOrderTwoSecantCompatDiffAvoidAt : Prop :=
  ∀ ⦃x₁ y₁ x₂ y₂ : F⦄, W.toAffine.Equation x₁ y₁ → W.toAffine.Equation x₂ y₂ →
    x₁ ≠ x₂ → x₁ ≠ x₀ → x₂ ≠ x₀ →
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀ →
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) ≠ x₀ →
    velu2X W x₀ y₀ x₁ ≠ velu2X W x₀ y₀ x₂
    ∧ velu2X W x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
        = (veluQuotient2 W x₀ y₀).toAffine.addX (velu2X W x₀ y₀ x₁) (velu2X W x₀ y₀ x₂)
            ((veluQuotient2 W x₀ y₀).toAffine.slope (velu2X W x₀ y₀ x₁) (velu2X W x₀ y₀ x₂)
              (velu2Y W x₀ y₀ x₁ y₁) (velu2Y W x₀ y₀ x₂ y₂))
    ∧ velu2Y W x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
          (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
        = (veluQuotient2 W x₀ y₀).toAffine.addY
            (velu2X W x₀ y₀ x₁) (velu2X W x₀ y₀ x₂) (velu2Y W x₀ y₀ x₁ y₁)
            ((veluQuotient2 W x₀ y₀).toAffine.slope (velu2X W x₀ y₀ x₁) (velu2X W x₀ y₀ x₂)
              (velu2Y W x₀ y₀ x₁ y₁) (velu2Y W x₀ y₀ x₂ y₂))


variable (W) in
/-- Explicit coordinate compatibility condition, discharged by the final additivity proof. -/
abbrev KwVeluOrderTwoTangentCompatAt : Prop :=
  ∀ ⦃x y : F⦄, W.toAffine.Equation x y → y ≠ W.toAffine.negY x y → x ≠ x₀ →
    W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀ →
    velu2Y W x₀ y₀ x y
      ≠ (veluQuotient2 W x₀ y₀).toAffine.negY (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y)
    ∧ velu2X W x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        = (veluQuotient2 W x₀ y₀).toAffine.addX (velu2X W x₀ y₀ x) (velu2X W x₀ y₀ x)
            ((veluQuotient2 W x₀ y₀).toAffine.slope (velu2X W x₀ y₀ x) (velu2X W x₀ y₀ x)
              (velu2Y W x₀ y₀ x y) (velu2Y W x₀ y₀ x y))
    ∧ velu2Y W x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
          (W.toAffine.addY x x y (W.toAffine.slope x x y y))
        = (veluQuotient2 W x₀ y₀).toAffine.addY
            (velu2X W x₀ y₀ x) (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y)
            ((veluQuotient2 W x₀ y₀).toAffine.slope (velu2X W x₀ y₀ x) (velu2X W x₀ y₀ x)
              (velu2Y W x₀ y₀ x y) (velu2Y W x₀ y₀ x y))


variable {x₀ y₀}
variable (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0)
  (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0)

include hQ hgy hΔ in

theorem veluPointMap2_add_of_secant_diffAvoid
    (hsec : KwVeluOrderTwoSecantCompatDiffAvoidAt W x₀ y₀)
    {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hsm : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) ≠ x₀) :
    veluPointMap2 hQ hgy hΔ
        ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)
      = veluPointMap2 hQ hgy hΔ (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)
        + veluPointMap2 hQ hgy hΔ (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) := by
  obtain ⟨hX12, hXeq, hYeq⟩ := hsec h₁.1 h₂.1 hx12 hx₁ hx₂ hsp hsm
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx12, veluPointMap2_some_of_ne hQ hgy hΔ _ hsp,
    veluPointMap2_some_of_ne hQ hgy hΔ h₁ hx₁,
    veluPointMap2_some_of_ne hQ hgy hΔ h₂ hx₂]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hX12]
  simpa only [WeierstrassCurve.Affine.Point.some.injEq] using And.intro hXeq hYeq

include hQ hgy hΔ in

theorem veluPointMap2_add_self_of_tangent
    (htan : KwVeluOrderTwoTangentCompatAt W x₀ y₀)
    {x y : F} (h : W.toAffine.Nonsingular x y) (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀) :
    veluPointMap2 hQ hgy hΔ
        ((WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) + WeierstrassCurve.Affine.Point.some x y h)
      = veluPointMap2 hQ hgy hΔ (WeierstrassCurve.Affine.Point.some x y h)
        + veluPointMap2 hQ hgy hΔ (WeierstrassCurve.Affine.Point.some x y h) := by
  obtain ⟨hY, hXeq, hYeq⟩ := htan h.1 hy hx hx2
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy, veluPointMap2_some_of_ne hQ hgy hΔ _ hx2,
    veluPointMap2_some_of_ne hQ hgy hΔ h hx]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hY]
  simpa only [WeierstrassCurve.Affine.Point.some.injEq] using And.intro hXeq hYeq

end Field


end
end Dubon2026.SourceEllipticVelu
