import Dubon2026.SourceEllipticVeluTwoAdditivityCases

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
abbrev KwVeluOrderTwoTangentYAlignAt : Prop :=
  ∀ ⦃x y : F⦄, W.toAffine.Equation x y → y ≠ W.toAffine.negY x y → x ≠ x₀ →
    W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀ →
    velu2Y W x₀ y₀ x y
      ≠ (veluQuotient2 W x₀ y₀).toAffine.negY (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y) →
    velu2Y W x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.addY x x y (W.toAffine.slope x x y y))
      = (veluQuotient2 W x₀ y₀).toAffine.addY
          (velu2X W x₀ y₀ x) (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y)
          ((veluQuotient2 W x₀ y₀).toAffine.slope (velu2X W x₀ y₀ x) (velu2X W x₀ y₀ x)
            (velu2Y W x₀ y₀ x y) (velu2Y W x₀ y₀ x y))

variable {x₀ y₀}
variable [W.IsElliptic]
variable (hgy : veluGy W x₀ y₀ = 0) (hQns : W.toAffine.Nonsingular x₀ y₀)

include hgy hQns in

theorem velu2_tangentCarrier_of_YAlign
    (hYal : KwVeluOrderTwoTangentYAlignAt W x₀ y₀) :
    KwVeluOrderTwoTangentCompatAt W x₀ y₀ := by
  intro x y hP hy hx hx2
  have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W.toAffine)).mp hP
  have hY := velu2Y_ne_quotNegY_of_tangent hgy hQns hns hy hx hx2
  exact ⟨hY, velu2_tanX_align hP hQns.1 hgy hy hx hx2 hY, hYal hP hy hx hx2 hY⟩

include hgy hQns in

theorem velu2_secantCarrier :
    KwVeluOrderTwoSecantCompatDiffAvoidAt W x₀ y₀ := by
  intro x₁ y₁ x₂ y₂ h₁ h₂ hx12 hx₁ hx₂ hsp hsm
  have hns₁ := (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W.toAffine)).mp h₁
  have hns₂ := (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W.toAffine)).mp h₂
  have hX12 := velu2X_ne_of_diffAvoid hgy hQns hns₁ hns₂ hx12 hx₁ hx₂ hsp hsm
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  exact ⟨hX12,
    velu2_secX_align h₁ h₂ hQns.1 hord hx12 hx₁ hx₂ hsp hX12,
    velu2_secY_align h₁ h₂ hQns.1 hgy hx12 hx₁ hx₂ hsp hX12⟩

include hgy hQns in

theorem velu2_addCompatAt_of_YAlign
    (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0)
    (hYal : KwVeluOrderTwoTangentYAlignAt W x₀ y₀) :
    KwVeluOrderTwoAddCompatAt W x₀ y₀ hQns.1 hgy hΔ := by
  exact veluOrderTwoAddCompatAt_of_carriers hQns.1 hgy hΔ
    (velu2_secantCarrier hgy hQns)
    (velu2_tangentCarrier_of_YAlign hgy hQns hYal)

end Field


end
end Dubon2026.SourceEllipticVelu
