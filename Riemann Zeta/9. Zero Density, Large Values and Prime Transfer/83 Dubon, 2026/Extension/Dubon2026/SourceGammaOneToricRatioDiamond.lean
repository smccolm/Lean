import Dubon2026.SourceGammaOneToricOriginalRatios
import Dubon2026.SourceIntegralDiamondScalarRatioAction

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> marked-point chart. Apply the existing actual residue diamond
action to the constructed original-field toric ratios. The inverse-action
formula follows from the proved Gamma0 slash action of the literal B and D
forms; no diamond-action or ratio-compatibility certificate is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ToricCoordinates
noncomputable section
open UpperHalfPlane CongruenceSubgroup SourceFricke ModularForm ToricFourier
open IntegralDiamond ReducedDegreeTransport
open scoped MatrixGroups ModularForm
attribute [local instance] originalFieldScalarAlgebra
variable (K : Type*) [Field K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  [Algebra (ZMod ℓ) K] (hℓN : ¬ ℓ ∣ N)

theorem reducedFieldActionOver_β_inv (γ : Gamma0 N) (c : ZMod N) :
    reducedFieldActionOver K N ℓ hℓN γ⁻¹ (β N K c) =
      β N K (c * (γ.val 0 0 : ZMod N)) := by
  apply Subtype.ext
  rw [coe_β]
  refine reducedFieldActionOver_integral_ratio K N ℓ hℓN γ⁻¹
    (show Even (6 : ℤ) by decide) (f6 N c) (E6Γ N)
    (f6 N (c * (γ.val 0 0 : ZMod N))) (E6Γ N)
    (isIntegralQExp_f6 N c) (isIntegralQExp_E6Γ N) ?_
    (isIntegralQExp_f6 N _) (isIntegralQExp_E6Γ N) ?_ ?_ (β N K c) (coe_β N K c)
  · simpa only [red_apply] using intSeriesC_eisenstein6_ne_zero (ZMod ℓ)
  · simpa only [inv_inv] using f6_slash N c γ.val γ.property
  · simp only [inv_inv]
    change (E₆ : ℍ → ℂ) ∣[(6 : ℤ)] γ.val = E₆
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq E₆ _ ⟨γ.val, rfl⟩

theorem reducedFieldActionOver_δ_inv (γ : Gamma0 N) (c : ZMod N) :
    reducedFieldActionOver K N ℓ hℓN γ⁻¹ (δ N K c) =
      δ N K (c * (γ.val 0 0 : ZMod N)) := by
  apply Subtype.ext
  rw [coe_δ]
  refine reducedFieldActionOver_integral_ratio K N ℓ hℓN γ⁻¹
    (show Even (4 : ℤ) by decide) (D N c) (E4Γ N)
    (D N (c * (γ.val 0 0 : ZMod N))) (E4Γ N)
    (isIntegralQExp_D N c) (isIntegralQExp_E4Γ N) ?_
    (isIntegralQExp_D N _) (isIntegralQExp_E4Γ N) ?_ ?_ (δ N K c) (coe_δ N K c)
  · simpa only [red_apply] using intSeriesC_eisenstein4_ne_zero (ZMod ℓ)
  · simpa only [inv_inv] using D_slash N c γ.val γ.property
  · simpa only [inv_inv] using E4Γ_slash N γ.val

theorem reducedFieldActionOver_β (γ : Gamma0 N) (c : ZMod N) :
    reducedFieldActionOver K N ℓ hℓN γ (β N K (c * (γ.val 0 0 : ZMod N))) = β N K c := by
  rw [← reducedFieldActionOver_β_inv K N ℓ hℓN γ c, map_inv]
  exact (reducedFieldActionOver K N ℓ hℓN γ).apply_symm_apply _

theorem reducedFieldActionOver_δ (γ : Gamma0 N) (c : ZMod N) :
    reducedFieldActionOver K N ℓ hℓN γ (δ N K (c * (γ.val 0 0 : ZMod N))) = δ N K c := by
  rw [← reducedFieldActionOver_δ_inv K N ℓ hℓN γ c, map_inv]
  exact (reducedFieldActionOver K N ℓ hℓN γ).apply_symm_apply _

end
end Dubon2026.SourceFunctionField.GammaOne.ToricCoordinates
