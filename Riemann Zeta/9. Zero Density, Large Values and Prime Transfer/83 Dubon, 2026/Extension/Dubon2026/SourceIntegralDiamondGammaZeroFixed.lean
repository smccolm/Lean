import Dubon2026.SourceIntegralDiamondFieldAction
import Dubon2026.SourceIntegralDiamondFullBaseInclusion

/-! DUB-17/18 -> original Gamma1 degree/genus -> signed-index lower bound.
The actual diamond pullback fixes every original Gamma0 integral ratio:
native even-weight replacement and restriction give invariant forms.
Native adjoin homomorphism extensionality then proves fixation of the
entire original Gamma0 field, without a second fixed-field construction. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne IntermediateField
open scoped MatrixGroups ModularForm

theorem reducedFieldPull_of_gammaZero_ratio (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (δ : Gamma0 N) (x : qExpFunctionFieldC (ZMod ℓ) (Gamma1 N))
    (hx : (x : LaurentSeries (ZMod ℓ)) ∈ intFormRatiosC (ZMod ℓ) (Gamma0 N)) :
    reducedFieldPull N ℓ δ x = (x : LaurentSeries (ZMod ℓ)) := by
  have hT : ModularGroup.T ∈ Gamma0 N := by simp [Gamma0_mem, ModularGroup.T]
  obtain ⟨k, hk, f, g, pf, pg, hf, hg, hg0, hrep⟩ := exists_even_integral_ratio hT hx
  let f' : ModularForm (Gamma1 N) k :=
    ModularNormPolynomial.restrict (Subgroup.map_mono (Gamma1_in_Gamma0 N)) f
  let g' : ModularForm (Gamma1 N) k :=
    ModularNormPolynomial.restrict (Subgroup.map_mono (Gamma1_in_Gamma0 N)) g
  have hfi : (⇑f' : ℍ → ℂ) ∣[k] δ.val = f' := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ δ.property)
  have hgi : (⇑g' : ℍ → ℂ) ∣[k] δ.val = g' := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ δ.property)
  simp only [← red_apply] at hg0 hrep
  rw [reducedFieldPull_eq N ℓ hℓN δ x hk f' g' hf hg hg0 hrep,
    reducedDiamond_of_invariant N ℓ hℓN hk δ f' hf hfi,
    reducedDiamond_of_invariant N ℓ hℓN hk δ g' hg hgi, hrep]

theorem reducedFieldEquiv_fixes_gammaZeroField (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (δ : Gamma0 N) (x : qExpFunctionFieldC (ZMod ℓ) (Gamma1 N))
    (hx : (x : LaurentSeries (ZMod ℓ)) ∈ qExpFunctionFieldC (ZMod ℓ) (Gamma0 N)) :
    reducedFieldEquiv N ℓ hℓN δ x = x := by
  let ι := IntermediateField.inclusion (qExpFunctionFieldC_mono (ZMod ℓ) (Gamma1_in_Gamma0 N))
  have he : (reducedFieldEquiv N ℓ hℓN δ).toAlgHom.comp ι = ι := by
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    apply Subtype.ext
    exact reducedFieldPull_of_gammaZero_ratio N ℓ hℓN δ (ι ⟨y, subset_adjoin _ _ hy⟩) hy
  exact congrArg (fun φ => φ ⟨(x : LaurentSeries (ZMod ℓ)), hx⟩) he

theorem reducedFieldAction_fixes_fullBase (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (γ : Gamma0 N) (x : qExpFunctionFieldC (ZMod ℓ) (Gamma1 N))
    (hx : (x : LaurentSeries (ZMod ℓ)) ∈ modularFunctionFieldCoeff N (ZMod ℓ)) :
    reducedFieldAction N ℓ hℓN γ x = x :=
  reducedFieldEquiv_fixes_gammaZeroField N ℓ hℓN γ⁻¹ x (fullBase_le_gammaZeroField _ N hx)

theorem fullBase_le_originalReducedField (N ℓ : ℕ) [Fact ℓ.Prime] :
    modularFunctionFieldCoeff N (ZMod ℓ) ≤ qExpFunctionFieldC (ZMod ℓ) (Gamma1 N) :=
  (fullBase_le_gammaZeroField _ N).trans (qExpFunctionFieldC_mono _ (Gamma1_in_Gamma0 N))

end
end Dubon2026.SourceFunctionField.IntegralDiamond
