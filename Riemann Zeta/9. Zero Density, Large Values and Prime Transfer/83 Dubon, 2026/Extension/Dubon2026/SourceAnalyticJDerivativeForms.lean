import Dubon2026.SourceModularDerivativeCuspBounds

/-! DUB-17/18 -> numerical modular genus -> elliptic ramification ->
the exact analytic multiplicity of j at each upper-half-plane point.
The required derivative identity follows from native level-one dimension
and discriminant division. This avoids adding a general Ramanujan system
or elliptic-curve uniformization. Full modular orbit separation identifies
the two exceptional fibers with the actual elliptic-point stabilizers.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two.
-/
namespace Dubon2026.SourceFunctionField.JMultiplicity
noncomputable section
open UpperHalfPlane ModularForm Complex SlashInvariantForm Derivative Filter ModularGroup
open scoped MatrixGroups Real Topology ModularForm Manifold Derivative Modular
local notation "Δ" => ModularForm.discriminant
theorem D_jf_mul_Δ_sq :
    (fun z => D jf z * Δ z ^ 2) = D ((E₄ : ℍ → ℂ) ^ 3) * Δ - (E₄ : ℍ → ℂ) ^ 3 * D Δ := by
  have hprod : jf * Δ = (E₄ : ℍ → ℂ) ^ 3 := by
    funext z
    simp only [jf, Pi.mul_apply, Pi.pow_apply]
    exact div_mul_cancel₀ _ (discriminant_ne_zero z)
  have hD := normalizedDerivOfComplex_mul jf Δ mdifferentiable_jf CuspForm.discriminant.holo'
  rw [hprod] at hD
  funext z
  have := congr_fun hD z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] at this ⊢
  rw [this]
  simp only [jf]
  field_simp [discriminant_ne_zero z]
  ring

theorem isZeroAtImInfty_D_jf_mul_Δ_sq : IsZeroAtImInfty (fun z => D jf z * Δ z ^ 2) := by
  rw [D_jf_mul_Δ_sq]
  have hE : MDiff ((E₄ : ℍ → ℂ) ^ 3) := E₄.holo'.pow 3
  have hEb : IsBoundedAtImInfty ((E₄ : ℍ → ℂ) ^ 3) := by
    have h := ModularFormClass.bdd_at_infty E₄
    have h__af := (h.mul h).mul h
    simp [pow_succ] at h__af ⊢
    exact h__af
  have hΔz : IsZeroAtImInfty Δ := CuspFormClass.zero_at_infty CuspForm.discriminant
  have h1 : IsZeroAtImInfty (D ((E₄ : ℍ → ℂ) ^ 3) * Δ) :=
    (isBoundedAtImInfty_D hE hEb).mul_zeroAtFilter hΔz
  have h2 : IsZeroAtImInfty ((E₄ : ℍ → ℂ) ^ 3 * D Δ) :=
    hEb.mul_zeroAtFilter (isZeroAtImInfty_D CuspForm.discriminant.holo' hΔz)
  have h__af := (ZeroAtFilter.add h1 h2.neg : IsZeroAtImInfty _)
  simp at h__af
  exact h__af

theorem D_jf_mul_Δ_sq_slash (γ : SL(2, ℤ)) :
    (fun z => D jf z * Δ z ^ 2) ∣[(26 : ℤ)] γ = fun z => D jf z * Δ z ^ 2 := by
  funext z
  rw [SL_slash_apply, D_smul mdifferentiable_jf jf_smul, Δ_smul]
  have hd : denom (γ : GL (Fin 2) ℝ) z ≠ 0 := denom_ne_zero _ _
  rw [zpow_neg, zpow_ofNat, zpow_ofNat]
  field_simp

/-- The derivative of j multiplied by the square of the discriminant. -/
def h26 : CuspForm 𝒮ℒ 26 where
  toFun z := D jf z * Δ z ^ 2
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact D_jf_mul_Δ_sq_slash γ
  holo' := (normalizedDerivOfComplex_mdifferentiable mdifferentiable_jf).mul
    (CuspForm.discriminant.holo'.pow 2)
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    change IsZeroAtImInfty ((fun z => D jf z * Δ z ^ 2) ∣[(26 : ℤ)] γ)
    rw [D_jf_mul_Δ_sq_slash γ]
    exact isZeroAtImInfty_D_jf_mul_Δ_sq

theorem h26_apply (z : ℍ) : h26 z = D jf z * Δ z ^ 2 := rfl

/-- Divide the actual weight-26 cusp form by the discriminant. -/
def g14 : ModularForm 𝒮ℒ ((14 : ℕ) : ℤ) :=
  (CuspForm.discriminantEquiv h26).mcast (by norm_num)

theorem g14_apply (z : ℍ) : g14 z = D jf z * Δ z := by
  change (CuspForm.discriminantEquiv h26) z = _
  rw [CuspForm.discriminantEquiv_apply, h26_apply, pow_two, ← mul_assoc,
    mul_div_cancel_right₀ _ (discriminant_ne_zero z)]

/-- The nonzero weight-14 modular form E4 squared times E6. -/
def e14 : ModularForm 𝒮ℒ ((14 : ℕ) : ℤ) := ((E₄.mul E₄).mul E₆).mcast (by norm_num)

theorem e14_apply (z : ℍ) : e14 z = E₄ z ^ 2 * E₆ z := by
  change (E₄ z * E₄ z) * E₆ z = _
  rw [pow_two]

theorem finrank_fourteen : Module.finrank ℂ (ModularForm 𝒮ℒ ((14 : ℕ) : ℤ)) = 1 := by
  have h := ModularForm.dimension_level_one 14 (by decide)
  norm_num [Nat.ModEq] at h
  exact Module.finrank_eq_of_rank_eq h


end
end Dubon2026.SourceFunctionField.JMultiplicity
