import Dubon2026.SourceGammaOneRatioClosure
import Mathlib.NumberTheory.ModularForms.Discriminant

/-! DUB-17/18 -> actual Gamma1 differential comparison -> cusp integral
bound. Construct the genuine modular form f^(2M) E4^3 / Delta. Normality
of the principal congruence subgroup supplies period M at every cusp;
native cusp exponential decay and discriminant growth prove boundedness.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_of_mul_thetaL_eq_qExpansion_of_gamma_le. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CuspAuxiliary
noncomputable section
open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Pointwise Manifold
local notation "Δ" => ModularForm.discriminant


open Matrix.SpecialLinearGroup CongruenceSubgroup

variable (M : ℕ) {Γ : Subgroup SL(2, ℤ)} (hΓ : Gamma M ≤ Γ)

include hΓ in

theorem conj_T_pow_mem (γ : SL(2, ℤ)) :
    γ * ModularGroup.T ^ (M : ℤ) * γ⁻¹ ∈ Γ := by
  have hT : ModularGroup.T ^ (M : ℤ) ∈ Gamma M := by
    simpa using ModularGroup_T_pow_mem_Gamma (M : ℤ) (M : ℤ) dvd_rfl
  exact hΓ ((Gamma_normal M).conj_mem _ hT γ)

theorem mapGL_T_zpow (m : ℤ) :
    (mapGL ℝ (ModularGroup.T ^ m) : GL (Fin 2) ℝ) = Matrix.GeneralLinearGroup.upperRightHom (m : ℝ) := by
  rw [Units.ext_iff, mapGL_coe_matrix, map_apply_coe, ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

include hΓ in
theorem natCast_mem_strictPeriods_conj (γ : SL(2, ℤ)) :
    (M : ℝ) ∈ (ConjAct.toConjAct (γ : GL (Fin 2) ℝ)⁻¹ •
      (Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  refine ⟨γ * ModularGroup.T ^ (M : ℤ) * γ⁻¹, conj_T_pow_mem M hΓ γ, ?_⟩
  rw [map_mul, map_mul, map_inv, mapGL_T_zpow, Int.cast_natCast]
  rfl

theorem pow_slash (k : ℤ) (γ : SL(2, ℤ)) (F : ℍ → ℂ) :
    ∀ m : ℕ, (F ^ m) ∣[(m : ℤ) * k] γ = (F ∣[k] γ) ^ m
  | 0 => by simpa using ModularForm.is_invariant_one γ
  | m + 1 => by
    have h : ((m + 1 : ℕ) : ℤ) * k = (m : ℤ) * k + k := by push_cast; ring
    rw [h, pow_succ, ModularForm.mul_slash_SL2, pow_slash k γ F m, pow_succ]

theorem num_slash (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) (γ : SL(2, ℤ)) :
    (fun τ ↦ f τ ^ (2 * M) * E₄ τ ^ 3) ∣[((2 * M : ℕ) : ℤ) * 2 + ((3 : ℕ) : ℤ) * 4] γ =
      fun τ ↦ ((f : ℍ → ℂ) ∣[(2 : ℤ)] γ) τ ^ (2 * M) * E₄ τ ^ 3 := by
  have h1 : (fun τ ↦ f τ ^ (2 * M) * E₄ τ ^ 3) = (⇑f) ^ (2 * M) * (⇑E₄) ^ 3 := rfl
  rw [h1, ModularForm.mul_slash_SL2, pow_slash, pow_slash]
  have hE : (⇑E₄) ∣[(4 : ℤ)] γ = ⇑E₄ := by
    have := SlashInvariantForm.slash_action_eqn E₄ (γ : GL (Fin 2) ℝ) ⟨γ, rfl⟩
    simpa [ModularForm.SL_slash] using this
  rw [hE]
  rfl

variable [NeZero M] [Γ.FiniteIndex]

include hΓ in

/-- The actual cusp numerator divided by the nonvanishing discriminant. -/
def Gform (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) :
    ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (((2 * M : ℕ) : ℤ) * 2 + ((3 : ℕ) : ℤ) * 4 - 12) where
  toFun τ := f τ ^ (2 * M) * E₄ τ ^ 3 / Δ τ
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    change ((fun τ ↦ f τ ^ (2 * M) * E₄ τ ^ 3) / Δ) ∣[_] (γ : GL (Fin 2) ℝ) = _
    rw [← ModularForm.SL_slash, ModularForm.div_slash_SL2, num_slash]
    have hΔ : (Δ : ℍ → ℂ) ∣[(12 : ℤ)] γ = Δ := by
      have := SlashInvariantForm.slash_action_eqn CuspForm.discriminant (γ : GL (Fin 2) ℝ) ⟨γ, rfl⟩
      simpa [ModularForm.SL_slash] using this
    have hf : (⇑f) ∣[(2 : ℤ)] γ = ⇑f := by
      have := SlashInvariantForm.slash_action_eqn f (γ : GL (Fin 2) ℝ) ⟨γ, hγ, rfl⟩
      simpa [ModularForm.SL_slash] using this
    rw [hΔ, hf]
    rfl
  holo' := by
    have h1 : MDiff (fun τ : ℍ ↦ f τ ^ (2 * M) * E₄ τ ^ 3) :=
      (f.holo'.pow _).mul (E₄.holo'.pow _)
    exact h1.div CuspForm.discriminant.holo' discriminant_ne_zero
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    change IsBoundedAtImInfty (((fun τ ↦ f τ ^ (2 * M) * E₄ τ ^ 3) / Δ) ∣[_] γ)
    rw [ModularForm.div_slash_SL2, num_slash]
    have hΔ : (Δ : ℍ → ℂ) ∣[(12 : ℤ)] γ = Δ := by
      have := SlashInvariantForm.slash_action_eqn CuspForm.discriminant (γ : GL (Fin 2) ℝ) ⟨γ, rfl⟩
      simpa [ModularForm.SL_slash] using this
    rw [hΔ, IsBoundedAtImInfty, Filter.BoundedAtFilter]
    refine (Asymptotics.div_isBoundedUnder_of_isBigO ?_).isBigO_one ℝ

    have hN : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
    have hF := CuspFormClass.exp_decay_atImInfty (CuspForm.translate f (γ : GL (Fin 2) ℝ)) hN
      (natCast_mem_strictPeriods_conj M hΓ γ)
    have hF' : (fun τ ↦ ((f : ℍ → ℂ) ∣[(2 : ℤ)] γ) τ ^ (2 * M)) =O[atImInfty]
        fun τ ↦ Real.exp (-2 * Real.pi * τ.im / M) ^ (2 * M) := by
      have := hF.pow (2 * M)
      simpa [CuspForm.coe_translate, ModularForm.SL_slash] using this
    have hE0 : (⇑E₄) =O[atImInfty] (1 : ℍ → ℝ) := ModularFormClass.bdd_at_infty E₄
    have hE : (fun τ ↦ E₄ τ ^ 3) =O[atImInfty] fun _ : ℍ ↦ (1 : ℝ) := by
      have := hE0.pow 3
      simp only [Pi.one_apply, one_pow] at this
      exact this
    have h3 := hF'.mul hE
    refine h3.trans ?_
    refine Asymptotics.IsBigO.trans ?_ exp_isBigO_discriminant
    simp only [mul_one]
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with τ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hτ : 0 ≤ τ.im := τ.im_pos.le
    have : ((2 * M : ℕ) : ℝ) * (-2 * Real.pi * τ.im / M) = - 2 * (2 * Real.pi * τ.im) := by
      have hN' : (M : ℝ) ≠ 0 := hN.ne'
      field_simp
      push_cast
      ring
    rw [this]
    nlinarith [Real.pi_pos]


end
end Dubon2026.SourceFunctionField.GammaOne.CuspAuxiliary
