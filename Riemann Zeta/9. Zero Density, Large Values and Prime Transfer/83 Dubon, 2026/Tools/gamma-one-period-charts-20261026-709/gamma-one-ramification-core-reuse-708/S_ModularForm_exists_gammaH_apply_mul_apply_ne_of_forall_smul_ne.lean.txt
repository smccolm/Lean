import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne
import Theorems.Thm_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq
import P2M.Util
namespace P2MW.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne
attribute [-simp] PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) (τ τ' : UpperHalfPlane)
    (hτ : ∀ γ ∈ CohCarrier.GammaH N H, γ • τ ≠ τ') :
    ∃ (k : ℤ) (g h : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k),
      (g : UpperHalfPlane → ℂ) τ * (h : UpperHalfPlane → ℂ) τ' ≠
        (g : UpperHalfPlane → ℂ) τ' * (h : UpperHalfPlane → ℂ) τ := by
  classical
  by_cases hex : ∃ γ₀ : SL(2, ℤ), γ₀ ∈ CongruenceSubgroup.Gamma0 N ∧ γ₀ • τ = τ'
  · obtain ⟨γ₀, hγ₀, hτ'⟩ := hex
    exact ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq N H τ τ' hτ γ₀ hγ₀ hτ'
  · have h0 : ∀ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ ≠ τ' :=
      fun γ hγ => hex ⟨γ.1, γ.2, hγ⟩
    obtain ⟨k, g, h, hne⟩ := ModularForm.exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne N τ τ' h0
    have hle : ((CohCarrier.GammaH N H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
        ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
      Subgroup.map_mono (CohCarrier.GammaH_le_Gamma0 H)
    refine ⟨k, ModularCurve.restrictForm hle g, ModularCurve.restrictForm hle h, ?_⟩
    rw [ModularCurve.coe_restrictForm, ModularCurve.coe_restrictForm]
    exact hne
