import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant
import Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_qParam
import Theorems.Thm_ModularCurve_hasSum_smul_modularUnitSeries_inv_qParam
import Theorems.Thm_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant
import P2M.Util
namespace P2MW.S_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

set_option autoImplicit false

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hmem : ModularCurve.modularUnitSeries ℓ ∈ ModularCurve.modularFunctionFieldFull ℓ) : ((ModularCurve.frickeInvolutionFull ℓ ⟨ModularCurve.modularUnitSeries ℓ, hmem⟩ : ModularCurve.modularFunctionFieldFull ℓ) : LaurentSeries ℚ) = (ℓ : ℚ) ^ 12 • (ModularCurve.modularUnitSeries ℓ)⁻¹ := by
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  exact ModularCurve.coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant ℓ
    (ModularCurve.modularUnitSeries ℓ) ((ℓ : ℚ) ^ 12 • (ModularCurve.modularUnitSeries ℓ)⁻¹)
    (fun τ => ModularForm.discriminant τ
      / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))
    (fun τ => ModularCurve.hasSum_modularUnitSeries_qParam ℓ τ)
    (fun τ => ModularCurve.hasSum_smul_modularUnitSeries_inv_qParam ℓ τ)
    (fun γ hγ τ => ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul ℓ γ hγ τ) hmem
