import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
import P2M.Util
namespace P2MW.S_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve

theorem solution (K : Type*) [Field K]
    (ℓ : ℕ) [CharP K ℓ] (N : ℕ) [NeZero N] (hlN : ¬ ℓ ∣ N) :
    modularFunctionFieldC K N = modularFunctionFieldFullC K N := by
  rcases eq_or_ne ℓ 0 with hℓ | hℓ
  ·
    subst hℓ
    haveI : CharZero K := CharP.charP_to_charZero K
    exact modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero K N
  ·
    haveI : NeZero ℓ := ⟨hℓ⟩
    exact modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos K ℓ N hlN
