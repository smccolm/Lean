import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt
import P2M.Util
namespace P2MW.S_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem solution (N : ℕ) [NeZero N] (hP : ∀ (M : ℕ) [NeZero M], HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) (hex : ∀ (ℓ ℓ' M : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] [NeZero M] (hM : M = N * ℓ * ℓ'), ℓ ≠ ℓ' → HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ ℓ' M hM) : HeckeOperatorsCommuteBar N := by
  rintro ⟨ℓ, hℓ⟩ ⟨ℓ', hℓ'⟩
  by_cases hne : ℓ = ℓ'
  · subst hne; rfl
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact ℓ'.Prime := ⟨hℓ'⟩
  haveI := hP (N * ℓ)
  haveI := hP (N * ℓ')
  haveI := hP (N * ℓ * ℓ')
  exact ModularCurve.heckeOperatorBar_comm_of_heckeExchangeAt N ℓ ℓ' (N * ℓ * ℓ') rfl (by ring)
    (hex ℓ ℓ' _ rfl hne) (hex ℓ' ℓ (N * ℓ * ℓ') (by ring) (Ne.symm hne))
