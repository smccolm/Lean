import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve AlgebraicCurve
theorem ModularCurve.heckeOperatorsCommuteBar_of_heckeExchangeAt (N : ℕ) [NeZero N] (hP : ∀ (M : ℕ) [NeZero M], HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) (hex : ∀ (ℓ ℓ' M : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] [NeZero M] (hM : M = N * ℓ * ℓ'), ℓ ≠ ℓ' → HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ ℓ' M hM) : HeckeOperatorsCommuteBar N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.solution
