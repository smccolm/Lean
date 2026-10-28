import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import P2M.Util
import P2M.Sol.S_ModularCurve_finrankAlong_frobeniusModL
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve AlgebraicCurve
theorem ModularCurve.finrankAlong_frobeniusModL (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ}
    [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N] :
    AlgebraicCurve.finrankAlong K (ModularCurve.frobeniusModL K N ℓ) = ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrankAlong_frobeniusModL.solution
