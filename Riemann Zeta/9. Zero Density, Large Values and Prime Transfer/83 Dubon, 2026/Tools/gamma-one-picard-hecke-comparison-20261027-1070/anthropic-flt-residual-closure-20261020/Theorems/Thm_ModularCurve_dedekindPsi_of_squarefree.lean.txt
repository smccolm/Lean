import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_dedekindPsi_of_squarefree
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve
theorem ModularCurve.dedekindPsi_of_squarefree {N : ℕ} (hN : Squarefree N) : dedekindPsi N = ∏ p ∈ N.primeFactors, (p + 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_dedekindPsi_of_squarefree.solution
