import Definitions.Def_ModularCurve_ProjectiveLine
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_card_projectiveLine_zmod
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve
theorem ModularCurve.card_projectiveLine_zmod (N : ℕ) (hN : N ≠ 0) : Nat.card (ProjectiveLine (ZMod N)) = dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_card_projectiveLine_zmod.solution
