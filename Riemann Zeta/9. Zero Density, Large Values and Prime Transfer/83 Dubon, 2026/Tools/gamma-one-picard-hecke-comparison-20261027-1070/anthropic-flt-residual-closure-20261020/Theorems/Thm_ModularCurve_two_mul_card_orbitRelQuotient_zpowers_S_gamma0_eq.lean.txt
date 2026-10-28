import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_two_mul_card_orbitRelQuotient_zpowers_S_gamma0_eq
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false
theorem ModularCurve.two_mul_card_orbitRelQuotient_zpowers_S_gamma0_eq (N : ℕ) [NeZero N] :
    2 * Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.S)
        (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N))
      = ModularCurve.dedekindPsi N + ModularCurve.nuTwo N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_two_mul_card_orbitRelQuotient_zpowers_S_gamma0_eq.solution
