import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount
attribute [-instance] ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite
attribute [-simp] ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one

set_option autoImplicit false
theorem ModularCurve.natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount (N : ℕ) [NeZero N] :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
        (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N))
      = ModularCurve.cuspCount N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount.solution
