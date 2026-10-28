import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_natCard_fixedPoints_S_cosets_Gamma0_eq_nuTwo

open scoped MatrixGroups
theorem ModularCurve.natCard_fixedPoints_S_cosets_Gamma0_eq_nuTwo (N : ℕ) [NeZero N] :
    Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x} =
      ModularCurve.nuTwo N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_natCard_fixedPoints_S_cosets_Gamma0_eq_nuTwo.solution
