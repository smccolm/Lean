import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_natCard_fixedPoints_ST_cosets_Gamma0_eq_nuThree

open scoped MatrixGroups
theorem ModularCurve.natCard_fixedPoints_ST_cosets_Gamma0_eq_nuThree (N : ℕ) [NeZero N] :
    Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N //
        (ModularGroup.S * ModularGroup.T) • x = x} =
      ModularCurve.nuThree N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_natCard_fixedPoints_ST_cosets_Gamma0_eq_nuThree.solution
