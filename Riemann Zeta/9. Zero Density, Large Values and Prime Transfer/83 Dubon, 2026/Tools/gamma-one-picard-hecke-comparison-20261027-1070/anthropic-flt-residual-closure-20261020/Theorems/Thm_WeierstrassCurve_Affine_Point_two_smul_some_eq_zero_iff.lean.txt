import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff

theorem WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) : 2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff.solution
