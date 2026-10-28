import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_evalEval_psi_sq

theorem WeierstrassCurve.Affine.evalEval_psi_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_evalEval_psi_sq.solution
