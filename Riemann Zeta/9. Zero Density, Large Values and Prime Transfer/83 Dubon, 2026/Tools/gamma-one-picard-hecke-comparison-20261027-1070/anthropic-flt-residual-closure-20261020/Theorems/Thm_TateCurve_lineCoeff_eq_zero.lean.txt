import Mathlib
import Definitions.Def_TateCurve_DefectLines
import P2M.Util
import P2M.Sol.S_TateCurve_lineCoeff_eq_zero

open TateCurve
theorem TateCurve.lineCoeff_eq_zero : ∀ N k : ℕ, 1 ≤ k → k ≤ N → lineCoeff N k = 0 := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_lineCoeff_eq_zero.solution
