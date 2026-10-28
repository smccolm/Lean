import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_CuspSpace_exists_normalForm

open OnePoint
theorem ModularCurve.CuspSpace.exists_normalForm {N : ℕ} (hN : N ≠ 0) (x : ModularCurve.CuspSpace N) :
    ∃ a : ℤ, IsCoprime a (ModularCurve.CuspSpace.cuspDenom N x : ℤ) ∧
      x = ModularCurve.CuspSpace.mk N (ModularCurve.ratPoint a (ModularCurve.CuspSpace.cuspDenom N x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CuspSpace_exists_normalForm.solution
