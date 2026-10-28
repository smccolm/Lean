import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_moduleFinite_heckeAlgebra_two
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

theorem CuspForm.moduleFinite_heckeAlgebra_two (N : ℕ) [NeZero N] (S : Set ℕ) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N 2 S) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_moduleFinite_heckeAlgebra_two.solution
