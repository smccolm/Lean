import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_qCoeff_zero

theorem CuspForm.qCoeff_zero {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ModularFormClass.qCoeff f 0 = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeff_zero.solution
