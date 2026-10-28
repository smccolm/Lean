import Mathlib
import Definitions.Def_CuspForm_QCoeffLinear
import P2M.Util
import P2M.Sol.S_CuspForm_qCoeffLinear_apply

theorem CuspForm.qCoeffLinear_apply (M : ℕ) (k : ℤ) (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    CuspForm.qCoeffLinear M k n f = ModularFormClass.qCoeff (⇑f) n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeffLinear_apply.solution
