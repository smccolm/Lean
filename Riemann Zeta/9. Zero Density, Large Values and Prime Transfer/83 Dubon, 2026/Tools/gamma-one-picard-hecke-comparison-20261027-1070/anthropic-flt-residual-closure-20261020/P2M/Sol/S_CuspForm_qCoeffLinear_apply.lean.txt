import Mathlib
import Definitions.Def_CuspForm_QCoeffLinear
import P2M.Util
namespace P2MW.S_CuspForm_qCoeffLinear_apply

theorem solution (M : ℕ) (k : ℤ) (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    CuspForm.qCoeffLinear M k n f = ModularFormClass.qCoeff (⇑f) n := rfl
