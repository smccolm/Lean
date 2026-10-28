import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

theorem CuspForm.eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero (N : ℕ) [NeZero N] (T : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))
    (hT : T ∈ Submodule.span ℂ (CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) : Set (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))))
    (h : ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, ModularFormClass.qCoeff (T f) 1 = 0) :
    T = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero.solution
