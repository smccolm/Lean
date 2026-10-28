import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_finrank_span_heckeAlgebra_eq_finrank
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

theorem CuspForm.finrank_span_heckeAlgebra_eq_finrank (N : ℕ) [NeZero N] :
    Module.finrank ℂ (Submodule.span ℂ (CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) : Set (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)))) = Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_finrank_span_heckeAlgebra_eq_finrank.solution
