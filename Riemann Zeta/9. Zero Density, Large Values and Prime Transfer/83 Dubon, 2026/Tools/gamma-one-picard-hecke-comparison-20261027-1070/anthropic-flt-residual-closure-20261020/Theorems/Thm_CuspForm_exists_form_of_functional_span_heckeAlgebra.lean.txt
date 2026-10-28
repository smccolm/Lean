import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_form_of_functional_span_heckeAlgebra
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

theorem CuspForm.exists_form_of_functional_span_heckeAlgebra (N : ℕ) [NeZero N] (φ : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) →ₗ[ℂ] ℂ) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      ∀ T ∈ Submodule.span ℂ (CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) : Set (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))), φ T = ModularFormClass.qCoeff (T f) 1 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_form_of_functional_span_heckeAlgebra.solution
