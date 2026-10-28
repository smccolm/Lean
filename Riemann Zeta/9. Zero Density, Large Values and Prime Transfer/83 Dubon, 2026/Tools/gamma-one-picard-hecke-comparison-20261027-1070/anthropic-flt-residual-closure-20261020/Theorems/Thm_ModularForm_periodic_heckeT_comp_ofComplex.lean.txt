import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularForm_periodic_heckeT_comp_ofComplex

theorem ModularForm.periodic_heckeT_comp_ofComplex {f : UpperHalfPlane → ℂ} (hf : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (k : ℤ) (p : ℕ) : Function.Periodic (ModularForm.heckeT k p f ∘ UpperHalfPlane.ofComplex) 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_periodic_heckeT_comp_ofComplex.solution
