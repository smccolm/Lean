import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularForm_mdifferentiable_heckeU

theorem ModularForm.mdifferentiable_heckeU {f : UpperHalfPlane → ℂ} (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU k p f) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_mdifferentiable_heckeU.solution
