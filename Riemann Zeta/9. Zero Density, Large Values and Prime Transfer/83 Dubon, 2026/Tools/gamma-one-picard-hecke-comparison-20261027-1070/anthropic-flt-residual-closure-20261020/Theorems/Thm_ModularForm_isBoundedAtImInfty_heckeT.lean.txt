import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularForm_isBoundedAtImInfty_heckeT

theorem ModularForm.isBoundedAtImInfty_heckeT {f : UpperHalfPlane → ℂ} (hf : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) (p : ℕ) : UpperHalfPlane.IsBoundedAtImInfty (ModularForm.heckeT k p f) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_isBoundedAtImInfty_heckeT.solution
