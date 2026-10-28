import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_qCoeff_heckeU

theorem UpperHalfPlane.qCoeff_heckeU {f : UpperHalfPlane → ℂ} (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeU k p f) n = ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_qCoeff_heckeU.solution
