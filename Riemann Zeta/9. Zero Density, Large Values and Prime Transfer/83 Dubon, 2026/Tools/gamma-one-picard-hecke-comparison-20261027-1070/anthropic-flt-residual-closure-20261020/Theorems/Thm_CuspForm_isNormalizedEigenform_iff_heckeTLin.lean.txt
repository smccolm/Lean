import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_isNormalizedEigenform_iff_heckeTLin

theorem CuspForm.isNormalizedEigenform_iff_heckeTLin {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ (p : ℕ) (hp : p.Prime),
      ((hpN : ¬ p ∣ N) → CuspForm.heckeTLin 2 hp hpN f = ModularFormClass.qCoeff f p • f) ∧
      ((hpN : p ∣ N) → CuspForm.heckeULin 2 hpN f = ModularFormClass.qCoeff f p • f)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_isNormalizedEigenform_iff_heckeTLin.solution
