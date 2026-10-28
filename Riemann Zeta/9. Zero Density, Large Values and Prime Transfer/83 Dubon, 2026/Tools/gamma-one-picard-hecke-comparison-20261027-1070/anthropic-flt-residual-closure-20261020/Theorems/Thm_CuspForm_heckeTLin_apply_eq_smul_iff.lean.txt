import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_heckeTLin_apply_eq_smul_iff

theorem CuspForm.heckeTLin_apply_eq_smul_iff {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (c : ℂ) :
    CuspForm.heckeTLin k hp hpN f = c • f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeTLin_apply_eq_smul_iff.solution
