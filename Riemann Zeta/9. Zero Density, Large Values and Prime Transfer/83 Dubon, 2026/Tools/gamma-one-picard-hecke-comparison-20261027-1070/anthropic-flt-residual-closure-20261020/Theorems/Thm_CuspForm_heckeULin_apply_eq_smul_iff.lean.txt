import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_heckeULin_apply_eq_smul_iff

theorem CuspForm.heckeULin_apply_eq_smul_iff {N : ℕ} [NeZero N] (k : ℤ) {p : ℕ} (hpN : p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (c : ℂ) :
    CuspForm.heckeULin k hpN f = c • f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeULin_apply_eq_smul_iff.solution
