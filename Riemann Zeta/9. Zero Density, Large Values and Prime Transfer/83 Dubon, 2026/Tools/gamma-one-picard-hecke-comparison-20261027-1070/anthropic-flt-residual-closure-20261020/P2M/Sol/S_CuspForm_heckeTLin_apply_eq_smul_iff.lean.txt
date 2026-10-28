import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularFormClass_heckeT_eq_smul_iff
import P2M.Util
namespace P2MW.S_CuspForm_heckeTLin_apply_eq_smul_iff

theorem solution {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (c : ℂ) :
    CuspForm.heckeTLin k hp hpN f = c • f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n := by
  rw [← ModularFormClass.heckeT_eq_smul_iff f (by simp) hp.ne_zero c, DFunLike.ext'_iff,
    CuspForm.coe_heckeTLin_apply, CuspForm.IsGLPos.coe_smul]
