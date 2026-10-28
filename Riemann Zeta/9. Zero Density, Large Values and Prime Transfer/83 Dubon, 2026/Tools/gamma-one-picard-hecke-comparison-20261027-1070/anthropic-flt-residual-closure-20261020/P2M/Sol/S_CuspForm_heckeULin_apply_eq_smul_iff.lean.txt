import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularFormClass_heckeU_eq_smul_iff
import P2M.Util
namespace P2MW.S_CuspForm_heckeULin_apply_eq_smul_iff

theorem solution {N : ℕ} [NeZero N] (k : ℤ) {p : ℕ} (hpN : p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (c : ℂ) :
    CuspForm.heckeULin k hpN f = c • f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n := by
  rw [← ModularFormClass.heckeU_eq_smul_iff f (by simp) (ne_zero_of_dvd_ne_zero (NeZero.ne N) hpN) c,
    DFunLike.ext'_iff, CuspForm.coe_heckeULin_apply, CuspForm.IsGLPos.coe_smul]
