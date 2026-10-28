import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeT
import P2M.Util
namespace P2MW.S_CuspForm_isNormalizedEigenform_iff_heckeTLin

theorem solution {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ (p : ℕ) (hp : p.Prime),
      ((hpN : ¬ p ∣ N) → CuspForm.heckeTLin 2 hp hpN f = ModularFormClass.qCoeff f p • f) ∧
      ((hpN : p ∣ N) → CuspForm.heckeULin 2 hpN f = ModularFormClass.qCoeff f p • f)) := by
  rw [CuspForm.isNormalizedEigenform_iff_heckeT]
  simp only [DFunLike.ext'_iff (f := CuspForm.heckeTLin 2 _ _ f), DFunLike.ext'_iff (f := CuspForm.heckeULin 2 _ f),
    CuspForm.coe_heckeTLin_apply, CuspForm.coe_heckeULin_apply, CuspForm.IsGLPos.coe_smul]
