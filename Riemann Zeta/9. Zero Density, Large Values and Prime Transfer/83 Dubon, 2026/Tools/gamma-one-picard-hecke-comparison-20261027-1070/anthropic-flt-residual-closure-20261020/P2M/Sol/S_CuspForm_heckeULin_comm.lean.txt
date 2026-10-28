import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularFormClass_heckeU_heckeU_comm
import P2M.Util
namespace P2MW.S_CuspForm_heckeULin_comm

theorem solution {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hpN : p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeULin k hpN) (CuspForm.heckeULin k hqN) := by
  rw [commute_iff_eq]; ext f τ
  simpa using congrFun (ModularFormClass.heckeU_heckeU_comm f (by simp) p q) τ
