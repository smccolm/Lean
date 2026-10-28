import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularFormClass_heckeT_heckeT_comm
import P2M.Util
namespace P2MW.S_CuspForm_heckeTLin_comm

theorem solution {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeTLin k hq hqN) := by
  by_cases hpq : p = q
  · subst hpq; exact Commute.refl _
  · rw [commute_iff_eq]; ext f τ
    simpa using congrFun (ModularFormClass.heckeT_heckeT_comm f (by simp)
      ((Nat.coprime_primes hp hq).mpr hpq)) τ
