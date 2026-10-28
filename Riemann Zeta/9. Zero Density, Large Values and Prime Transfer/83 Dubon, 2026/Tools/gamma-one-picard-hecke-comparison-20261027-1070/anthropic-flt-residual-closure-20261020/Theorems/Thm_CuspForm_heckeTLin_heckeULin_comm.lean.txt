import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_heckeTLin_heckeULin_comm

theorem CuspForm.heckeTLin_heckeULin_comm {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeULin k hqN) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeTLin_heckeULin_comm.solution
