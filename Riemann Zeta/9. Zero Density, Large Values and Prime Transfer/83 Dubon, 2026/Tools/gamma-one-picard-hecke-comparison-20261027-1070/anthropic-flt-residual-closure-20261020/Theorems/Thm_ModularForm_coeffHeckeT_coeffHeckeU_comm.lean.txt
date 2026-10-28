import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularForm_coeffHeckeT_coeffHeckeU_comm

theorem ModularForm.coeffHeckeT_coeffHeckeU_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) : ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeU q a) = ModularForm.coeffHeckeU q (ModularForm.coeffHeckeT k p a) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_coeffHeckeT_coeffHeckeU_comm.solution
