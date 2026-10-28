import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularForm_coeffHeckeU_comm

theorem ModularForm.coeffHeckeU_comm (p q : ℕ) (a : ℕ → ℂ) : ModularForm.coeffHeckeU p (ModularForm.coeffHeckeU q a) = ModularForm.coeffHeckeU q (ModularForm.coeffHeckeU p a) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_coeffHeckeU_comm.solution
