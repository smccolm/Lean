import Mathlib
import P2M.Util
import P2M.Sol.S_Field_nonempty_ringHom_complex_of_countable

universe u

theorem Field.nonempty_ringHom_complex_of_countable
    (K : Type u) [Field K] [CharZero K] [Countable K] : Nonempty (K →+* ℂ) := by p2m_exact_reverting @_root_.P2MW.S_Field_nonempty_ringHom_complex_of_countable.solution
