import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem

theorem Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z : F) :
    ∃ q₀ : Algebra.adjoin L ({f} : Set F), q₀ ≠ 0 ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → (q₀ : F) * z ∈ V := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem.solution
