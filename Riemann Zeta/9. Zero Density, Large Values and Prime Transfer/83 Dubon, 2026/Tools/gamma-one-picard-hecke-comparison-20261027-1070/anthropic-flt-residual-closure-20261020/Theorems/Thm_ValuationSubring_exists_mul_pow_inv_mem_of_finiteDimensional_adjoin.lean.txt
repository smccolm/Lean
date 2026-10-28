import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mul_pow_inv_mem_of_finiteDimensional_adjoin

theorem ValuationSubring.exists_mul_pow_inv_mem_of_finiteDimensional_adjoin
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (u : F)
    (h₁ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) :
    ∃ m : ℕ, ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∉ V →
      u * (f ^ m)⁻¹ ∈ V := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mul_pow_inv_mem_of_finiteDimensional_adjoin.solution
