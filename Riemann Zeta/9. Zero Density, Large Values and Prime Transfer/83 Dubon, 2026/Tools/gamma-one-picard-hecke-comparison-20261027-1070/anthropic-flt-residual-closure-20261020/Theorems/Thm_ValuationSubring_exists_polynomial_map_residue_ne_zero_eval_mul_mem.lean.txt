import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem

theorem ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z : F) :
    ∃ q : Polynomial A, (q.map (IsLocalRing.residue A)) ≠ 0 ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V →
        (Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q) * z ∈ V := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem.solution
