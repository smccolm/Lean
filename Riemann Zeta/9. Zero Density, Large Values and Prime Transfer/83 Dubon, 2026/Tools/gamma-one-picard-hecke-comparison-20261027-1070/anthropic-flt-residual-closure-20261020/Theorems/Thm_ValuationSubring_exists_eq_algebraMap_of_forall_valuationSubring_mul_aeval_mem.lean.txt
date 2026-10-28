import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem

open Polynomial

theorem ValuationSubring.exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    (t t' : L[X])
    (ht : A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1)
    (ht' : A.valuation (t'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t'.coeff j) < 1)
    (x : F)
    (hx : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → x * aeval f t ∈ V)
    (hx' : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
      x * aeval f⁻¹ t' ∈ V) :
    ∃ c : L, x = algebraMap L F c := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem.solution
