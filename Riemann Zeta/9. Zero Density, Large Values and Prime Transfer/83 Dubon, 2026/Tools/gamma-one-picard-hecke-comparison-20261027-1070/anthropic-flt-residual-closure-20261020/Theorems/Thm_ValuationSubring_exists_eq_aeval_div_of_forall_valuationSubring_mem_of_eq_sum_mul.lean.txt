import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul

open Polynomial

theorem ValuationSubring.exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    {ι : Type*} [Fintype ι] (z : ι → F)
    (hzT : ∀ i, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z i ∈ V)
    (hzind : LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z)
    (hres : ∀ (y : F) (w : ι → F),
      (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y ∈ V) →
      (∀ i, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
        ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
        w i * aeval f q = aeval f p) →
      y = ∑ i, w i * z i →
      ∃ (C₁ : ι → L[X]) (μ : ι → F), (∀ i j, (C₁ i).coeff j ∈ A) ∧
        (∀ i, ∃ p q : L[X], (∀ j, A.valuation (p.coeff j) < 1) ∧
          ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
          μ i * aeval f q = aeval f p) ∧
        y = ∑ i, (aeval f (C₁ i) + μ i) * z i)
    (s : F) (w : ι → F)
    (hsT : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → s ∈ V)
    (hw : ∀ i, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
      ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
      w i * aeval f q = aeval f p)
    (hs : s = ∑ i, w i * z i) (i : ι) :
    ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
      (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
      w i = aeval f p / aeval f t := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul.solution
