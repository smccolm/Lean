import Mathlib
import P2M.Util
import P2M.Sol.S_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one

theorem IsAlgClosed.exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed K]
    (S : Finset E) (hS : (0 : E) ∉ S) :
    ∃ (A : ValuationSubring E) (hK : ∀ c : K, algebraMap K E c ∈ A) (σ : A →+* K),
      RingHom.ker σ = IsLocalRing.maximalIdeal A ∧
      (∀ c : K, σ ⟨algebraMap K E c, hK c⟩ = c) ∧
      ∀ s ∈ S, A.valuation s = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one.solution
