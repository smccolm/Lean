import Mathlib
import P2M.Util
import P2M.Sol.S_IsAlgClosed_exists_valuationSubring_ringHom_retraction

theorem IsAlgClosed.exists_valuationSubring_ringHom_retraction
    (K K' : Type*) [Field K] [IsAlgClosed K] [Field K'] [Algebra K K'] :
    ∃ (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K),
      RingHom.ker σ = IsLocalRing.maximalIdeal A ∧
      ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c := by p2m_exact_reverting @_root_.P2MW.S_IsAlgClosed_exists_valuationSubring_ringHom_retraction.solution
