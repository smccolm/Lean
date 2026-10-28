import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin

theorem ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (O : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ O) (hO : O ≠ ⊤) :
    IsPrincipalIdealRing O := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin.solution
