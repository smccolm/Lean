import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_of_valuationSubring

theorem AlgebraicCurve.Place.exists_of_valuationSubring {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤) : ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = A := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_of_valuationSubring.solution
