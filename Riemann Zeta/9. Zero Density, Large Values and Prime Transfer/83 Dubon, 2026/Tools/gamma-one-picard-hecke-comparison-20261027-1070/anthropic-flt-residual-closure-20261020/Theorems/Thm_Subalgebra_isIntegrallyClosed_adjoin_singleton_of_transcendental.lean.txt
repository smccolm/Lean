import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental

theorem Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental
    {L : Type*} [Field L] {F : Type*} [CommRing F] [IsDomain F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) :
    IsIntegrallyClosed (Algebra.adjoin L ({x} : Set F)) := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental.solution
