import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_separating_transcendental_of_perfectField

theorem AlgebraicCurve.exists_separating_transcendental_of_perfectField
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_separating_transcendental_of_perfectField.solution
