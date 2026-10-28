import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional

theorem AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional.solution
