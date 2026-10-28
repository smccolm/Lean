import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_kaehlerRankOne_of_transcendental

open KaehlerDifferential
theorem AlgebraicCurve.kaehlerRankOne_of_transcendental
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_kaehlerRankOne_of_transcendental.solution
