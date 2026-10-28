import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental

theorem AlgebraicCurve.finiteDimensional_adjoin_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.solution
