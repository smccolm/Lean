import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Algebraic.Defs
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental

theorem AlgebraicCurve.isAlgebraic_adjoin_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.solution
