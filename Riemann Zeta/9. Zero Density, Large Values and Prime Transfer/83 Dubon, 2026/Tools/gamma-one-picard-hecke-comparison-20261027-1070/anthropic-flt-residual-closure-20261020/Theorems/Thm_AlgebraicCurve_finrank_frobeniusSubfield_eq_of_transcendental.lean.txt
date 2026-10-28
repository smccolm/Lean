import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental

theorem AlgebraicCurve.finrank_frobeniusSubfield_eq_of_transcendental {K M : Type*} [Field K] [Field M] [Algebra K M]
    [PerfectField K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (t : M) (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set M)) M] :
    haveI : ExpChar M p := expChar_of_injective_algebraMap (algebraMap K M).injective p
    Module.finrank ↥(frobenius M p).fieldRange M = p := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental.solution
