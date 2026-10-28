import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Algebraic.Defs
import P2M.Util
import P2M.Sol.S_KaehlerDifferential_D_ne_zero_of_transcendental

theorem KaehlerDifferential.D_ne_zero_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    KaehlerDifferential.D K F x ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_KaehlerDifferential_D_ne_zero_of_transcendental.solution
