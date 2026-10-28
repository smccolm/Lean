import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable

theorem AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (φ : F →+* F') (w : ValuationSubring F')
    (hwK : ∀ a : K, φ (algebraMap K F a) ∈ w) (hwx : ∃ y : F, φ y ∉ w) :
    ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = w.comap φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable.solution
