import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum

open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] : ∃ v : Place K (RatFunc K), ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum.solution
