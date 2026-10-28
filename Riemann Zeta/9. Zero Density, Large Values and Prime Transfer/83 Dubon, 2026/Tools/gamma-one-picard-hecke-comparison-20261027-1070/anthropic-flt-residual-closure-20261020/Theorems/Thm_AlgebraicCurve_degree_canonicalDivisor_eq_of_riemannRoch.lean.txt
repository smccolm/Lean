import Mathlib
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch

open AlgebraicCurve KaehlerDifferential
theorem AlgebraicCurve.degree_canonicalDivisor_eq_of_riemannRoch {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch.solution
