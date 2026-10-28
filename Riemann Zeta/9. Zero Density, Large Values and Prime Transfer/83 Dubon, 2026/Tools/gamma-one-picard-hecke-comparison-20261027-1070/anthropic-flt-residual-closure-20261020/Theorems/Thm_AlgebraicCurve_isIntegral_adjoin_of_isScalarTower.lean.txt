import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isIntegral_adjoin_of_isScalarTower

theorem AlgebraicCurve.isIntegral_adjoin_of_isScalarTower {K L F : Type*} [CommRing K] [CommRing L] [CommRing F] [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F] {j x : F} (hx : IsIntegral (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin L {j}) x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isIntegral_adjoin_of_isScalarTower.solution
