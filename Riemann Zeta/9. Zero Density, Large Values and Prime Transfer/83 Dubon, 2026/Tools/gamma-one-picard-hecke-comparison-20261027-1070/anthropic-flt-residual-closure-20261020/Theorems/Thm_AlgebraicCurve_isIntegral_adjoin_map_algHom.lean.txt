import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isIntegral_adjoin_map_algHom

theorem AlgebraicCurve.isIntegral_adjoin_map_algHom {K F F' : Type*} [CommRing K] [CommRing F] [CommRing F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') {j x : F} (hx : IsIntegral (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin K {φ j}) (φ x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isIntegral_adjoin_map_algHom.solution
