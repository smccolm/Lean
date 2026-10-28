import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative

theorem ModularCurve.thetaL_coeffMap_eq_coeffMap_single_mul_derivative {R : Type*} [CommRing R]
    {K : Type*} [Field K] (φ : R →+* K) (w : LaurentSeries R) :
    ModularCurve.thetaL K (ModularCurve.coeffMap φ w) =
      ModularCurve.coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.solution
