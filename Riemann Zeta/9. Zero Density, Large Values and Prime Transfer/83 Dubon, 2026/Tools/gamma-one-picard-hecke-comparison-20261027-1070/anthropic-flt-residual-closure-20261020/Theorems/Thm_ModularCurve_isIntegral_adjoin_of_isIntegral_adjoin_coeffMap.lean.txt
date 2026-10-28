import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap

open ModularCurve

theorem ModularCurve.isIntegral_adjoin_of_isIntegral_adjoin_coeffMap {k L : Type*} [Field k]
    [Field L] (σ : k →+* L) (j x : LaurentSeries k)
    (h : IsIntegral (Algebra.adjoin L ({coeffMap σ j} : Set (LaurentSeries L))) (coeffMap σ x)) :
    IsIntegral (Algebra.adjoin k ({j} : Set (LaurentSeries k))) x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap.solution
