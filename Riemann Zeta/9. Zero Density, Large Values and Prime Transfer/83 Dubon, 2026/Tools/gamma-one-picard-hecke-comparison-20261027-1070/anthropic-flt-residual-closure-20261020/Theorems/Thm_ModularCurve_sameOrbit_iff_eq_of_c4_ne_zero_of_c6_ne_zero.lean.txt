import Mathlib
import Definitions.Def_ModularCurve_EMD
import P2M.Util
import P2M.Sol.S_ModularCurve_sameOrbit_iff_eq_of_c4_ne_zero_of_c6_ne_zero

open ModularCurve WeierstrassCurve
theorem ModularCurve.sameOrbit_iff_eq_of_c4_ne_zero_of_c6_ne_zero (E₀ : WeierstrassCurve (AlgebraicClosure ℚ))
    (hc₄ : E₀.c₄ ≠ 0) (hc₆ : E₀.c₆ ≠ 0) (H H' : AddSubgroup E₀.toAffine.Point) :
    SameOrbit E₀ H H' ↔ H' = H ∧ ∃ g : E₀.toAffine.Point, H = AddSubgroup.zmultiples g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sameOrbit_iff_eq_of_c4_ne_zero_of_c6_ne_zero.solution
