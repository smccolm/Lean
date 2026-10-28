import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_ellipticNet_four
import Definitions.Def_WeierstrassCurve_DivPolyMulFormula

open Polynomial
theorem P2M.Dup.WeierstrassCurve.ellipticNet_four {R : Type*} [CommRing R] (W : WeierstrassCurve R) (t : R) :
    2 * t * (W.Φ 4).eval t * ((W.Φ 4).eval t + t * (W.ΨSq 4).eval t) +
        W.b₂ * t * ((W.Φ 4).eval t * (W.ΨSq 4).eval t) +
        W.b₄ * (((W.Φ 4).eval t + t * (W.ΨSq 4).eval t) * (W.ΨSq 4).eval t) +
        W.b₆ * (W.ΨSq 4).eval t ^ 2 =
      (W.Φ 5).eval t * (W.ΨSq 3).eval t + (W.Φ 3).eval t * (W.ΨSq 5).eval t := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_ellipticNet_four.solution
#p2m_type_eq_warn P2M.Dup.WeierstrassCurve.ellipticNet_four WeierstrassCurve.ellipticNet_four
