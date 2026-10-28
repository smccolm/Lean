import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_ellipticNet_three
import Definitions.Def_WeierstrassCurve_DivPolyMulFormula

open Polynomial
theorem P2M.Dup.WeierstrassCurve.ellipticNet_three {R : Type*} [CommRing R] (W : WeierstrassCurve R) (t : R) :
    2 * t * (W.Φ 3).eval t * ((W.Φ 3).eval t + t * (W.ΨSq 3).eval t) +
        W.b₂ * t * ((W.Φ 3).eval t * (W.ΨSq 3).eval t) +
        W.b₄ * (((W.Φ 3).eval t + t * (W.ΨSq 3).eval t) * (W.ΨSq 3).eval t) +
        W.b₆ * (W.ΨSq 3).eval t ^ 2 =
      (W.Φ 4).eval t * (W.ΨSq 2).eval t + (W.Φ 2).eval t * (W.ΨSq 4).eval t := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_ellipticNet_three.solution
#p2m_type_eq_warn P2M.Dup.WeierstrassCurve.ellipticNet_three WeierstrassCurve.ellipticNet_three
