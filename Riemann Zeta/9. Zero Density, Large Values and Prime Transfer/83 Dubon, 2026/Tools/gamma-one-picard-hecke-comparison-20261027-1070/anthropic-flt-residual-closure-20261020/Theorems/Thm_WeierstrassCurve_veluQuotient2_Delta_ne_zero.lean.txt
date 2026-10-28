import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluQuotient2_Delta_ne_zero

namespace WeierstrassCurve
variable {R : Type*} [CommRing R] [NoZeroDivisors R] {W : WeierstrassCurve R} {x₀ y₀ : R}
open Affine
theorem veluQuotient2_Delta_ne_zero (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluQuotient2_Delta_ne_zero.solution
end WeierstrassCurve
