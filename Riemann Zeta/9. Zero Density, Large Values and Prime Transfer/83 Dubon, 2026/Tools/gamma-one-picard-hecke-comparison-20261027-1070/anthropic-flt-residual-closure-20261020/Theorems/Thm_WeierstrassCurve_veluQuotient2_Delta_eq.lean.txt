import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluQuotient2_Delta_eq

namespace WeierstrassCurve
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}
open Affine
theorem veluQuotient2_Delta_eq {x₀ y₀ : R}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).Δ = W.veluGx x₀ y₀ * W.velu2QuadDisc x₀ ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluQuotient2_Delta_eq.solution
end WeierstrassCurve
