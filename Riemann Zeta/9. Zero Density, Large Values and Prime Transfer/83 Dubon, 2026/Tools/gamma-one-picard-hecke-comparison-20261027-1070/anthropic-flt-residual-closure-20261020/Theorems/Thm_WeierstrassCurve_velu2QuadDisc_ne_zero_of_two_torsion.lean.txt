import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion

namespace WeierstrassCurve
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}
open Affine
theorem velu2QuadDisc_ne_zero_of_two_torsion {x₀ y₀ : R} (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.velu2QuadDisc x₀ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion.solution
end WeierstrassCurve
