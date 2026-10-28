import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc

namespace WeierstrassCurve
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}
open Affine
theorem Delta_eq_veluGx_sq_mul_velu2QuadDisc {x₀ y₀ : R}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.Δ = W.veluGx x₀ y₀ ^ 2 * W.velu2QuadDisc x₀ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc.solution
end WeierstrassCurve
