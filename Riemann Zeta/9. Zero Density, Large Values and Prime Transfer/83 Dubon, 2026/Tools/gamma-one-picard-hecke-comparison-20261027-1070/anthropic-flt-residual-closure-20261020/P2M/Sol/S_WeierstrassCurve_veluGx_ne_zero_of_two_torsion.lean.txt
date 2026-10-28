import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Theorems.Thm_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc
import P2M.Util
namespace P2MW.S_WeierstrassCurve_veluGx_ne_zero_of_two_torsion

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ : R} (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.veluGx x₀ y₀ ≠ 0 := by
  intro h
  exact hΔ (by rw [Delta_eq_veluGx_sq_mul_velu2QuadDisc hQ hgy, h]; ring)
