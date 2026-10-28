import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_eq
import Theorems.Thm_WeierstrassCurve_veluGx_ne_zero_of_two_torsion
import Theorems.Thm_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion
import P2M.Util
namespace P2MW.S_WeierstrassCurve_veluQuotient2_Delta_ne_zero

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {R : Type*} [CommRing R] [NoZeroDivisors R] {W : WeierstrassCurve R}
    {x₀ y₀ : R} (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := by
  rw [veluQuotient2_Delta_eq hQ hgy]
  exact mul_ne_zero (veluGx_ne_zero_of_two_torsion hΔ hQ hgy)
    (pow_ne_zero 2 (velu2QuadDisc_ne_zero_of_two_torsion hΔ hQ hgy))
