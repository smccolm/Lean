import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_WeierstrassCurve_VeluQuotientJInvariant
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_eq
import Theorems.Thm_WeierstrassCurve_veluQuotient2_cFour
import P2M.Util
namespace P2MW.S_WeierstrassCurve_veluQuotient2_j

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic] {x₀ y₀ : F}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    haveI : (W.veluQuotient2 x₀ y₀).IsElliptic :=
      isElliptic_veluQuotient2_of_isElliptic hQ hgy
    (W.veluQuotient2 x₀ y₀).j
      = (W.c₄ + 240 * W.veluGx x₀ y₀) ^ 3
        / (W.veluGx x₀ y₀ * W.velu2QuadDisc x₀ ^ 2) := by
  haveI hE : (W.veluQuotient2 x₀ y₀).IsElliptic :=
    isElliptic_veluQuotient2_of_isElliptic hQ hgy
  have hΔ' : (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := (W.veluQuotient2 x₀ y₀).isUnit_Δ.ne_zero
  rw [← veluQuotient2_Delta_eq hQ hgy, eq_div_iff hΔ', mul_comm, Δ_mul_j, veluQuotient2_cFour]
