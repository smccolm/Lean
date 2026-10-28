import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_eq
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluQuotient2_j
attribute [-instance] WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4
attribute [-simp] WeierstrassCurve.veluX_empty

namespace WeierstrassCurve
variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic] {x₀ y₀ : F}
open Affine
theorem veluQuotient2_j (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    haveI : (W.veluQuotient2 x₀ y₀).IsElliptic :=
      isElliptic_veluQuotient2_of_isElliptic hQ hgy
    (W.veluQuotient2 x₀ y₀).j
      = (W.c₄ + 240 * W.veluGx x₀ y₀) ^ 3
        / (W.veluGx x₀ y₀ * W.velu2QuadDisc x₀ ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluQuotient2_j.solution
end WeierstrassCurve
