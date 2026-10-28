import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic

namespace WeierstrassCurve
variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic] {x₀ y₀ : F}
open Affine
theorem isElliptic_veluQuotient2_of_isElliptic
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).IsElliptic := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic.solution
end WeierstrassCurve
