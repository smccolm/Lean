import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluQuotient2_cFour

namespace WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₀ y₀ : R)
theorem veluQuotient2_cFour :
    (W.veluQuotient2 x₀ y₀).c₄ = W.c₄ + 240 * W.veluGx x₀ y₀ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluQuotient2_cFour.solution
end WeierstrassCurve
