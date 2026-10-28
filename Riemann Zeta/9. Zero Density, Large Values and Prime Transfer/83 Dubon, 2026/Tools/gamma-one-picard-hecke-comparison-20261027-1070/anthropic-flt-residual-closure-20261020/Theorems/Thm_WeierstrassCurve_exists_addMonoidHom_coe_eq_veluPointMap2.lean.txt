import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient2 x₀ y₀).toAffine.Point,
      ⇑φ = veluPointMap2 h2 hQ hgy hΔ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.solution
