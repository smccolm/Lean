import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import P2M.Util
namespace P2MW.S_WeierstrassCurve_veluQuotient2_cFour

open WeierstrassCurve in
theorem solution {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₀ y₀ : R) :
    (W.veluQuotient2 x₀ y₀).c₄ = W.c₄ + 240 * W.veluGx x₀ y₀ := by
  have hb₄ : (W.veluQuotient2 x₀ y₀).b₄ = W.b₄ - 10 * W.veluGx x₀ y₀ := by
    simp only [b₄, veluQuotient2_a₁, veluQuotient2_a₃, veluQuotient2_a₄]; ring
  simp only [c₄, veluQuotient2_b₂, hb₄]; ring
