import Dubon2026.SourceEllipticOddRootPackets
import Dubon2026.SourceEllipticOddDoublingFormula

/-! The four root-packet identities at the actual double of a curve point.
The required quartic identity is derived from the existing integral
division-polynomial multiplication theorem. This removes the artificial
doubling-numerator premise from the odd quotient discriminant chain for
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}
  (ha1 : V.a₁ = 0) (ha3 : V.a₃ = 0) {e₁ e₂ e₃ xq yq : F}
  (hσ1 : e₁ + e₂ + e₃ = -V.a₂) (hσ2 : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = V.a₄)
  (hσ3 : e₁ * e₂ * e₃ = -V.a₆) (hq : V.toAffine.Equation xq yq)
  (h1 : xq ≠ e₁) (h2 : xq ≠ e₂) (h3 : xq ≠ e₃)
  (hy : yq ≠ V.toAffine.negY xq yq)

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 hy in
theorem double_pack_esymm1 :
    xiAt V e₁ xq yq + xiAt V e₂ xq yq + xiAt V e₃ xq yq + xq = 4 * (V.toAffine.addX xq xq (V.toAffine.slope xq xq yq yq)) :=
  pack_esymm1 ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 (double_x_mul_psi2Sq V hq hy)

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 hy in
theorem double_pack_esymm2 :
    xiAt V e₁ xq yq * xiAt V e₂ xq yq + xiAt V e₁ xq yq * xiAt V e₃ xq yq
        + xiAt V e₂ xq yq * xiAt V e₃ xq yq
        + xq * (xiAt V e₁ xq yq + xiAt V e₂ xq yq + xiAt V e₃ xq yq)
      = -(V.b₄ + V.b₂ * (V.toAffine.addX xq xq (V.toAffine.slope xq xq yq yq))) :=
  pack_esymm2 ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 (double_x_mul_psi2Sq V hq hy)

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 hy in
theorem double_pack_esymm3 :
    xiAt V e₁ xq yq * xiAt V e₂ xq yq * xiAt V e₃ xq yq
        + xq * (xiAt V e₁ xq yq * xiAt V e₂ xq yq + xiAt V e₁ xq yq * xiAt V e₃ xq yq
          + xiAt V e₂ xq yq * xiAt V e₃ xq yq)
      = 2 * V.b₆ + 2 * V.b₄ * (V.toAffine.addX xq xq (V.toAffine.slope xq xq yq yq)) :=
  pack_esymm3 ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 (double_x_mul_psi2Sq V hq hy)

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 hy in
theorem double_pack_esymm4 :
    xiAt V e₁ xq yq * xiAt V e₂ xq yq * xiAt V e₃ xq yq * xq = -(V.b₈ + V.b₆ * (V.toAffine.addX xq xq (V.toAffine.slope xq xq yq yq))) :=
  pack_esymm4 ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 (double_x_mul_psi2Sq V hq hy)

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
