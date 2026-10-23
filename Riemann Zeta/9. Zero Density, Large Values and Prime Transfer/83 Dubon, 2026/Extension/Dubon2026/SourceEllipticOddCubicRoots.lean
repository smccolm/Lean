import Dubon2026.SourceEllipticOddCurveCoordinates

/-! Native cubic-root formulas for the explicit odd quotient discriminant.
Mathlib's cubic discriminant and Vieta identities supply these formulas
for the actual two-torsion polynomial. This discharges the root-coordinate
input to odd quotient ellipticity, then cyclic quotient products, inertia
census and modular-curve good reduction for DUB-17 / DUB-18. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K]

theorem delta_eq_prod_two_torsion_roots (V : WeierstrassCurve K)
    (h2 : (2 : K) ≠ 0) {r₁ r₂ r₃ : K}
    (hr : (Cubic.map (RingHom.id K) V.twoTorsionPolynomial).roots = {r₁, r₂, r₃}) :
    V.Δ = 16 * ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 := by
  have h4 : (4 : K) ≠ 0 := by simpa only [show (2 : K) ^ 2 = 4 by ring] using pow_ne_zero 2 h2
  have h16 : (16 : K) ≠ 0 := by simpa only [show (2 : K) ^ 4 = 16 by ring] using pow_ne_zero 4 h2
  have hd := Cubic.discr_eq_prod_three_roots (P := V.twoTorsionPolynomial) h4 hr
  simp only [RingHom.id_apply] at hd
  rw [twoTorsionPolynomial_discr] at hd
  change 16 * V.Δ = (4 * 4 * (r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 at hd
  apply mul_left_cancel₀ h16
  linear_combination hd

theorem two_torsion_root_symmetric_sums (V : WeierstrassCurve K)
    (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) (h2 : (2 : K) ≠ 0) {r₁ r₂ r₃ : K}
    (hr : (Cubic.map (RingHom.id K) V.twoTorsionPolynomial).roots = {r₁, r₂, r₃}) :
    r₁ + r₂ + r₃ = -V.a₂ ∧ r₁ * r₂ + r₁ * r₃ + r₂ * r₃ = V.a₄ ∧
      r₁ * r₂ * r₃ = -V.a₆ := by
  have h4 : (4 : K) ≠ 0 := by simpa only [show (2 : K) ^ 2 = 4 by ring] using pow_ne_zero 2 h2
  have hb := Cubic.b_eq_three_roots (P := V.twoTorsionPolynomial) h4 hr
  have hc := Cubic.c_eq_three_roots (P := V.twoTorsionPolynomial) h4 hr
  have hd := Cubic.d_eq_three_roots (P := V.twoTorsionPolynomial) h4 hr
  simp only [RingHom.id_apply, twoTorsionPolynomial, b₂, b₄, b₆, ha₁, ha₃] at hb hc hd
  refine ⟨?_, ?_, ?_⟩
  · apply mul_left_cancel₀ h4
    linear_combination hb
  · apply mul_left_cancel₀ h4
    linear_combination -hc
  · apply mul_left_cancel₀ h4
    linear_combination hd

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
