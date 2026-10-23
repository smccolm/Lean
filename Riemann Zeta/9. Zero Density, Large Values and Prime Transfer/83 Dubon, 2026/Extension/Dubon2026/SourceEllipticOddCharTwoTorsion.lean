import Dubon2026.SourceEllipticOddOrbitInvariance

/-! Characteristic-two algebra for the actual odd quotient discriminant.
The ordinary case uses the squared-coordinate norm polynomial and its two
required coefficients. The supersingular case uses the actual unchanged
a3 coefficient. These cases are required by odd quotient ellipticity,
cyclic quotient products, inertia census and modular-curve good reduction
for DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2; characteristic two is not excluded.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Native root bounds and the
already proved denominator degree replace duplicate general foundations. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
open WeierstrassCurve Polynomial Finset
noncomputable section
section CharTwoOrdCurve


variable {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}

omit [DecidableEq F] in

theorem equation_ord (ha1 : V.a₁ = 1) (ha3 : V.a₃ = 0) (ha4 : V.a₄ = 0) {x y : F}
    (h : V.toAffine.Equation x y) : y ^ 2 + x * y = x ^ 3 + V.a₂ * x ^ 2 + V.a₆ := by
  rw [Affine.equation_iff, ha1, ha3, ha4] at h
  linear_combination h

theorem addX_twoTorsion (h2 : (2 : F) = 0) (ha1 : V.a₁ = 1) (ha3 : V.a₃ = 0)
    (ha4 : V.a₄ = 0) {c x y : F} (hc : c ^ 2 = V.a₆) (h : V.toAffine.Equation x y)
    (hx : x ≠ 0) :
    V.toAffine.addX 0 x (V.toAffine.slope 0 x c y) = c / x := by
  have e := equation_ord ha1 ha3 ha4 h
  rw [Affine.slope_of_X_ne (Ne.symm hx)]
  simp only [Affine.addX, toAffine, ha1]
  apply mul_left_cancel₀ (pow_ne_zero 2 hx)
  have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  linear_combination e + hc + (V.a₆ - c * (x + y)) * h2
    + ((c - y) ^ 2 * (x * x⁻¹ + 1) - x * (c - y) - c * x) * hinv

omit [DecidableEq F] in

theorem nonsingular_twoTorsion [V.IsElliptic] (ha3 : V.a₃ = 0) (ha4 : V.a₄ = 0) {c : F}
    (hc : c ^ 2 = V.a₆) : V.toAffine.Nonsingular 0 c := by
  rw [← Affine.equation_iff_nonsingular, Affine.equation_iff, ha3, ha4]
  linear_combination hc

omit [DecidableEq F] in

theorem negY_twoTorsion (h2 : (2 : F) = 0) (ha3 : V.a₃ = 0) (c : F) :
    V.toAffine.negY 0 c = c := by
  simp only [Affine.negY, ha3]
  linear_combination (-c) * h2

theorem coordsOrZero_twoTorsion_add_fst (h2 : (2 : F) = 0) (ha1 : V.a₁ = 1)
    (ha3 : V.a₃ = 0) (ha4 : V.a₄ = 0) {c : F} (hT : V.toAffine.Nonsingular 0 c)
    (hc : c ^ 2 = V.a₆) {x y : F} (h : V.toAffine.Nonsingular x y) (hx : x ≠ 0) :
    ((coordsOrZero (Affine.Point.some 0 c hT + Affine.Point.some x y h))).1 = c / x := by
  rw [Affine.Point.add_of_X_ne (Ne.symm hx), coordsOrZero]
  exact addX_twoTorsion h2 ha1 ha3 ha4 hc h.1 hx


end CharTwoOrdCurve

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
