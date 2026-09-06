import GafniTao.ClassicalA3BOptimization
import GafniTao.PintzNearOneZetaExponent

/-!
# Pintz's coefficient-one-half exponent down to three quarters

In Pintz's off-diagonal Gram kernel the real part is
`1 - etaJ - etaK - 4 * eta`.  Since both zero distances may be as large as
`eta`, the strict range `eta < 1 / 24` requires the zeta input down to real
part `3 / 4`, not merely `11 / 12`.

The logarithmic phase is covered by four explicit ranges.  The classical
`AB` bound is used through `9 / 4`, the native `A^2B` bound through `25 / 8`,
the native `A^3B` bound through `7 / 2`, and the existing Heath--Brown
large-scale estimate thereafter.  This file proves the exact exponent
comparisons needed to assemble those bounds.
-/

namespace GafniTao

noncomputable section

private theorem threeQuarter_three_halves_eq_sqrt_cube
    {u : ℝ} (hu : 0 ≤ u) :
    u ^ (3 / 2 : ℝ) = (Real.sqrt u) ^ 3 := by
  rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * (3 : ℕ) by norm_num,
    Real.rpow_mul_natCast]
  rw [show u ^ (1 / 2 : ℝ) = Real.sqrt u by
    exact (Real.sqrt_eq_rpow u).symm]
  exact hu

private theorem sqrt_le_one_half_of_le_one_quarter
    {u : ℝ} (huUpper : u ≤ 1 / 4) :
    Real.sqrt u ≤ 1 / 2 := by
  have hsqrt := Real.sqrt_le_sqrt huUpper
  norm_num at hsqrt ⊢
  simpa using hsqrt

private theorem a2b_endpoint_polynomial_nonneg
    {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ 1 - 16 * r ^ 2 + 25 * r ^ 3 := by
  let a : ℝ := 32 / 75
  have hfactor :
      1 - 16 * r ^ 2 + 25 * r ^ 3 =
        12275 / 421875 + (r - a) ^ 2 * (25 * r + 16 / 3) := by
    dsimp only [a]
    ring
  rw [hfactor]
  positivity

private theorem a3b_upper_endpoint_polynomial_nonneg
    {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ 1 - 20 * r ^ 2 + 35 * r ^ 3 := by
  let a : ℝ := 8 / 21
  have hfactor :
      1 - 20 * r ^ 2 + 35 * r ^ 3 =
        301 / 9261 + (r - a) ^ 2 * (35 * r + 20 / 3) := by
    dsimp only [a]
    ring
  rw [hfactor]
  positivity

/-- The `AB` exponent lies below Pintz's coefficient-one-half target on the
initial logarithmic-scale range, uniformly for `3/4 ≤ sigma ≤ 1`. -/
theorem pintz_threeQuarter_AB_exponent_le
    {sigma epsilon tau : ℝ}
    (hsigmaUpper : sigma ≤ 1) (hsigmaLower : 3 / 4 ≤ sigma)
    (hepsilon : 0 ≤ epsilon) (htauLow : 2 ≤ tau)
    (htauHigh : tau ≤ 9 / 4) :
    (tau + 3) / 6 ≤ pintzNearOneUnweightedTarget sigma epsilon tau := by
  let u : ℝ := 1 - sigma
  let r : ℝ := Real.sqrt u
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have huUpper : u ≤ 1 / 4 := by dsimp only [u]; linarith
  have hr : 0 ≤ r := Real.sqrt_nonneg u
  have hrUpper : r ≤ 1 / 2 :=
    sqrt_le_one_half_of_le_one_quarter huUpper
  have hrsq : r ^ 2 = u := by
    dsimp only [r]
    exact Real.sq_sqrt hu
  have hrcube : r ^ 3 = u ^ (3 / 2 : ℝ) := by
    rw [threeQuarter_three_halves_eq_sqrt_cube hu]
  have hrsqLe : r ^ 2 ≤ r / 2 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrUpper)]
  have hpoly : 0 ≤ 1 / 8 - r ^ 2 + (9 / 8 : ℝ) * r ^ 3 := by
    have hdiff :
        1 / 8 - r ^ 2 + (9 / 8 : ℝ) * r ^ 3 - 1 / 64 =
          (1 / 2 - r) *
            (7 / 32 + (7 / 16 : ℝ) * r - (9 / 8 : ℝ) * r ^ 2) := by
      ring
    have hbracket :
        0 ≤ 7 / 32 + (7 / 16 : ℝ) * r - (9 / 8 : ℝ) * r ^ 2 := by
      nlinarith
    have hprod : 0 ≤ (1 / 2 - r) *
        (7 / 32 + (7 / 16 : ℝ) * r - (9 / 8 : ℝ) * r ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hrUpper) hbracket
    linarith
  have htauCoeff : -1 / 6 + r ^ 3 / 2 ≤ 0 := by
    have hcubeUpper : r ^ 3 ≤ 1 / 8 := by
      nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hrUpper)]
    linarith
  have hendpoint :
      (9 / 4 + 3) / 6 ≤
        1 - u + (9 / 4) * ((1 / 2 : ℝ) * u ^ (3 / 2 : ℝ)) := by
    rw [← hrcube, ← hrsq]
    norm_num at hpoly ⊢
    linarith
  unfold pintzNearOneUnweightedTarget
  dsimp only [u] at hendpoint
  have hmove := mul_nonneg (sub_nonneg.mpr htauHigh)
    (neg_nonneg.mpr htauCoeff)
  nlinarith

/-- The classical pair `(1/14,11/14)` covers the middle range needed for
Pintz's zeta input down to `sigma = 3/4`. -/
theorem pintz_threeQuarter_A2B_exponent_le
    {sigma epsilon tau : ℝ}
    (hsigmaUpper : sigma ≤ 1) (hsigmaLower : 3 / 4 ≤ sigma)
    (hepsilon : 0 ≤ epsilon) (htauLow : 9 / 4 ≤ tau)
    (htauHigh : tau ≤ 25 / 8) :
    (tau + 10) / 14 ≤
      pintzNearOneUnweightedTarget sigma epsilon tau := by
  let u : ℝ := 1 - sigma
  let r : ℝ := Real.sqrt u
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have huUpper : u ≤ 1 / 4 := by dsimp only [u]; linarith
  have hr : 0 ≤ r := Real.sqrt_nonneg u
  have hrUpper : r ≤ 1 / 2 :=
    sqrt_le_one_half_of_le_one_quarter huUpper
  have hrsq : r ^ 2 = u := by
    dsimp only [r]
    exact Real.sq_sqrt hu
  have hrcube : r ^ 3 = u ^ (3 / 2 : ℝ) := by
    rw [threeQuarter_three_halves_eq_sqrt_cube hu]
  have hcubeUpper : r ^ 3 ≤ 1 / 8 := by
    nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hrUpper)]
  have htauCoeff : -1 / 14 + r ^ 3 / 2 ≤ 0 := by linarith
  have hpoly := a2b_endpoint_polynomial_nonneg hr
  have hendpoint :
      (25 / 8 + 10) / 14 ≤
        1 - u + (25 / 8) * ((1 / 2 : ℝ) * u ^ (3 / 2 : ℝ)) := by
    rw [← hrcube, ← hrsq]
    norm_num at hpoly ⊢
    linarith
  unfold pintzNearOneUnweightedTarget
  dsimp only [u] at hendpoint
  have hmove := mul_nonneg (sub_nonneg.mpr htauHigh)
    (neg_nonneg.mpr htauCoeff)
  nlinarith

/-- The native `A^3B` exponent covers the remaining compact gap between the
classical `A^2B` range and Heath--Brown's large-scale estimate. -/
theorem pintz_threeQuarter_A3B_exponent_le
    {sigma epsilon tau : ℝ}
    (hsigmaUpper : sigma ≤ 1) (hsigmaLower : 3 / 4 ≤ sigma)
    (hepsilon : 0 ≤ epsilon) (htauLow : 25 / 8 ≤ tau)
    (htauHigh : tau ≤ 7 / 2) :
    (tau + 25) / 30 ≤
      pintzNearOneUnweightedTarget sigma epsilon tau := by
  let u : ℝ := 1 - sigma
  let r : ℝ := Real.sqrt u
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have huUpper : u ≤ 1 / 4 := by dsimp only [u]; linarith
  have hr : 0 ≤ r := Real.sqrt_nonneg u
  have hrsq : r ^ 2 = u := by
    dsimp only [r]
    exact Real.sq_sqrt hu
  have hrcube : r ^ 3 = u ^ (3 / 2 : ℝ) := by
    rw [threeQuarter_three_halves_eq_sqrt_cube hu]
  have hLowerPoly := a2b_endpoint_polynomial_nonneg hr
  have hUpperPoly := a3b_upper_endpoint_polynomial_nonneg hr
  have hAtLower :
      (25 / 8 + 25) / 30 ≤
        1 - u + (25 / 8) * ((1 / 2 : ℝ) * u ^ (3 / 2 : ℝ)) := by
    rw [← hrcube, ← hrsq]
    norm_num at hLowerPoly ⊢
    linarith
  have hAtUpper :
      (7 / 2 + 25) / 30 ≤
        1 - u + (7 / 2) * ((1 / 2 : ℝ) * u ^ (3 / 2 : ℝ)) := by
    rw [← hrcube, ← hrsq]
    norm_num at hUpperPoly ⊢
    linarith
  let a : ℝ := (28 - 8 * tau) / 3
  let b : ℝ := (8 * tau - 25) / 3
  have ha : 0 ≤ a := by dsimp only [a]; linarith
  have hb : 0 ≤ b := by dsimp only [b]; linarith
  have hab : a + b = 1 := by dsimp only [a, b]; ring
  have hcomb := add_nonneg (mul_nonneg ha (sub_nonneg.mpr hAtLower))
    (mul_nonneg hb (sub_nonneg.mpr hAtUpper))
  unfold pintzNearOneUnweightedTarget
  dsimp only [u, a, b] at hcomb
  nlinarith

#print axioms pintz_threeQuarter_AB_exponent_le
#print axioms pintz_threeQuarter_A2B_exponent_le
#print axioms pintz_threeQuarter_A3B_exponent_le

end

end GafniTao
