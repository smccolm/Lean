import GafniTao.HeathBrownEPHalfZetaExponent

/-!
# The conductor-scale exponent in Heath--Brown's zeta estimate

On the logarithmic block range `1 ≤ tau ≤ 2`, the B-process and the
shifted Weyl estimate meet at `tau = 9/5`.  This file proves that their
common worst exponent is still bounded by the coefficient-one-half
Heath--Brown exponent throughout the source range `0 ≤ u ≤ 1/6`.
-/

namespace GafniTao

noncomputable section

/-- The common exponent at the transition `tau = 9/5` is dominated by the
Heath--Brown `u^(3/2)` exponent on the full Pintz range. -/
theorem heathBrownHalf_middle_transition_exponent_le
    {u : ℝ} (hu0 : 0 ≤ u) (hu6 : u ≤ 1 / 6) :
    5 * u / 9 - 1 / 18 ≤
      heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ) := by
  let r := Real.sqrt u
  let q := Real.sqrt 6
  let y := q * r
  have hr0 : 0 ≤ r := Real.sqrt_nonneg u
  have hrSq : r ^ 2 = u := by
    dsimp only [r]
    exact Real.sq_sqrt hu0
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hqSq : q ^ 2 = 6 := by
    dsimp only [q]
    norm_num
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hySq : y ^ 2 = 6 * u := by
    dsimp only [y]
    rw [mul_pow, hqSq, hrSq]
  have hy1 : y ≤ 1 := by
    have hySqLe : y ^ 2 ≤ 1 ^ 2 := by nlinarith
    nlinarith
  have hquad : 2 * y ^ 2 - 3 * y - 3 ≤ 0 := by
    nlinarith [sq_nonneg (y - 1)]
  have hpoly : 0 ≤ 2 * y ^ 3 - 5 * y ^ 2 + 3 := by
    have hfactor :
        2 * y ^ 3 - 5 * y ^ 2 + 3 =
          (y - 1) * (2 * y ^ 2 - 3 * y - 3) := by ring
    rw [hfactor]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hquad
  have hrpow : u ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * (3 : ℕ) by norm_num,
      Real.rpow_mul_natCast]
    rw [show u ^ (1 / 2 : ℝ) = Real.sqrt u by
      exact (Real.sqrt_eq_rpow u).symm]
    exact hu0
  have hscaled :
      18 * (heathBrownHalfZetaKappa * r ^ 3 -
        (5 * u / 9 - 1 / 18)) =
        (2 * y ^ 3 - 5 * y ^ 2 + 3) / 3 := by
    have hprodSq : (Real.sqrt 6 * r) ^ 2 = 6 * u := by
      rw [mul_pow]
      norm_num
      rw [hrSq]
    have hprodCube : (Real.sqrt 6 * r) ^ 3 =
        6 * Real.sqrt 6 * r ^ 3 := by
      rw [mul_pow]
      have hs6 : (Real.sqrt 6) ^ 2 = 6 := by norm_num
      calc
        (Real.sqrt 6) ^ 3 * r ^ 3 =
            ((Real.sqrt 6) ^ 2 * Real.sqrt 6) * r ^ 3 := by ring
        _ = 6 * Real.sqrt 6 * r ^ 3 := by rw [hs6]
    dsimp only [heathBrownHalfZetaKappa, y, q]
    rw [hprodSq, hprodCube]
    nlinarith
  rw [hrpow]
  nlinarith

/-- On the lower conductor-scale range, the B-process exponent increases up
to its value at `tau = 9/5`. -/
theorem heathBrownHalf_middle_B_exponent_le
    {u tau : ℝ} (hu0 : 0 ≤ u) (hu6 : u ≤ 1 / 6)
    (htau1 : 1 ≤ tau) (htau : tau ≤ 9 / 5) :
    1 / 2 - (1 - u) / tau ≤
      heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ) := by
  have htau0 : 0 < tau := lt_of_lt_of_le zero_lt_one htau1
  have huOne : u ≤ 1 := by linarith
  have hmono :
      1 / 2 - (1 - u) / tau ≤ 5 * u / 9 - 1 / 18 := by
    have hquot : 5 * (1 - u) / 9 ≤ (1 - u) / tau := by
      apply (le_div_iff₀ htau0).2
      have hnonneg : 0 ≤ 1 - u := by linarith
      nlinarith
    linarith
  exact hmono.trans (heathBrownHalf_middle_transition_exponent_le hu0 hu6)

/-- On the upper conductor-scale range, the shifted Weyl exponent decreases
from its value at `tau = 9/5`. -/
theorem heathBrownHalf_middle_Weyl_exponent_le
    {u tau : ℝ} (hu0 : 0 ≤ u) (hu6 : u ≤ 1 / 6)
    (htau : 9 / 5 ≤ tau) :
    (u + 1 / 2) / tau - 1 / 3 ≤
      heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ) := by
  have htau0 : 0 < tau := by nlinarith
  have hmono :
      (u + 1 / 2) / tau - 1 / 3 ≤ 5 * u / 9 - 1 / 18 := by
    have hquot : (u + 1 / 2) / tau ≤ 5 * (u + 1 / 2) / 9 := by
      apply (div_le_iff₀ htau0).2
      have hpos : 0 ≤ u + 1 / 2 := by linarith
      nlinarith
    linarith
  exact hmono.trans (heathBrownHalf_middle_transition_exponent_le hu0 hu6)

#print axioms heathBrownHalf_middle_transition_exponent_le
#print axioms heathBrownHalf_middle_B_exponent_le
#print axioms heathBrownHalf_middle_Weyl_exponent_le

end

end GafniTao
