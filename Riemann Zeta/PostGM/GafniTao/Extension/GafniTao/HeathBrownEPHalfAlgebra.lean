import GafniTao.HeathBrownEP1Algebra

/-!
# A sufficient Heath--Brown logarithmic-sum exponent

Pintz's use of Heath--Brown Theorem 5 only needs an exponential-sum
saving strong enough to make the shifted zeta integral negligible.  The
constant `1/2` is sufficient.  These lemmas verify a covering of every
logarithmic scale `tau >= 2` by the frozen `AB` estimate and the already
native Heath--Brown k-th derivative theorem.

The large-scale choice is `k = ceil tau + 1`.  It keeps `k - tau` between
one and two and makes each of the three derivative-test terms save at least
`1 / (2 tau^2)` once `tau >= 4`.
-/

namespace GafniTao

noncomputable section

/-- The frozen `(1/6,2/3)` estimate supplies the required saving on the
low logarithmic range. -/
theorem heathBrown_half_AB_range
    {tau : ℝ} (hlow : 2 ≤ tau) (hhigh : tau ≤ 5 / 2) :
    (tau - 3) / 6 ≤ -1 / (2 * tau ^ 2) := by
  have htau : 0 < tau := by linarith
  have hpoly : tau ^ 2 * (3 - tau) ≥ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlow)
      (mul_nonneg (sub_nonneg.mpr hhigh) (by linarith : 0 ≤ tau + 1 / 2))]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6)
    (by positivity : 0 < 2 * tau ^ 2)]
  nlinarith

/-- The first term of the `k=4` derivative estimate. -/
theorem heathBrown_half_kfour_first
    {tau : ℝ} (hlow : 5 / 2 ≤ tau) (hhigh : tau ≤ 7 / 2) :
    (tau - 4) / 12 ≤ -1 / (2 * tau ^ 2) := by
  have htau : 0 < tau := by linarith
  have hpoly : tau ^ 2 * (4 - tau) ≥ 6 := by
    have hleft : 0 ≤ (tau - 5 / 2) * (7 / 2 - tau) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_nonneg (tau - 3)]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 12)
    (by positivity : 0 < 2 * tau ^ 2)]
  nlinarith

/-- The constant term of the `k=4` derivative estimate. -/
theorem heathBrown_half_kfour_second
    {tau : ℝ} (hlow : 5 / 2 ≤ tau) :
    (-1 / 12 : ℝ) ≤ -1 / (2 * tau ^ 2) := by
  have htau : 0 < tau := by linarith
  have hsquare : 6 ≤ tau ^ 2 := by nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 2 * tau ^ 2)).2
  nlinarith

/-- The third term of the `k=4` derivative estimate. -/
theorem heathBrown_half_kfour_third
    {tau : ℝ} (hlow : 5 / 2 ≤ tau) :
    -tau / 24 ≤ -1 / (2 * tau ^ 2) := by
  have htau : 0 < tau := by linarith
  have hcube : 12 ≤ tau ^ 3 := by nlinarith [sq_nonneg (tau - 5 / 2)]
  apply (le_div_iff₀ (by positivity : 0 < 2 * tau ^ 2)).2
  nlinarith

/-- The `k=5` derivative estimate bridges the short interval before the
ceiling-based choice becomes uniformly convenient. -/
theorem heathBrown_half_kfive_first
    {tau : ℝ} (hlow : 7 / 2 ≤ tau) (hhigh : tau ≤ 4) :
    (tau - 5) / 20 ≤ -1 / (2 * tau ^ 2) := by
  have htau : 0 < tau := by linarith
  have hpoly : tau ^ 2 * (5 - tau) ≥ 10 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlow)
      (mul_nonneg (sub_nonneg.mpr hhigh) (by linarith : 0 ≤ tau - 3))]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 20)
    (by positivity : 0 < 2 * tau ^ 2)]
  nlinarith

theorem heathBrown_half_kfive_second
    {tau : ℝ} (hlow : 7 / 2 ≤ tau) :
    (-1 / 20 : ℝ) ≤ -1 / (2 * tau ^ 2) := by
  have htau : 0 < tau := by linarith
  have hsquare : 10 ≤ tau ^ 2 := by nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 2 * tau ^ 2)).2
  nlinarith

theorem heathBrown_half_kfive_third
    {tau : ℝ} (hlow : 7 / 2 ≤ tau) :
    -tau / 50 ≤ -1 / (2 * tau ^ 2) := by
  have htau : 0 < tau := by linarith
  have hcube : 25 ≤ tau ^ 3 := by nlinarith [sq_nonneg (tau - 7 / 2)]
  apply (le_div_iff₀ (by positivity : 0 < 2 * tau ^ 2)).2
  nlinarith

/-- Derivative order used in the unbounded logarithmic range. -/
def heathBrownHalfOrder (tau : ℝ) : ℕ := Nat.ceil tau + 1

theorem heathBrownHalfOrder_bounds
    {tau : ℝ} (htau : 4 ≤ tau) :
    5 ≤ heathBrownHalfOrder tau ∧
      (heathBrownHalfOrder tau : ℝ) - 2 < tau ∧
      tau ≤ (heathBrownHalfOrder tau : ℝ) - 1 := by
  have htauNonneg : 0 ≤ tau := by linarith
  have hceilLower : tau ≤ (Nat.ceil tau : ℝ) := Nat.le_ceil tau
  have hceilUpper : (Nat.ceil tau : ℝ) < tau + 1 :=
    Nat.ceil_lt_add_one htauNonneg
  have hnatFour : 4 ≤ Nat.ceil tau := by
    exact_mod_cast htau.trans hceilLower
  unfold heathBrownHalfOrder
  constructor
  · omega
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

/-- The first two derivative-test savings for `k=ceil(tau)+1`. -/
theorem heathBrown_half_large_first_second
    {tau : ℝ} (htau : 4 ≤ tau) :
    1 / (2 * tau ^ 2) ≤
      ((heathBrownHalfOrder tau : ℝ) - tau) /
        ((heathBrownHalfOrder tau : ℝ) *
          ((heathBrownHalfOrder tau : ℝ) - 1)) ∧
    1 / (2 * tau ^ 2) ≤
      1 / ((heathBrownHalfOrder tau : ℝ) *
        ((heathBrownHalfOrder tau : ℝ) - 1)) := by
  obtain ⟨hk, hkLower, hkUpper⟩ := heathBrownHalfOrder_bounds htau
  let k : ℝ := heathBrownHalfOrder tau
  have htauPos : 0 < tau := by linarith
  have hkPos : 0 < k := by dsimp only [k]; positivity
  have hkOnePos : 0 < k - 1 := by
    have : (5 : ℝ) ≤ k := by
      dsimp only [k]
      exact_mod_cast hk
    linarith
  have hgap : 1 ≤ k - tau := by dsimp only [k] at hkUpper ⊢; linarith
  have hkHigh : k < tau + 2 := by dsimp only [k] at hkLower ⊢; linarith
  have hdenHigh : k * (k - 1) ≤ 2 * tau ^ 2 := by
    have hbasic : (tau + 2) * (tau + 1) ≤ 2 * tau ^ 2 := by
      nlinarith [sq_nonneg (tau - 4)]
    nlinarith [mul_pos hkPos hkOnePos]
  have hdenPos : 0 < k * (k - 1) := mul_pos hkPos hkOnePos
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 2 * tau ^ 2) hdenPos]
    nlinarith
  · exact one_div_le_one_div_of_le (by positivity) hdenHigh

/-- The third derivative-test saving for `k=ceil(tau)+1`. -/
theorem heathBrown_half_large_third
    {tau : ℝ} (htau : 4 ≤ tau) :
    1 / (2 * tau ^ 2) ≤
      2 * tau /
        ((heathBrownHalfOrder tau : ℝ) ^ 2 *
          ((heathBrownHalfOrder tau : ℝ) - 1)) := by
  obtain ⟨hk, hkLower, _hkUpper⟩ := heathBrownHalfOrder_bounds htau
  let k : ℝ := heathBrownHalfOrder tau
  have htauPos : 0 < tau := by linarith
  have hkPos : 0 < k := by dsimp only [k]; positivity
  have hkOnePos : 0 < k - 1 := by
    have : (5 : ℝ) ≤ k := by
      dsimp only [k]
      exact_mod_cast hk
    linarith
  have hkHigh : k < tau + 2 := by dsimp only [k] at hkLower ⊢; linarith
  have hpoly : (tau + 2) ^ 2 * (tau + 1) ≤ 4 * tau ^ 3 := by
    nlinarith [sq_nonneg (tau - 4), mul_nonneg
      (sq_nonneg (tau - 4)) (by linarith : 0 ≤ tau + 3)]
  have hden : k ^ 2 * (k - 1) ≤ 4 * tau ^ 3 := by
    have hkSq : k ^ 2 ≤ (tau + 2) ^ 2 := by nlinarith
    have hkOne : k - 1 ≤ tau + 1 := by linarith
    calc
      k ^ 2 * (k - 1) ≤ (tau + 2) ^ 2 * (tau + 1) :=
        mul_le_mul hkSq hkOne (by positivity) (by positivity)
      _ ≤ 4 * tau ^ 3 := hpoly
  rw [div_le_div_iff₀ (by positivity : 0 < 2 * tau ^ 2)
    (mul_pos (sq_pos_of_pos hkPos) hkOnePos)]
  nlinarith

#print axioms heathBrown_half_AB_range
#print axioms heathBrown_half_kfour_first
#print axioms heathBrown_half_kfive_first
#print axioms heathBrownHalfOrder_bounds
#print axioms heathBrown_half_large_first_second
#print axioms heathBrown_half_large_third

end

end GafniTao
