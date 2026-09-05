import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Heath--Brown's zeta exponent: the exact one-variable optimization

This file isolates the calculus-free numerical step in the proof of
Heath--Brown's Theorem 5.  If `u = 1 - sigma` and
`tau = log t / log N`, partial summation from Theorem 4 produces the
exponent

`u / tau - 49 / (80 * tau ^ 3)`.

The source maximizes this at `tau = sqrt (147 / (80*u))`.  We prove the
uniform inequality directly by a nonnegative factorization, retaining the
published constant `kappa = 8*sqrt(15)/63`.
-/

namespace GafniTao

noncomputable section

/-- The constant in Heath--Brown (2017), Theorem 5, equation (1.10). -/
noncomputable def heathBrownZetaKappa : ℝ :=
  8 * Real.sqrt 15 / 63

/-- The positive critical point for the normalized cubic optimization. -/
noncomputable def heathBrownZetaCriticalTau : ℝ :=
  Real.sqrt (147 / 80)

theorem heathBrownZetaCriticalTau_pos :
    0 < heathBrownZetaCriticalTau := by
  unfold heathBrownZetaCriticalTau
  positivity

theorem heathBrownZetaCriticalTau_sq :
    heathBrownZetaCriticalTau ^ 2 = 147 / 80 := by
  unfold heathBrownZetaCriticalTau
  exact Real.sq_sqrt (by norm_num)

/-- The radical form printed in the paper agrees with the coefficient
obtained from the critical point. -/
theorem heathBrownZetaKappa_eq_two_div_three_critical :
    heathBrownZetaKappa = 2 / (3 * heathBrownZetaCriticalTau) := by
  have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have hq : heathBrownZetaCriticalTau ^ 2 = 147 / 80 :=
    heathBrownZetaCriticalTau_sq
  have hs15 : 0 < Real.sqrt 15 := Real.sqrt_pos.2 (by norm_num)
  have hqpos := heathBrownZetaCriticalTau_pos
  have hprodSq :
      (Real.sqrt 15 * heathBrownZetaCriticalTau) ^ 2 = 441 / 16 := by
    rw [mul_pow, h15, hq]
    norm_num
  have hprod : Real.sqrt 15 * heathBrownZetaCriticalTau = 21 / 4 := by
    have hprodNonneg : 0 ≤ Real.sqrt 15 * heathBrownZetaCriticalTau := by
      positivity
    nlinarith
  unfold heathBrownZetaKappa
  field_simp
  nlinarith

theorem fortyNine_div_eighty_eq_kappa_critical_cube_half :
    (49 / 80 : ℝ) =
      heathBrownZetaKappa * heathBrownZetaCriticalTau ^ 3 / 2 := by
  have hk := heathBrownZetaKappa_eq_two_div_three_critical
  have hq := heathBrownZetaCriticalTau_sq
  have hqpos := heathBrownZetaCriticalTau_pos
  rw [hk]
  field_simp
  nlinarith

/-- The normalized cubic has its global minimum zero at the source critical
point.  This exact factorization avoids any appeal to an external optimizer. -/
theorem heathBrown_normalized_cubic_nonneg (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ heathBrownZetaKappa * v ^ 3 - v ^ 2 + 49 / 80 := by
  let q := heathBrownZetaCriticalTau
  have hq : 0 < q := heathBrownZetaCriticalTau_pos
  have hk : heathBrownZetaKappa = 2 / (3 * q) := by
    simpa only [q] using heathBrownZetaKappa_eq_two_div_three_critical
  have ha : (49 / 80 : ℝ) = heathBrownZetaKappa * q ^ 3 / 2 := by
    simpa only [q] using fortyNine_div_eighty_eq_kappa_critical_cube_half
  have hfactor :
      heathBrownZetaKappa * v ^ 3 - v ^ 2 + 49 / 80 =
        heathBrownZetaKappa * (v - q) ^ 2 * (v + q / 2) := by
    rw [ha, hk]
    field_simp
    ring
  rw [hfactor]
  have hkpos : 0 < heathBrownZetaKappa := by
    unfold heathBrownZetaKappa
    positivity
  positivity

/-- Exact source optimization.  This is the exponent comparison used after
dyadic partial summation in the proof of Heath--Brown's zeta bound. -/
theorem heathBrown_zeta_exponent_le
    {u tau : ℝ} (hu : 0 ≤ u) (htau : 0 < tau) :
    u / tau - 49 / (80 * tau ^ 3) ≤
      heathBrownZetaKappa * u ^ (3 / 2 : ℝ) := by
  let r := Real.sqrt u
  let v := r * tau
  have hr : 0 ≤ r := Real.sqrt_nonneg u
  have hrSq : r ^ 2 = u := by
    dsimp only [r]
    exact Real.sq_sqrt hu
  have hv : 0 ≤ v := mul_nonneg hr htau.le
  have hcubic := heathBrown_normalized_cubic_nonneg v hv
  have htauCube : 0 < tau ^ 3 := pow_pos htau 3
  have hrpow : u ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * (3 : ℕ) by norm_num,
      Real.rpow_mul_natCast]
    rw [show u ^ (1 / 2 : ℝ) = Real.sqrt u by
      exact (Real.sqrt_eq_rpow u).symm]
    exact hu
  rw [hrpow]
  dsimp only [v] at hcubic
  have hidentity :
      (heathBrownZetaKappa * r ^ 3 -
          (u / tau - 49 / (80 * tau ^ 3))) * (80 * tau ^ 3) =
        80 * (heathBrownZetaKappa * (r * tau) ^ 3 -
          (r * tau) ^ 2 + 49 / 80) := by
    rw [← hrSq]
    field_simp [htau.ne']
    ring
  have hprod :
      0 ≤ (heathBrownZetaKappa * r ^ 3 -
          (u / tau - 49 / (80 * tau ^ 3))) * (80 * tau ^ 3) := by
    rw [hidentity]
    positivity
  have hfactor : 0 < 80 * tau ^ 3 := by positivity
  have hdiff :
      0 ≤ heathBrownZetaKappa * r ^ 3 -
        (u / tau - 49 / (80 * tau ^ 3)) := by
    exact nonneg_of_mul_nonneg_left hprod hfactor
  linarith

#print axioms heathBrown_zeta_exponent_le

end

end GafniTao
