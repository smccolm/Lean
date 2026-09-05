import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Zeta exponent from the coefficient-one-half exponential-sum estimate

For `u = 1 - σ` and `τ = log t / log N`, the exponential-sum saving
`1 / (2 * τ ^ 2)` gives the power of `t`

`u / τ - 1 / (2 * τ ^ 3)`.

This file proves its exact global maximum by factorization.  The resulting
coefficient `2 * sqrt 6 / 9` is slightly weaker than Heath--Brown's published
`8 * sqrt 15 / 63`, but it remains strictly below `1 / sqrt 3`; that strict
inequality is the numerical margin needed in Pintz's equations (4.9)--(4.11).
-/

namespace GafniTao

noncomputable section

/-- The zeta exponent produced by a logarithmic block saving of
`1 / (2 * τ ^ 2)`. -/
noncomputable def heathBrownHalfZetaKappa : ℝ :=
  2 * Real.sqrt 6 / 9

/-- The positive critical point of the normalized cubic optimization. -/
noncomputable def heathBrownHalfZetaCriticalTau : ℝ :=
  Real.sqrt (3 / 2)

theorem heathBrownHalfZetaCriticalTau_pos :
    0 < heathBrownHalfZetaCriticalTau := by
  unfold heathBrownHalfZetaCriticalTau
  positivity

theorem heathBrownHalfZetaCriticalTau_sq :
    heathBrownHalfZetaCriticalTau ^ 2 = 3 / 2 := by
  unfold heathBrownHalfZetaCriticalTau
  exact Real.sq_sqrt (by norm_num)

theorem heathBrownHalfZetaKappa_eq_two_div_three_critical :
    heathBrownHalfZetaKappa = 2 / (3 * heathBrownHalfZetaCriticalTau) := by
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hq : heathBrownHalfZetaCriticalTau ^ 2 = 3 / 2 :=
    heathBrownHalfZetaCriticalTau_sq
  have hs6 : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hqpos := heathBrownHalfZetaCriticalTau_pos
  have hprodSq :
      (Real.sqrt 6 * heathBrownHalfZetaCriticalTau) ^ 2 = 9 := by
    rw [mul_pow, h6, hq]
    norm_num
  have hprod : Real.sqrt 6 * heathBrownHalfZetaCriticalTau = 3 := by
    have hprodNonneg :
        0 ≤ Real.sqrt 6 * heathBrownHalfZetaCriticalTau := by
      positivity
    nlinarith
  unfold heathBrownHalfZetaKappa
  field_simp
  nlinarith

theorem one_half_eq_half_kappa_critical_cube :
    (1 / 2 : ℝ) =
      heathBrownHalfZetaKappa * heathBrownHalfZetaCriticalTau ^ 3 / 2 := by
  have hk := heathBrownHalfZetaKappa_eq_two_div_three_critical
  have hq := heathBrownHalfZetaCriticalTau_sq
  have hqpos := heathBrownHalfZetaCriticalTau_pos
  rw [hk]
  field_simp
  nlinarith

theorem heathBrownHalf_normalized_cubic_nonneg (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ heathBrownHalfZetaKappa * v ^ 3 - v ^ 2 + 1 / 2 := by
  let q := heathBrownHalfZetaCriticalTau
  have hq : 0 < q := heathBrownHalfZetaCriticalTau_pos
  have hk : heathBrownHalfZetaKappa = 2 / (3 * q) := by
    simpa only [q] using heathBrownHalfZetaKappa_eq_two_div_three_critical
  have ha : (1 / 2 : ℝ) = heathBrownHalfZetaKappa * q ^ 3 / 2 := by
    simpa only [q] using one_half_eq_half_kappa_critical_cube
  have hfactor :
      heathBrownHalfZetaKappa * v ^ 3 - v ^ 2 + 1 / 2 =
        heathBrownHalfZetaKappa * (v - q) ^ 2 * (v + q / 2) := by
    rw [ha, hk]
    field_simp
    ring
  rw [hfactor]
  have hkpos : 0 < heathBrownHalfZetaKappa := by
    unfold heathBrownHalfZetaKappa
    positivity
  positivity

/-- Exact optimization of the exponent produced by the coefficient-one-half
block estimate. -/
theorem heathBrownHalf_zeta_exponent_le
    {u tau : ℝ} (hu : 0 ≤ u) (htau : 0 < tau) :
    u / tau - 1 / (2 * tau ^ 3) ≤
      heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ) := by
  let r := Real.sqrt u
  let v := r * tau
  have hr : 0 ≤ r := Real.sqrt_nonneg u
  have hrSq : r ^ 2 = u := by
    dsimp only [r]
    exact Real.sq_sqrt hu
  have hv : 0 ≤ v := mul_nonneg hr htau.le
  have hcubic := heathBrownHalf_normalized_cubic_nonneg v hv
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
      (heathBrownHalfZetaKappa * r ^ 3 -
          (u / tau - 1 / (2 * tau ^ 3))) * (2 * tau ^ 3) =
        2 * (heathBrownHalfZetaKappa * (r * tau) ^ 3 -
          (r * tau) ^ 2 + 1 / 2) := by
    rw [← hrSq]
    field_simp [htau.ne']
    ring
  have hprod :
      0 ≤ (heathBrownHalfZetaKappa * r ^ 3 -
          (u / tau - 1 / (2 * tau ^ 3))) * (2 * tau ^ 3) := by
    rw [hidentity]
    positivity
  have hfactor : 0 < 2 * tau ^ 3 := by positivity
  have hdiff :
      0 ≤ heathBrownHalfZetaKappa * r ^ 3 -
        (u / tau - 1 / (2 * tau ^ 3)) := by
    exact nonneg_of_mul_nonneg_left hprod hfactor
  linarith

/-- The strict numerical margin used in Pintz's final small-gap estimate. -/
theorem heathBrownHalfZetaKappa_lt_inv_sqrt_three :
    heathBrownHalfZetaKappa < 1 / Real.sqrt 3 := by
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs6 : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hs3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs6sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  unfold heathBrownHalfZetaKappa
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 9) hs3]
  have hprodSq : (2 * Real.sqrt 6 * Real.sqrt 3) ^ 2 = 72 := by
    rw [mul_pow, mul_pow, hs6sq, hs3sq]
    norm_num
  have hprodNonneg : 0 ≤ 2 * Real.sqrt 6 * Real.sqrt 3 := by positivity
  nlinarith

#print axioms heathBrownHalf_zeta_exponent_le
#print axioms heathBrownHalfZetaKappa_lt_inv_sqrt_three

end

end GafniTao
