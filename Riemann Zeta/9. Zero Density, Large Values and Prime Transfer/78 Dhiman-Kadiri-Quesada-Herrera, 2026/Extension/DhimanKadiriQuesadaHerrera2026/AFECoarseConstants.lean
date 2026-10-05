import DhimanKadiriQuesadaHerrera2026.AFEUniformMax

namespace DhimanKadiriQuesadaHerrera2026

/-- A rational logarithm enclosure used only through its kernel proof. -/
theorem log_two_le_seven_tenths : Real.log 2 ≤ 7 / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 10) 5
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The decimal scale logarithm has a simple rigorous rational enclosure. -/
theorem log_ten_le_seven_thirds : Real.log 10 ≤ 7 / 3 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 3) 7
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The complete cubic C₁ has a uniform rational bound on the entire sigma interval. -/
theorem chiC1_le_nine_twentieths {σ t₀ : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 6 ≤ t₀) : chiC1 σ t₀ ≤ 9 / 20 := by
  have htpos : 0 < t₀ := by linarith
  have ha : 0 ≤ 1 - σ := by linarith [hσ.2]
  have hb : 0 ≤ σ - 1 / 2 := by linarith [hσ.1]
  have hab : (1 - σ) * (σ - 1 / 2) ≤ 1 / 16 := by nlinarith [sq_nonneg (σ - 3 / 4)]
  have haa : (1 - σ) ^ 2 ≤ 1 / 4 := by nlinarith [hσ.1, hσ.2]
  have hp : 1 / 2 + 2 / Real.pi ≤ 7 / 6 := by
    have h : 2 / Real.pi ≤ (2 / 3 : ℝ) := (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
    linarith
  have hq : (Real.pi / 2) ^ 2 + (1 - σ) / (2 * t₀) ≤ 12107 / 4800 := by
    have hdiv : (1 - σ) / (2 * t₀) ≤ 1 / 24 :=
      (div_le_iff₀ (by positivity : 0 < 2 * t₀)).mpr (by linarith [hσ.1])
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hfirst := mul_le_mul haa hp (by positivity : 0 ≤ 1 / 2 + 2 / Real.pi) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hsecond := mul_le_mul hab hq (by positivity : 0 ≤ (Real.pi / 2) ^ 2 + (1 - σ) / (2 * t₀)) (by norm_num : (0 : ℝ) ≤ 1 / 16)
  unfold chiC1
  linarith

/-- The exponential factor C₂ is controlled uniformly by a rational function of the threshold. -/
theorem chiC2_le_one_add {t₀ : ℝ} (ht : 6 ≤ t₀) : chiC2 t₀ ≤ 1 + 1 / (6 * t₀) := by
  have htpos : 0 < t₀ := by linarith
  have he : 1 / (12 * t₀) + 1 / (90 * t₀ ^ 3) ≤ 1 / (11 * t₀) := by
    have hden : 132 * t₀ ≤ 90 * t₀ ^ 3 := by
      have hsq : (132 : ℝ) ≤ 90 * t₀ ^ 2 := by nlinarith [sq_nonneg (t₀ - 6)]
      have hm := mul_le_mul_of_nonneg_right hsq htpos.le
      nlinarith only [hm]
    have hh := one_div_le_one_div_of_le (show 0 < 132 * t₀ by positivity) hden
    have hid : 1 / (12 * t₀) + 1 / (132 * t₀) = 1 / (11 * t₀) := by
      field_simp
      ring
    rw [← hid]
    linarith
  have hsmall : 1 / (11 * t₀) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hb := Real.exp_bound_div_one_sub_of_interval (by positivity : 0 ≤ 1 / (11 * t₀)) hsmall
  have hrat : 1 / (1 - 1 / (11 * t₀)) ≤ 1 + 1 / (6 * t₀) := by
    apply (div_le_iff₀ (sub_pos.mpr hsmall)).mpr
    field_simp
    nlinarith
  exact (Real.exp_le_exp.mpr he).trans (hb.trans hrat)

/-- The negative exponential at every source threshold has an explicit rational bound. -/
theorem exp_neg_pi_threshold_le {t₀ : ℝ} (ht : 6 ≤ t₀) :
    Real.exp (-Real.pi * t₀) ≤ 1 / (24 * t₀) := by
  have htpos : 0 < t₀ := by linarith
  have h := Real.pow_div_factorial_le_exp (Real.pi * t₀) (show 0 ≤ Real.pi * t₀ by positivity) 2
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at h
  have hp : 24 * t₀ ≤ Real.exp (Real.pi * t₀) := by
    have hs : 9 * t₀ ^ 2 ≤ (Real.pi * t₀) ^ 2 := by nlinarith [mul_nonneg (sq_nonneg t₀) (show 0 ≤ Real.pi ^ 2 - 9 by nlinarith [Real.pi_gt_three])]
    nlinarith [sq_nonneg (t₀ - 6)]
  rw [neg_mul, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (show 0 < 24 * t₀ by positivity) hp

/-- The literal C₀ is at most 1+1/t₀ on the whole closed source sigma interval. -/
theorem chiC0_le_one_add_inv {σ t₀ : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 6 ≤ t₀) : chiC0 σ t₀ ≤ 1 + 1 / t₀ := by
  have htpos : 0 < t₀ := by linarith
  have hc := chiC1_nonneg hσ htpos
  have hb := chiC1_le_nine_twentieths hσ ht
  rw [chiC0_eq htpos]
  have hmul : chiC2 t₀ * (1 + Real.exp (-Real.pi * t₀)) * (1 + chiC1 σ t₀ / t₀) ≤
      (1 + 1 / (6 * t₀)) * (1 + 1 / (24 * t₀)) * (1 + (9 / 20) / t₀) := by
    gcongr
    · exact chiC2_le_one_add ht
    · exact exp_neg_pi_threshold_le ht
  apply hmul.trans
  have hid : (1 + 1 / t₀) - (1 + 1 / (6 * t₀)) * (1 + 1 / (24 * t₀)) *
      (1 + (9 / 20) / t₀) = (984 * t₀ ^ 2 - 290 * t₀ - 9) / (2880 * t₀ ^ 3) := by
    field_simp
    ring
  have hn : 0 ≤ 984 * t₀ ^ 2 - 290 * t₀ - 9 := by nlinarith [sq_nonneg (t₀ - 6)]
  have hd := div_nonneg hn (show 0 ≤ 2880 * t₀ ^ 3 by positivity)
  rw [← hid] at hd
  linarith


/-- The complete B₀ numerator and exponential denominator give a uniform inverse-square bound. -/
theorem afeSourceB0_le_inv_sq {σ t₀ : ℝ} (hσ : 0 ≤ σ) (ht₀ : 2 * Real.pi ≤ t₀) :
    afeSourceB0 σ t₀ ≤ 1 / t₀ ^ 2 := by
  have ht : 6 ≤ t₀ := by linarith [Real.pi_gt_three]
  have htpos : 0 < t₀ := by linarith
  let z : ℝ := t₀ / (2 * Real.pi)
  have hz : 1 ≤ z := (one_le_div (by positivity : 0 < 2 * Real.pi)).mpr ht₀
  have hzpos : 0 < z := by linarith
  have hsz : Real.sqrt z ≤ z := (Real.sqrt_le_iff).mpr ⟨hzpos.le, by nlinarith⟩
  have hlz : Real.log z ≤ z := by linarith [Real.log_le_sub_one_of_pos hzpos]
  have hn0 := mul_le_mul hsz hlz (Real.log_nonneg hz) hzpos.le
  have hr := Real.rpow_le_self_of_one_le hz (show (1 - σ) / 2 ≤ 1 by linarith)
  have hzt : 6 * z ≤ t₀ := by
    have hid : (2 * Real.pi) * z = t₀ := by dsimp only [z]; field_simp
    nlinarith [mul_nonneg hzpos.le (show 0 ≤ 2 * Real.pi - 6 by linarith [Real.pi_gt_three])]
  have hzsq : (6 * z) ^ 2 ≤ t₀ ^ 2 := pow_le_pow_left₀ (by positivity) hzt 2
  have hn : (1 / 2) * Real.sqrt z * Real.log z + z ^ ((1 - σ) / 2) ≤ t₀ ^ 2 := by
    nlinarith [sq_nonneg (z - 1)]
  have hen := exp_neg_pi_threshold_le ht
  have hen2 : Real.exp (-Real.pi * t₀) ≤ 1 / 2 := by
    have hh : 1 / (24 * t₀) ≤ (1 / 2 : ℝ) := (div_le_iff₀ (by positivity)).mpr (by linarith)
    exact hen.trans hh
  have hden : 1 / 2 ≤ 1 - Real.exp (-Real.pi * t₀) := by linarith
  have he4 := Real.pow_div_factorial_le_exp (Real.pi * t₀) (by positivity) 4
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at he4
  have hpi4 : (48 : ℝ) ≤ Real.pi ^ 4 := by nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi ^ 2 - 9)]
  have hh : 2 * t₀ ^ 4 ≤ Real.exp (Real.pi * t₀) := by
    have hp := mul_le_mul_of_nonneg_right hpi4 (pow_nonneg htpos.le 4)
    rw [mul_pow] at he4
    nlinarith only [hp, he4]
  have he : Real.exp (-Real.pi * t₀) ≤ 1 / (2 * t₀ ^ 4) := by
    rw [neg_mul, Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (show 0 < 2 * t₀ ^ 4 by positivity) hh
  have hNnon : 0 ≤ (1 / 2) * Real.sqrt z * Real.log z + z ^ ((1 - σ) / 2) := by
    have hl := Real.log_nonneg hz
    positivity
  unfold afeSourceB0
  change (((1 / 2) * Real.sqrt z * Real.log z + z ^ ((1 - σ) / 2)) * Real.exp (-Real.pi * t₀)) /
    (1 - Real.exp (-Real.pi * t₀)) ≤ _
  calc
    _ ≤ (t₀ ^ 2 * (1 / (2 * t₀ ^ 4))) / (1 / 2) := by
      apply div_le_div₀ (show 0 ≤ t₀ ^ 2 * (1 / (2 * t₀ ^ 4)) by positivity)
        (mul_le_mul hn he (Real.exp_pos _).le (sq_nonneg t₀)) (by norm_num) hden
    _ = 1 / t₀ ^ 2 := by
      field_simp


/-- A parameter-explicit rational majorant for every term of A₀ on 0≤sigma≤1. -/
theorem afeSourceA0_le_rational {σ h t₀ P L H T : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hP : 0 < P) (hPpi : P ≤ Real.pi) (hL : Real.log 2 ≤ L)
    (hH : 0 < H) (hHh : H ≤ h) (hT : 0 < T) (hTt : T ≤ t₀) :
    afeSourceA0 σ h t₀ ≤
  1 / 4 + ((2 / 3) + (7 / 2) * L - 3 / 2) / P +
    115 / (27 * P ^ 2) +
    7 / (4 * P * H) + 3 / (4 * P * (H + 1)) + 7 / (8 * P * H ^ 2) +
    (23 * ((1 : ℝ) + 1)) / (9 * P ^ 2 * H) + (115 * (1 : ℝ)) / (54 * P ^ 3 * H ^ 2) +
    (1 : ℝ) / (4 * T) + (1 : ℝ) / (2 * P * H ^ 2 * T) +
    ((1 : ℝ) * L) / (2 * P * T) + (3 * (1 : ℝ)) / (4 * P * (H + 1) * T) +
    (23 * (1 : ℝ) * ((1 : ℝ) + 1)) / (9 * P ^ 2 * H * T) := by
  have hh : 0 < h := hH.trans_le hHh
  have ht : 0 < t₀ := hT.trans_le hTt
  have hX : H ≤ max h (Real.sqrt (t₀ / (2 * Real.pi))) := hHh.trans (le_max_left _ _)
  have hXp : 0 < max h (Real.sqrt (t₀ / (2 * Real.pi))) := hH.trans_le hX
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hl
    exact hl
  have hbase : 0 ≤ Real.eulerMascheroniConstant + (7 / 2) * Real.log 2 - 3 / 2 := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hL0 : 0 ≤ L := hl0.trans hL
  unfold afeSourceA0
  dsimp only
  gcongr <;> linarith [Real.eulerMascheroniConstant_lt_two_thirds, hσ.1, hσ.2]

/-- A coarse global A₀ bound suffices for the bounded smaller-cutoff branch. -/
theorem afeSourceA0_le_three {σ h t₀ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hh : 3 / 2 ≤ h) (ht : 6 ≤ t₀) : afeSourceA0 σ h t₀ ≤ 3 := by
  have h := afeSourceA0_le_rational hσ (P := 3) (L := 1) (H := 3 / 2) (T := 6)
    (by norm_num) Real.pi_gt_three.le
    (by linarith [log_two_le_seven_tenths]) (by norm_num) hh (by norm_num) ht
  norm_num at h
  linarith

/-- Large cutoffs give a sharper rational A₀ bound, with no decimal optimization. -/
theorem afeSourceA0_le_five_fourths {σ h t₀ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hh : 100 ≤ h) (ht : 60000 ≤ t₀) : afeSourceA0 σ h t₀ ≤ 5 / 4 := by
  have h := afeSourceA0_le_rational hσ (P := 25 / 8) (L := 7 / 10) (H := 100) (T := 60000)
    (by norm_num) (by linarith [Real.pi_gt_d2]) log_two_le_seven_tenths
    (by norm_num) hh (by norm_num) ht
  norm_num at h
  linarith


/-- Both complete source coefficients are below six when the smaller cutoff is at most 100. -/
theorem afe_small_coefficients_le_six {σ z : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hz : 1 ≤ z) (hzmax : z ≤ 100) :
    Real.log z / Real.pi + afeSourceA0 σ (3 / 2) (2 * Real.pi) +
      chiC0 σ (2 * Real.pi) * afeSourceB0 σ (2 * Real.pi) ≤ 6 ∧
    chiC0 σ (2 * Real.pi) / Real.pi * Real.log z +
      afeSourceA0 (1 - σ) (3 / 2) (2 * Real.pi) * chiC0 σ (2 * Real.pi) +
        afeSourceB0 (1 - σ) (2 * Real.pi) ≤ 6 := by
  have hs : σ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hσ.1], hσ.2⟩
  have hdual : 1 - σ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have ht : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hzpos : 0 < z := by linarith
  have hl0 : 0 ≤ Real.log z := Real.log_nonneg hz
  have hl : Real.log z ≤ 14 / 3 := by
    have hh := Real.log_le_log hzpos hzmax
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [log_ten_le_seven_thirds]
  have hlp : Real.log z / Real.pi ≤ 14 / 9 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_three]
  have hA := afeSourceA0_le_three hs (h := 3 / 2) (by norm_num) ht
  have hAd := afeSourceA0_le_three hdual (h := 3 / 2) (by norm_num) ht
  have hC : chiC0 σ (2 * Real.pi) ≤ 7 / 6 := by
    have hh := chiC0_le_one_add_inv hσ ht
    have hi : 1 / (2 * Real.pi) ≤ (1 / 6 : ℝ) := one_div_le_one_div_of_le (by norm_num) ht
    linarith
  have hB (v : ℝ) (hv : 0 ≤ v) : afeSourceB0 v (2 * Real.pi) ≤ 1 / 36 := by
    have hh := afeSourceB0_le_inv_sq hv (le_refl (2 * Real.pi))
    have hi : 1 / (2 * Real.pi) ^ 2 ≤ (1 / 36 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith [Real.pi_pos])
    exact hh.trans hi
  have hCB := mul_le_mul hC (hB σ hs.1) (afeSourceB0_nonneg σ (le_refl _)) (by norm_num : (0 : ℝ) ≤ 7 / 6)
  have hAC := mul_le_mul hAd hC (chiC0_pos hσ (by positivity)).le (by norm_num : (0 : ℝ) ≤ 3)
  have hClog := mul_le_mul hC hlp (div_nonneg hl0 Real.pi_pos.le) (by norm_num : (0 : ℝ) ≤ 7 / 6)
  have he : chiC0 σ (2 * Real.pi) * (Real.log z / Real.pi) = chiC0 σ (2 * Real.pi) / Real.pi * Real.log z := by ring
  rw [he] at hClog
  constructor <;> linarith [hB (1 - σ) hdual.1]

/-- Both complete source coefficients are below six on the large-cutoff range through one million. -/
theorem afe_large_coefficients_le_six {σ z : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hz : 1 ≤ z) (hzmax : z ≤ 1000000) :
    Real.log z / Real.pi + afeSourceA0 σ 100 60000 + chiC0 σ 60000 * afeSourceB0 σ 60000 ≤ 6 ∧
    chiC0 σ 60000 / Real.pi * Real.log z + afeSourceA0 (1 - σ) 100 60000 * chiC0 σ 60000 +
      afeSourceB0 (1 - σ) 60000 ≤ 6 := by
  have hs : σ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hσ.1], hσ.2⟩
  have hdual : 1 - σ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have ht : 2 * Real.pi ≤ (60000 : ℝ) := by linarith [Real.pi_lt_four]
  have hzpos : 0 < z := by linarith
  have hl0 : 0 ≤ Real.log z := Real.log_nonneg hz
  have hl : Real.log z ≤ 14 := by
    have hh := Real.log_le_log hzpos hzmax
    rw [show (1000000 : ℝ) = 10 ^ 6 by norm_num, Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [log_ten_le_seven_thirds]
  have hlp : Real.log z / Real.pi ≤ 14 / 3 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_three]
  have hA := afeSourceA0_le_five_fourths hs (h := 100) (t₀ := 60000) (by norm_num) (by norm_num)
  have hAd := afeSourceA0_le_five_fourths hdual (h := 100) (t₀ := 60000) (by norm_num) (by norm_num)
  have hC : chiC0 σ 60000 ≤ 60001 / 60000 := by
    have hh := chiC0_le_one_add_inv hσ (t₀ := 60000) (by norm_num)
    norm_num at hh
    exact hh
  have hB (v : ℝ) (hv : 0 ≤ v) : afeSourceB0 v 60000 ≤ 1 / 3600000000 := by
    simpa only [show (60000 : ℝ) ^ 2 = 3600000000 by norm_num] using afeSourceB0_le_inv_sq hv ht
  have hCB := mul_le_mul hC (hB σ hs.1) (afeSourceB0_nonneg σ ht) (by norm_num : (0 : ℝ) ≤ 60001 / 60000)
  have hAC := mul_le_mul hAd hC (chiC0_pos hσ (by norm_num : (0 : ℝ) < 60000)).le (by norm_num : (0 : ℝ) ≤ 5 / 4)
  have hClog := mul_le_mul hC hlp (div_nonneg hl0 Real.pi_pos.le) (by norm_num : (0 : ℝ) ≤ 60001 / 60000)
  have he : chiC0 σ 60000 * (Real.log z / Real.pi) = chiC0 σ 60000 / Real.pi * Real.log z := by ring
  rw [he] at hClog
  constructor <;> linarith [hB (1 - σ) hdual.1]

/-- Positive half-integer cutoffs at least one are automatically at least three halves. -/
theorem half_integer_ge_three_halves {x : ℝ} (hx : 1 ≤ x)
    (hh : ∃ k : ℤ, x = (k : ℝ) + 1 / 2) : 3 / 2 ≤ x := by
  obtain ⟨k, rfl⟩ := hh
  have hk : (0 : ℤ) < k := by exact_mod_cast (show (0 : ℝ) < (k : ℝ) by linarith)
  have hk1 : (1 : ℤ) ≤ k := by omega
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  linarith

/-- The physical product scale supplies the larger threshold when both cutoffs exceed 100. -/
theorem afe_height_ge_sixty_thousand {t x y : ℝ} (hx : 100 ≤ x) (hy : 100 ≤ y)
    (hscale : 2 * Real.pi * x * y = |t|) : 60000 ≤ |t| := by
  have hp : (10000 : ℝ) ≤ x * y := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * Real.pi by positivity)
  rw [← mul_assoc, hscale] at hm
  linarith [Real.pi_gt_three]


/-- The source constant-six consequence holds in the direct region throughout min(x,y)≤10⁶. -/
theorem afe_constant_six_direct {σ t x y : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (ht : 2 * Real.pi ≤ |t|) (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hymax : y ≤ 1000000)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      6 * (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  have hx3 := half_integer_ge_three_halves hx hxhalf
  have hy3 := half_integer_ge_three_halves hy hyhalf
  have hypos : 0 < y := by linarith
  have hp : 0 ≤ (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) := Real.rpow_nonneg (by positivity) _
  have hq : 0 ≤ y ^ (σ - 1) := Real.rpow_nonneg hypos.le _
  by_cases hsmall : y ≤ 100
  · have hs := afe_second_uniform_direct hσ (le_refl (2 * Real.pi)) ht
      (le_refl (3 / 2 : ℝ)) hx3 hy3 hyx hxhalf hyhalf hscale
    exact hs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (afe_small_coefficients_le_six hσ hy hsmall).1 hp) hq)
  · have hy100 : 100 ≤ y := (lt_of_not_ge hsmall).le
    have hx100 : 100 ≤ x := hy100.trans hyx
    have hs := afe_second_uniform_direct hσ
      (show 2 * Real.pi ≤ (60000 : ℝ) by linarith [Real.pi_lt_four])
      (afe_height_ge_sixty_thousand hx100 hy100 hscale) (by norm_num : (3 / 2 : ℝ) ≤ 100)
      hx100 hy100 hyx hxhalf hyhalf hscale
    exact hs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (afe_large_coefficients_le_six hσ hy hymax).1 hp) hq)

/-- The same literal constant-six consequence holds in the reflected region, including sigma=1. -/
theorem afe_constant_six_reflected {σ t x y : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (ht : 2 * Real.pi ≤ |t|) (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x ≤ y)
    (hxmax : x ≤ 1000000)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤ 6 * x ^ (-σ) := by
  have hx3 := half_integer_ge_three_halves hx hxhalf
  have hy3 := half_integer_ge_three_halves hy hyhalf
  have hxpos : 0 < x := by linarith
  have hp : 0 ≤ x ^ (-σ) := Real.rpow_nonneg hxpos.le _
  by_cases hsmall : x ≤ 100
  · have hs := afe_second_uniform_reflected hσ (le_refl (2 * Real.pi)) ht
      (le_refl (3 / 2 : ℝ)) hx3 hy3 hxy hxhalf hyhalf hscale
    exact hs.trans (mul_le_mul_of_nonneg_right (afe_small_coefficients_le_six hσ hx hsmall).2 hp)
  · have hx100 : 100 ≤ x := (lt_of_not_ge hsmall).le
    have hy100 : 100 ≤ y := hx100.trans hxy
    have hs := afe_second_uniform_reflected hσ
      (show 2 * Real.pi ≤ (60000 : ℝ) by linarith [Real.pi_lt_four])
      (afe_height_ge_sixty_thousand hx100 hy100 hscale) (by norm_num : (3 / 2 : ℝ) ≤ 100)
      hx100 hy100 hxy hxhalf hyhalf hscale
    exact hs.trans (mul_le_mul_of_nonneg_right (afe_large_coefficients_le_six hσ hx hxmax).2 hp)

/-- Both branches of the literal constant-six AFE consequence, using positive absolute height in real powers. -/
theorem afe_constant_six {σ t x y : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (ht : 2 * Real.pi ≤ |t|) (hx : 1 ≤ x) (hy : 1 ≤ y) (hmin : min x y ≤ 1000000)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      if x < y then 6 * x ^ (-σ) else
        6 * (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  split_ifs with hxy
  · rw [min_eq_left hxy.le] at hmin
    exact afe_constant_six_reflected hσ ht hx hy hxy.le hmin hxhalf hyhalf hscale
  · have hyx := le_of_not_gt hxy
    rw [min_eq_right hyx] at hmin
    exact afe_constant_six_direct hσ ht hx hy hyx hmin hxhalf hyhalf hscale

end DhimanKadiriQuesadaHerrera2026
