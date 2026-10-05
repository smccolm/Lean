import DhimanKadiriQuesadaHerrera2026.AFECoarseConstants
import DhimanKadiriQuesadaHerrera2026.AFEDigammaNumerics

namespace DhimanKadiriQuesadaHerrera2026

/-- The logarithm enclosure is certified by the finite rational series with its proved tail. -/
theorem log_two_le_precise : Real.log 2 ≤ 693148 / 1000000 := by
  have h := log_le_logRationalUpper (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 8
  rw [show (1 + (1 / 3 : ℝ)) / (1 - 1 / 3) = 2 by norm_num] at h
  have hr : logRationalUpper 8 (1 / 3) ≤ (693148 / 1000000 : ℝ) := by
    norm_num [logRationalUpper, logRationalLower, Finset.sum_range_succ]
  exact h.trans hr

/-- Euler's constant is bounded by the existing finite Euler remainder and a certified logarithm. -/
theorem euler_constant_le_precise : Real.eulerMascheroniConstant ≤ 577216 / 1000000 := by
  have h := euler_constant_upper_finite 15
  have hl := logRationalLower_le (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 8
  rw [show (1 + (1 / 3 : ℝ)) / (1 - 1 / 3) = 2 by norm_num] at hl
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  norm_num only [Nat.cast_ofNat, show (15 : ℝ) + 1 = 16 by norm_num] at h
  rw [h16] at h
  have hr : (∑ n ∈ Finset.range 15, 1 / ((n : ℝ) + 1)) - 4 * logRationalLower 8 (1 / 3) +
      1 / (2 * 16) + 1 / (12 * 16 ^ 2) ≤ (577216 / 1000000 : ℝ) := by
    norm_num [logRationalLower, Finset.sum_range_succ]
  linarith

/-- The exact exponential band endpoint exceeds the required rational cutoff. -/
theorem exp_ten_ge_twenty_two_thousand : (22000 : ℝ) ≤ Real.exp 10 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10) 32
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Every band k≥11 lies above the rational cutoff used in the uniform certificate. -/
theorem afeBandLower_ge_twenty_two_thousand {k : ℕ} (hk : 11 ≤ k) :
    (22000 : ℝ) ≤ afeBandLower k := by
  have hkr : (11 : ℝ) ≤ k := by exact_mod_cast hk
  have he : (22000 : ℝ) ≤ Real.exp ((k : ℝ) - 1) :=
    exp_ten_ge_twenty_two_thousand.trans (Real.exp_le_exp.mpr (by linarith))
  have hf : (22000 : ℕ) ≤ ⌊Real.exp ((k : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat] using he)
  have hfr : (22000 : ℝ) ≤ (⌊Real.exp ((k : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
  unfold afeBandLower
  linarith

/-- The physical source x₀ at threshold 10¹⁰ exceeds an independently certified rational cutoff. -/
theorem afe_x0_ge_precise (h : ℝ) : (39890 : ℝ) ≤ max h (Real.sqrt (10000000000 / (2 * Real.pi))) := by
  apply le_trans _ (le_max_right _ _)
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  nlinarith [Real.pi_lt_d4]

/-- A rational majorant retains independent lower bounds for h and x₀, and an explicit Euler enclosure. -/
theorem afeSourceA0_le_precise_rational {σ h t₀ P L H T X G : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hP : 0 < P) (hPpi : P ≤ Real.pi) (hL : Real.log 2 ≤ L)
    (hH : 0 < H) (hHh : H ≤ h) (hT : 0 < T) (hTt : T ≤ t₀) (hXpos : 0 < X)
    (hXmax : X ≤ max h (Real.sqrt (t₀ / (2 * Real.pi))))
    (hG : Real.eulerMascheroniConstant ≤ G) :
    afeSourceA0 σ h t₀ ≤
  1 / 4 + (G + (7 / 2) * L - 3 / 2) / P +
    115 / (27 * P ^ 2) +
    7 / (4 * P * H) + 3 / (4 * P * (H + 1)) + 7 / (8 * P * H ^ 2) +
    (23 * ((1 : ℝ) + 1)) / (9 * P ^ 2 * X) + (115 * (1 : ℝ)) / (54 * P ^ 3 * X ^ 2) +
    (1 : ℝ) / (4 * T) + (1 : ℝ) / (2 * P * H ^ 2 * T) +
    ((1 : ℝ) * L) / (2 * P * T) + (3 * (1 : ℝ)) / (4 * P * (H + 1) * T) +
    (23 * (1 : ℝ) * ((1 : ℝ) + 1)) / (9 * P ^ 2 * X * T) := by
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
  gcongr <;> linarith [hσ.1, hσ.2]


/-- The complete A₀ is below the certified decimal on every sigma and every band k≥11. -/
theorem afeSourceA0_le_band_constant {σ h : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hh : 22000 ≤ h) : afeSourceA0 σ h 10000000000 ≤ 1160097 / 1000000 := by
  have he := afeSourceA0_le_precise_rational hσ (P := 3141592 / 1000000) (L := 693148 / 1000000)
    (H := 22000) (T := 10000000000) (X := 39890) (G := 577216 / 1000000)
    (by norm_num) (by linarith [Real.pi_gt_d6]) log_two_le_precise (by norm_num) hh
    (by norm_num) (le_refl _) (by norm_num) (afe_x0_ge_precise h) euler_constant_le_precise
  norm_num at he
  linarith


/-- The exact global excess chi maximum inherits the proved inverse-threshold bound. -/
theorem afeDelta0_le_inv {t₀ : ℝ} (ht : 6 ≤ t₀) : afeDelta0 t₀ ≤ 1 / t₀ := by
  have hn : afeSigmaStrip.Nonempty := ⟨1, by norm_num [afeSigmaStrip]⟩
  have hs : sSup ((fun σ => chiC0 σ t₀) '' afeSigmaStrip) ≤ 1 + 1 / t₀ := by
    apply csSup_le (hn.image _)
    rintro _ ⟨σ, hσ, rfl⟩
    exact chiC0_le_one_add_inv hσ ht
  dsimp only [afeDelta0]
  linarith

/-- Both exact global E₀ maxima have rational certificates on every band above the eleventh. -/
theorem afe_maxima_large_band_le {h : ℝ} (hh : 22000 ≤ h) :
    afeDirectMaximum h 10000000000 ≤ 1160097 / 1000000 +
      (1 + 1 / 10000000000) * (1 / 100000000000000000000) ∧
    afeReflectedMaximum h 10000000000 ≤ (1160097 / 1000000) *
      (1 + 1 / 10000000000) + 1 / 100000000000000000000 := by
  have hn : afeSigmaStrip.Nonempty := ⟨1, by norm_num [afeSigmaStrip]⟩
  have ht : 2 * Real.pi ≤ (10000000000 : ℝ) := by linarith [Real.pi_lt_four]
  have hC (σ : ℝ) (hσ : σ ∈ afeSigmaStrip) := chiC0_le_one_add_inv hσ (t₀ := 10000000000) (by norm_num)
  have hB (σ : ℝ) (hσ : 0 ≤ σ) : afeSourceB0 σ 10000000000 ≤ 1 / 100000000000000000000 := by
    simpa only [show (10000000000 : ℝ) ^ 2 = 100000000000000000000 by norm_num] using afeSourceB0_le_inv_sq hσ ht
  constructor
  · apply csSup_le (hn.image _)
    rintro _ ⟨σ, hσ, rfl⟩
    have hs : σ ∈ Set.Icc (0 : ℝ) 1 := ⟨by change 1 / 2 ≤ σ ∧ σ ≤ 1 at hσ; linarith [hσ.1], hσ.2⟩
    have hA := afeSourceA0_le_band_constant hs hh
    have hp := mul_le_mul (hC σ hσ) (hB σ hs.1) (afeSourceB0_nonneg σ ht)
      (by norm_num : (0 : ℝ) ≤ 1 + 1 / 10000000000)
    dsimp only [afeDirectE0]
    linarith
  · apply csSup_le (hn.image _)
    rintro _ ⟨σ, hσ, rfl⟩
    have hs : 1 - σ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hA := afeSourceA0_le_band_constant hs hh
    have hp := mul_le_mul hA (hC σ hσ) (chiC0_pos hσ (by norm_num : (0 : ℝ) < 10000000000)).le
      (by norm_num : (0 : ℝ) ≤ 1160097 / 1000000)
    have hb := hB (1 - σ) hs.1
    dsimp only [afeReflectedE0]
    linarith

/-- The unchanged displayed k/pi+1.1601 bound holds for both exact source constants on 11≤k≤50. -/
theorem afe_band_coefficients_large_k {k : ℕ} (hk : 11 ≤ k) (hkmax : k ≤ 50) :
    (k : ℝ) / Real.pi + afeDirectMaximum (afeBandLower k) 10000000000 ≤ (k : ℝ) / Real.pi + 1.1601 ∧
    (k : ℝ) * (1 + afeDelta0 10000000000) / Real.pi + afeReflectedMaximum (afeBandLower k) 10000000000 ≤
      (k : ℝ) / Real.pi + 1.1601 := by
  have hmax := afe_maxima_large_band_le (afeBandLower_ge_twenty_two_thousand hk)
  have hd := afeDelta0_le_inv (t₀ := 10000000000) (by norm_num)
  have hd0 := afeDelta0_nonneg (t₀ := 10000000000) (by norm_num)
  have hkr : (k : ℝ) ≤ 50 := by exact_mod_cast hkmax
  have hm := mul_le_mul hkr hd hd0 (by norm_num : (0 : ℝ) ≤ 50)
  have hterm : (k : ℝ) * afeDelta0 10000000000 / Real.pi ≤ 1 / 600000000 := by
    have hh := div_le_div₀ (show 0 ≤ (50 : ℝ) * (1 / 10000000000) by norm_num) hm
      (show (0 : ℝ) < 3 by norm_num) Real.pi_gt_three.le
    norm_num at hh
    exact hh
  have he : (k : ℝ) * (1 + afeDelta0 10000000000) / Real.pi =
      (k : ℝ) / Real.pi + (k : ℝ) * afeDelta0 10000000000 / Real.pi := by ring
  rw [he]
  constructor <;> linarith [hmax.1, hmax.2]

/-- The actual direct AFE consumes the certified unchanged large-k decimal bound. -/
theorem afe_large_k_direct {σ t x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 10000000000 ≤ |t|)
    (hk : 11 ≤ k) (hkmax : k ≤ 50) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hyx : y ≤ x)
    (hband : y ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      ((k : ℝ) / Real.pi + 1.1601) * (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  have hk1 : 1 ≤ k := by omega
  have hypos : 0 < y := by linarith [afeBandLower_ge hk1]
  have hs := afe_band_direct hσ (show 2 * Real.pi ≤ (10000000000 : ℝ) by linarith [Real.pi_lt_four])
    ht hk1 hx hy hyx hband hxhalf hyhalf hscale
  exact hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (afe_band_coefficients_large_k hk hkmax).1
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg hypos.le _))

/-- The actual reflected AFE consumes the certified unchanged large-k decimal bound. -/
theorem afe_large_k_reflected {σ t x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 10000000000 ≤ |t|)
    (hk : 11 ≤ k) (hkmax : k ≤ 50) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hxy : x ≤ y)
    (hband : x ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤ ((k : ℝ) / Real.pi + 1.1601) * x ^ (-σ) := by
  have hk1 : 1 ≤ k := by omega
  have hxpos : 0 < x := by linarith [afeBandLower_ge hk1]
  have hs := afe_band_reflected hσ (show 2 * Real.pi ≤ (10000000000 : ℝ) by linarith [Real.pi_lt_four])
    ht hk1 hx hy hxy hband hxhalf hyhalf hscale
  exact hs.trans (mul_le_mul_of_nonneg_right (afe_band_coefficients_large_k hk hkmax).2
    (Real.rpow_nonneg hxpos.le _))

end DhimanKadiriQuesadaHerrera2026
