import DhimanKadiriQuesadaHerrera2026.AFEBandConstants

namespace DhimanKadiriQuesadaHerrera2026

/-- The logarithm enclosure is certified by the finite rational series with its proved tail. -/
theorem log_two_le_table_precision : Real.log 2 ≤ 693147181 / 1000000000 := by
  have h := log_le_logRationalUpper (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 12
  rw [show (1 + (1 / 3 : ℝ)) / (1 - 1 / 3) = 2 by norm_num] at h
  have hr : logRationalUpper 12 (1 / 3) ≤ (693147181 / 1000000000 : ℝ) := by
    norm_num [logRationalUpper, logRationalLower, Finset.sum_range_succ]
  exact h.trans hr

/-- Euler's constant is bounded by the existing finite Euler remainder and a certified logarithm. -/
theorem euler_constant_le_table_precision : Real.eulerMascheroniConstant ≤ 577215674 / 1000000000 := by
  have h := euler_constant_upper_finite 31
  have hl := logRationalLower_le (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 12
  rw [show (1 + (1 / 3 : ℝ)) / (1 - 1 / 3) = 2 by norm_num] at hl
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  norm_num only [Nat.cast_ofNat, show (31 : ℝ) + 1 = 32 by norm_num] at h
  rw [h32] at h
  have hr : (∑ n ∈ Finset.range 31, 1 / ((n : ℝ) + 1)) - 5 * logRationalLower 12 (1 / 3) +
      1 / (2 * 32) + 1 / (12 * 32 ^ 2) ≤ (577215674 / 1000000000 : ℝ) := by
    norm_num [logRationalLower, Finset.sum_range_succ]
  linarith

/-- The exact lower band endpoint is certified by a finite exponential series at k=15. -/
theorem afeBandLower_ge_fifteen {k : ℕ} (hk : 15 ≤ k) : (1200000 : ℝ) ≤ afeBandLower k := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 14) 48
  norm_num [Finset.sum_range_succ] at h
  have he0 : (1200000 : ℝ) ≤ Real.exp 14 := by linarith
  have hkr : (15 : ℝ) ≤ k := by exact_mod_cast hk
  have he : (1200000 : ℝ) ≤ Real.exp ((k : ℝ) - 1) := he0.trans (Real.exp_le_exp.mpr (by linarith))
  have hf : (1200000 : ℕ) ≤ ⌊Real.exp ((k : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat] using he)
  have hfr : (1200000 : ℝ) ≤ (⌊Real.exp ((k : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
  unfold afeBandLower
  linarith

/-- The exact lower band endpoint is certified by a finite exponential series at k=20. -/
theorem afeBandLower_ge_twenty {k : ℕ} (hk : 20 ≤ k) : (100000000 : ℝ) ≤ afeBandLower k := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 19) 40
  norm_num [Finset.sum_range_succ] at h
  have he0 : (100000000 : ℝ) ≤ Real.exp 19 := by linarith
  have hkr : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have he : (100000000 : ℝ) ≤ Real.exp ((k : ℝ) - 1) := he0.trans (Real.exp_le_exp.mpr (by linarith))
  have hf : (100000000 : ℕ) ≤ ⌊Real.exp ((k : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat] using he)
  have hfr : (100000000 : ℝ) ≤ (⌊Real.exp ((k : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
  unfold afeBandLower
  linarith

/-- Every A₀ term has an outward rational certificate above the fifteen band cutoff. -/
theorem afeSourceA0_le_fifteen_constant {σ h : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hh : 1200000 ≤ h) : afeSourceA0 σ h 10000000000 ≤ 116004753 / 100000000 := by
  have he := afeSourceA0_le_precise_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := 1200000) (T := 10000000000) (X := 1200000) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision (by norm_num) hh
    (by norm_num) (le_refl _) (by norm_num) (hh.trans (le_max_left _ _)) euler_constant_le_table_precision
  norm_num at he
  linarith

/-- Every A₀ term has an outward rational certificate above the twenty band cutoff. -/
theorem afeSourceA0_le_twenty_constant {σ h : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hh : 100000000 ≤ h) : afeSourceA0 σ h 10000000000 ≤ 1160046431 / 1000000000 := by
  have he := afeSourceA0_le_precise_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := 100000000) (T := 10000000000) (X := 100000000) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision (by norm_num) hh
    (by norm_num) (le_refl _) (by norm_num) (hh.trans (le_max_left _ _)) euler_constant_le_table_precision
  norm_num at he
  linarith


/-- A separately certified A₀ enclosure propagates through both exact attained E₀ maxima. -/
theorem afe_maxima_le_rational_A {h A : ℝ} (hA0 : 0 ≤ A)
    (hAall : ∀ σ ∈ Set.Icc (0 : ℝ) 1, afeSourceA0 σ h 10000000000 ≤ A) :
    afeDirectMaximum h 10000000000 ≤ A +
      (1 + 1 / 10000000000) * (1 / 100000000000000000000) ∧
    afeReflectedMaximum h 10000000000 ≤ (A) *
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
    have hA := hAall _ hs
    have hp := mul_le_mul (hC σ hσ) (hB σ hs.1) (afeSourceB0_nonneg σ ht)
      (by norm_num : (0 : ℝ) ≤ 1 + 1 / 10000000000)
    dsimp only [afeDirectE0]
    linarith
  · apply csSup_le (hn.image _)
    rintro _ ⟨σ, hσ, rfl⟩
    have hs : 1 - σ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hA := hAall _ hs
    have hp := mul_le_mul hA (hC σ hσ) (chiC0_pos hσ (by norm_num : (0 : ℝ) < 10000000000)).le
      hA0
    have hb := hB (1 - σ) hs.1
    dsimp only [afeReflectedE0]
    linarith


/-- On k≤50 the exact chi and exponential corrections cost less than 10⁻⁸ beyond any certified A₀≤2. -/
theorem afe_band_coefficients_le_A_margin {k : ℕ} {A : ℝ} (hk : k ≤ 50)
    (hA0 : 0 ≤ A) (hA2 : A ≤ 2)
    (hAall : ∀ σ ∈ Set.Icc (0 : ℝ) 1, afeSourceA0 σ (afeBandLower k) 10000000000 ≤ A) :
    (k : ℝ) / Real.pi + afeDirectMaximum (afeBandLower k) 10000000000 ≤ (k : ℝ) / Real.pi + A + 1 / 100000000 ∧
    (k : ℝ) * (1 + afeDelta0 10000000000) / Real.pi + afeReflectedMaximum (afeBandLower k) 10000000000 ≤
      (k : ℝ) / Real.pi + A + 1 / 100000000 := by
  have hmax := afe_maxima_le_rational_A hA0 hAall
  have hd := afeDelta0_le_inv (t₀ := 10000000000) (by norm_num)
  have hd0 := afeDelta0_nonneg (t₀ := 10000000000) (by norm_num)
  have hkr : (k : ℝ) ≤ 50 := by exact_mod_cast hk
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

/-- The eight unchanged displayed upper bounds in source Table 3. -/
noncomputable def afeTableThreeConstant (k : ℕ) : ℝ :=
  if k ≤ 15 then 5.9346959 else if k ≤ 20 then 7.5262442 else
  if k ≤ 25 then 9.1177936 else if k ≤ 30 then 10.7093431 else
  if k ≤ 35 then 12.3008925 else if k ≤ 40 then 13.8924419 else
  if k ≤ 45 then 15.4839914 else 17.0755408

/-- Every group endpoint in Table 3 has an outward certificate from the full analytic coefficients. -/
theorem afe_table_three_endpoint {K : ℕ} (hK : K ∈ ({15, 20, 25, 30, 35, 40, 45, 50} : Finset ℕ)) :
    (K : ℝ) / Real.pi + afeDirectMaximum (afeBandLower K) 10000000000 ≤ afeTableThreeConstant K ∧
    (K : ℝ) * (1 + afeDelta0 10000000000) / Real.pi + afeReflectedMaximum (afeBandLower K) 10000000000 ≤
      afeTableThreeConstant K := by
  have hpi (n : ℕ) : (n : ℝ) / Real.pi ≤ (n : ℝ) / (314159265358979323846 / 100000000000000000000) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by linarith [Real.pi_gt_d20])
  fin_cases hK
  · have hc := afe_band_coefficients_le_A_margin (k := 15) (A := 116004753 / 100000000) (by norm_num)
      (by norm_num) (by norm_num) (fun σ hσ => afeSourceA0_le_fifteen_constant hσ (afeBandLower_ge_fifteen (by norm_num)))
    have hr : (15 : ℝ) / (314159265358979323846 / 100000000000000000000) + 116004753 / 100000000 + 1 / 100000000 ≤
        afeTableThreeConstant 15 := by norm_num [afeTableThreeConstant]
    constructor <;> linarith [hc.1, hc.2, hpi 15]
  · have hc := afe_band_coefficients_le_A_margin (k := 20) (A := 1160046431 / 1000000000) (by norm_num)
      (by norm_num) (by norm_num) (fun σ hσ => afeSourceA0_le_twenty_constant hσ (afeBandLower_ge_twenty (by norm_num)))
    have hr : (20 : ℝ) / (314159265358979323846 / 100000000000000000000) + 1160046431 / 1000000000 + 1 / 100000000 ≤
        afeTableThreeConstant 20 := by norm_num [afeTableThreeConstant]
    constructor <;> linarith [hc.1, hc.2, hpi 20]
  · have hc := afe_band_coefficients_le_A_margin (k := 25) (A := 1160046431 / 1000000000) (by norm_num)
      (by norm_num) (by norm_num) (fun σ hσ => afeSourceA0_le_twenty_constant hσ (afeBandLower_ge_twenty (by norm_num)))
    have hr : (25 : ℝ) / (314159265358979323846 / 100000000000000000000) + 1160046431 / 1000000000 + 1 / 100000000 ≤
        afeTableThreeConstant 25 := by norm_num [afeTableThreeConstant]
    constructor <;> linarith [hc.1, hc.2, hpi 25]
  · have hc := afe_band_coefficients_le_A_margin (k := 30) (A := 1160046431 / 1000000000) (by norm_num)
      (by norm_num) (by norm_num) (fun σ hσ => afeSourceA0_le_twenty_constant hσ (afeBandLower_ge_twenty (by norm_num)))
    have hr : (30 : ℝ) / (314159265358979323846 / 100000000000000000000) + 1160046431 / 1000000000 + 1 / 100000000 ≤
        afeTableThreeConstant 30 := by norm_num [afeTableThreeConstant]
    constructor <;> linarith [hc.1, hc.2, hpi 30]
  · have hc := afe_band_coefficients_le_A_margin (k := 35) (A := 1160046431 / 1000000000) (by norm_num)
      (by norm_num) (by norm_num) (fun σ hσ => afeSourceA0_le_twenty_constant hσ (afeBandLower_ge_twenty (by norm_num)))
    have hr : (35 : ℝ) / (314159265358979323846 / 100000000000000000000) + 1160046431 / 1000000000 + 1 / 100000000 ≤
        afeTableThreeConstant 35 := by norm_num [afeTableThreeConstant]
    constructor <;> linarith [hc.1, hc.2, hpi 35]
  · have hc := afe_band_coefficients_le_A_margin (k := 40) (A := 1160046431 / 1000000000) (by norm_num)
      (by norm_num) (by norm_num) (fun σ hσ => afeSourceA0_le_twenty_constant hσ (afeBandLower_ge_twenty (by norm_num)))
    have hr : (40 : ℝ) / (314159265358979323846 / 100000000000000000000) + 1160046431 / 1000000000 + 1 / 100000000 ≤
        afeTableThreeConstant 40 := by norm_num [afeTableThreeConstant]
    constructor <;> linarith [hc.1, hc.2, hpi 40]
  · have hc := afe_band_coefficients_le_A_margin (k := 45) (A := 1160046431 / 1000000000) (by norm_num)
      (by norm_num) (by norm_num) (fun σ hσ => afeSourceA0_le_twenty_constant hσ (afeBandLower_ge_twenty (by norm_num)))
    have hr : (45 : ℝ) / (314159265358979323846 / 100000000000000000000) + 1160046431 / 1000000000 + 1 / 100000000 ≤
        afeTableThreeConstant 45 := by norm_num [afeTableThreeConstant]
    constructor <;> linarith [hc.1, hc.2, hpi 45]
  · have hc := afe_band_coefficients_le_A_margin (k := 50) (A := 1160046431 / 1000000000) (by norm_num)
      (by norm_num) (by norm_num) (fun σ hσ => afeSourceA0_le_twenty_constant hσ (afeBandLower_ge_twenty (by norm_num)))
    have hr : (50 : ℝ) / (314159265358979323846 / 100000000000000000000) + 1160046431 / 1000000000 + 1 / 100000000 ≤
        afeTableThreeConstant 50 := by norm_num [afeTableThreeConstant]
    constructor <;> linarith [hc.1, hc.2, hpi 50]


/-- Each entire integer group is covered by its certified endpoint and the analytic large-k bound. -/
theorem afe_table_three_group {k K : ℕ} (hk : 11 ≤ k) (hkK : k ≤ K) (hKmax : K ≤ 50)
    (hK : K ∈ ({15, 20, 25, 30, 35, 40, 45, 50} : Finset ℕ)) :
    (k : ℝ) / Real.pi + afeDirectMaximum (afeBandLower k) 10000000000 ≤ afeTableThreeConstant K ∧
    (k : ℝ) * (1 + afeDelta0 10000000000) / Real.pi + afeReflectedMaximum (afeBandLower k) 10000000000 ≤
      afeTableThreeConstant K := by
  by_cases heq : k = K
  · subst k
    exact afe_table_three_endpoint hK
  have hklt : k ≤ K - 1 := by omega
  have hkr : (k : ℝ) ≤ (K - 1 : ℕ) := by exact_mod_cast hklt
  have hp : (k : ℝ) / Real.pi ≤ (K - 1 : ℕ) / (314 / 100 : ℝ) :=
    div_le_div₀ (Nat.cast_nonneg _) hkr (by norm_num) (by linarith [Real.pi_gt_d2])
  have hr : (K - 1 : ℕ) / (314 / 100 : ℝ) + 1.1601 ≤ afeTableThreeConstant K := by
    fin_cases hK <;> norm_num [afeTableThreeConstant]
  have hc := afe_band_coefficients_large_k hk (hkK.trans hKmax)
  constructor <;> linarith [hc.1, hc.2]

/-- All forty integer values in the unchanged Table 3 are certified, with no sampled sigma values. -/
theorem afe_table_three_constants {k : ℕ} (hk : 11 ≤ k) (hkmax : k ≤ 50) :
    (k : ℝ) / Real.pi + afeDirectMaximum (afeBandLower k) 10000000000 ≤ afeTableThreeConstant k ∧
    (k : ℝ) * (1 + afeDelta0 10000000000) / Real.pi + afeReflectedMaximum (afeBandLower k) 10000000000 ≤
      afeTableThreeConstant k := by
  by_cases h15 : k ≤ 15
  · have hc := afe_table_three_group hk h15 (by norm_num) (by norm_num)
    simpa [afeTableThreeConstant, h15] using hc
  by_cases h20 : k ≤ 20
  · have hc := afe_table_three_group hk h20 (by norm_num) (by norm_num)
    simpa [afeTableThreeConstant, h15, h20] using hc
  by_cases h25 : k ≤ 25
  · have hc := afe_table_three_group hk h25 (by norm_num) (by norm_num)
    simpa [afeTableThreeConstant, h15, h20, h25] using hc
  by_cases h30 : k ≤ 30
  · have hc := afe_table_three_group hk h30 (by norm_num) (by norm_num)
    simpa [afeTableThreeConstant, h15, h20, h25, h30] using hc
  by_cases h35 : k ≤ 35
  · have hc := afe_table_three_group hk h35 (by norm_num) (by norm_num)
    simpa [afeTableThreeConstant, h15, h20, h25, h30, h35] using hc
  by_cases h40 : k ≤ 40
  · have hc := afe_table_three_group hk h40 (by norm_num) (by norm_num)
    simpa [afeTableThreeConstant, h15, h20, h25, h30, h35, h40] using hc
  by_cases h45 : k ≤ 45
  · have hc := afe_table_three_group hk h45 (by norm_num) (by norm_num)
    simpa [afeTableThreeConstant, h15, h20, h25, h30, h35, h40, h45] using hc
  have hc := afe_table_three_group hk hkmax (by norm_num) (by norm_num)
  simpa [afeTableThreeConstant, h15, h20, h25, h30, h35, h40, h45] using hc

/-- The actual direct AFE consumes the certified unchanged Table 3 bound. -/
theorem afe_table_three_direct {σ t x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 10000000000 ≤ |t|)
    (hk : 11 ≤ k) (hkmax : k ≤ 50) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hyx : y ≤ x)
    (hband : y ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      (afeTableThreeConstant k) * (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  have hk1 : 1 ≤ k := by omega
  have hypos : 0 < y := by linarith [afeBandLower_ge hk1]
  have hs := afe_band_direct hσ (show 2 * Real.pi ≤ (10000000000 : ℝ) by linarith [Real.pi_lt_four])
    ht hk1 hx hy hyx hband hxhalf hyhalf hscale
  exact hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (afe_table_three_constants hk hkmax).1
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg hypos.le _))

/-- The actual reflected AFE consumes the certified unchanged Table 3 bound. -/
theorem afe_table_three_reflected {σ t x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 10000000000 ≤ |t|)
    (hk : 11 ≤ k) (hkmax : k ≤ 50) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hxy : x ≤ y)
    (hband : x ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤ (afeTableThreeConstant k) * x ^ (-σ) := by
  have hk1 : 1 ≤ k := by omega
  have hxpos : 0 < x := by linarith [afeBandLower_ge hk1]
  have hs := afe_band_reflected hσ (show 2 * Real.pi ≤ (10000000000 : ℝ) by linarith [Real.pi_lt_four])
    ht hk1 hx hy hxy hband hxhalf hyhalf hscale
  exact hs.trans (mul_le_mul_of_nonneg_right (afe_table_three_constants hk hkmax).2
    (Real.rpow_nonneg hxpos.le _))

end DhimanKadiriQuesadaHerrera2026
