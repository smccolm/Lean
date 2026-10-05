import DhimanKadiriQuesadaHerrera2026.AFETableThree

namespace DhimanKadiriQuesadaHerrera2026

/-- A rational enclosure retains the actual upper sigma endpoint of each AFE branch. -/
theorem afeSourceA0_le_sigma_rational {σ h t₀ P L H T X G S : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) S)
    (hP : 0 < P) (hPpi : P ≤ Real.pi) (hL : Real.log 2 ≤ L)
    (hH : 0 < H) (hHh : H ≤ h) (hT : 0 < T) (hTt : T ≤ t₀) (hXpos : 0 < X)
    (hXmax : X ≤ max h (Real.sqrt (t₀ / (2 * Real.pi))))
    (hG : Real.eulerMascheroniConstant ≤ G) :
    afeSourceA0 σ h t₀ ≤
  1 / 4 + (G + (7 / 2) * L - 3 / 2) / P +
    115 / (27 * P ^ 2) +
    7 / (4 * P * H) + 3 / (4 * P * (H + 1)) + 7 / (8 * P * H ^ 2) +
    (23 * (S + 1)) / (9 * P ^ 2 * X) + (115 * S) / (54 * P ^ 3 * X ^ 2) +
    S / (4 * T) + S / (2 * P * H ^ 2 * T) +
    (S * L) / (2 * P * T) + (3 * S) / (4 * P * (H + 1) * T) +
    (23 * S * (S + 1)) / (9 * P ^ 2 * X * T) := by
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
  have hS0 : 0 ≤ S := hσ.1.trans hσ.2
  unfold afeSourceA0
  dsimp only
  gcongr <;> first | positivity | linarith [hσ.1, hσ.2]



/-- The larger cutoff at height 10¹⁰ is uniformly above this certified rational bound. -/
theorem afe_x0_ge_table_two (h : ℝ) : (39894 : ℝ) ≤ max h (Real.sqrt (10000000000 / (2 * Real.pi))) := by
  apply le_trans _ (le_max_right _ _)
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  nlinarith [Real.pi_lt_d20]

/-- The displayed exact half-integer lower cutoffs for k=1,...,10. -/
noncomputable def afeTableTwoLower (k : ℕ) : ℝ :=
  if k = 1 then 1.5 else if k = 2 then 2.5 else if k = 3 then 7.5 else
  if k = 4 then 20.5 else if k = 5 then 54.5 else if k = 6 then 148.5 else
  if k = 7 then 403.5 else if k = 8 then 1096.5 else if k = 9 then 2980.5 else 8103.5

/-- Each rational cutoff lies below the actual floor-defined band endpoint. -/
theorem afeTableTwoLower_le_band {k : ℕ} (hk : 1 ≤ k) (hkmax : k ≤ 10) :
    afeTableTwoLower k ≤ afeBandLower k := by
  interval_cases k
  · norm_num [afeTableTwoLower, afeBandLower]
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 48
    norm_num [Finset.sum_range_succ] at h
    have he : (2 : ℝ) ≤ Real.exp ((2 : ℝ) - 1) := by norm_num; linarith
    have hf : (2 : ℕ) ≤ ⌊Real.exp ((2 : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat, Nat.cast_one] using he)
    have hfr : (2 : ℝ) ≤ (⌊Real.exp ((2 : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
    norm_num [afeTableTwoLower, afeBandLower]
    simp only [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num] at hfr
    linarith
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 48
    norm_num [Finset.sum_range_succ] at h
    have he : (7 : ℝ) ≤ Real.exp ((3 : ℝ) - 1) := by norm_num; linarith
    have hf : (7 : ℕ) ≤ ⌊Real.exp ((3 : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat, Nat.cast_one] using he)
    have hfr : (7 : ℝ) ≤ (⌊Real.exp ((3 : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
    norm_num [afeTableTwoLower, afeBandLower]
    simp only [show ((3 : ℝ) - 1) = (2 : ℝ) by norm_num] at hfr
    linarith
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 48
    norm_num [Finset.sum_range_succ] at h
    have he : (20 : ℝ) ≤ Real.exp ((4 : ℝ) - 1) := by norm_num; linarith
    have hf : (20 : ℕ) ≤ ⌊Real.exp ((4 : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat, Nat.cast_one] using he)
    have hfr : (20 : ℝ) ≤ (⌊Real.exp ((4 : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
    norm_num [afeTableTwoLower, afeBandLower]
    simp only [show ((4 : ℝ) - 1) = (3 : ℝ) by norm_num] at hfr
    linarith
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 48
    norm_num [Finset.sum_range_succ] at h
    have he : (54 : ℝ) ≤ Real.exp ((5 : ℝ) - 1) := by norm_num; linarith
    have hf : (54 : ℕ) ≤ ⌊Real.exp ((5 : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat, Nat.cast_one] using he)
    have hfr : (54 : ℝ) ≤ (⌊Real.exp ((5 : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
    norm_num [afeTableTwoLower, afeBandLower]
    simp only [show ((5 : ℝ) - 1) = (4 : ℝ) by norm_num] at hfr
    linarith
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 48
    norm_num [Finset.sum_range_succ] at h
    have he : (148 : ℝ) ≤ Real.exp ((6 : ℝ) - 1) := by norm_num; linarith
    have hf : (148 : ℕ) ≤ ⌊Real.exp ((6 : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat, Nat.cast_one] using he)
    have hfr : (148 : ℝ) ≤ (⌊Real.exp ((6 : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
    norm_num [afeTableTwoLower, afeBandLower]
    simp only [show ((6 : ℝ) - 1) = (5 : ℝ) by norm_num] at hfr
    linarith
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6) 48
    norm_num [Finset.sum_range_succ] at h
    have he : (403 : ℝ) ≤ Real.exp ((7 : ℝ) - 1) := by norm_num; linarith
    have hf : (403 : ℕ) ≤ ⌊Real.exp ((7 : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat, Nat.cast_one] using he)
    have hfr : (403 : ℝ) ≤ (⌊Real.exp ((7 : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
    norm_num [afeTableTwoLower, afeBandLower]
    simp only [show ((7 : ℝ) - 1) = (6 : ℝ) by norm_num] at hfr
    linarith
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7) 48
    norm_num [Finset.sum_range_succ] at h
    have he : (1096 : ℝ) ≤ Real.exp ((8 : ℝ) - 1) := by norm_num; linarith
    have hf : (1096 : ℕ) ≤ ⌊Real.exp ((8 : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat, Nat.cast_one] using he)
    have hfr : (1096 : ℝ) ≤ (⌊Real.exp ((8 : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
    norm_num [afeTableTwoLower, afeBandLower]
    simp only [show ((8 : ℝ) - 1) = (7 : ℝ) by norm_num] at hfr
    linarith
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) 48
    norm_num [Finset.sum_range_succ] at h
    have he : (2980 : ℝ) ≤ Real.exp ((9 : ℝ) - 1) := by norm_num; linarith
    have hf : (2980 : ℕ) ≤ ⌊Real.exp ((9 : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat, Nat.cast_one] using he)
    have hfr : (2980 : ℝ) ≤ (⌊Real.exp ((9 : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
    norm_num [afeTableTwoLower, afeBandLower]
    simp only [show ((9 : ℝ) - 1) = (8 : ℝ) by norm_num] at hfr
    linarith
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9) 48
    norm_num [Finset.sum_range_succ] at h
    have he : (8103 : ℝ) ≤ Real.exp ((10 : ℝ) - 1) := by norm_num; linarith
    have hf : (8103 : ℕ) ≤ ⌊Real.exp ((10 : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat, Nat.cast_one] using he)
    have hfr : (8103 : ℝ) ≤ (⌊Real.exp ((10 : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
    norm_num [afeTableTwoLower, afeBandLower]
    simp only [show ((10 : ℝ) - 1) = (9 : ℝ) by norm_num] at hfr
    linarith

/-- A finite rational upper expression for the full A₀, used only through its analytic certificate. -/
noncomputable def afeTableRationalA (S H : ℝ) : ℝ :=
  let P : ℝ := 314159265358979323846 / 100000000000000000000
  let L : ℝ := 693147181 / 1000000000
  let G : ℝ := 577215674 / 1000000000
  let T : ℝ := 10000000000
  let X : ℝ := 39894
  1 / 4 + (G + (7 / 2) * L - 3 / 2) / P + 115 / (27 * P ^ 2) +
    7 / (4 * P * H) + 3 / (4 * P * (H + 1)) + 7 / (8 * P * H ^ 2) +
    23 * (S + 1) / (9 * P ^ 2 * X) + 115 * S / (54 * P ^ 3 * X ^ 2) +
    S / (4 * T) + S / (2 * P * H ^ 2 * T) + S * L / (2 * P * T) +
    3 * S / (4 * P * (H + 1) * T) + 23 * S * (S + 1) / (9 * P ^ 2 * X * T)

/-- The finite expression is an upper bound over the complete sigma interval and cutoff ray. -/
theorem afeSourceA0_le_table_rational {σ S H h : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) S)
    (hH : 0 < H) (hh : H ≤ h) : afeSourceA0 σ h 10000000000 ≤ afeTableRationalA S H := by
  exact afeSourceA0_le_sigma_rational hσ (by norm_num) (by linarith [Real.pi_gt_d20])
    log_two_le_table_precision hH hh (by norm_num) (le_refl _) (by norm_num)
    (afe_x0_ge_table_two h) euler_constant_le_table_precision

/-- Proposed outward Table 2 direct bounds, preserving every displayed bound that the certificate supports. -/
noncomputable def proposedTableTwoDirect (k : ℕ) : ℝ :=
  if k = 1 then 2.069011 else if k = 2 then 2.132269 else if k = 3 then 2.222300 else
  if k = 4 then 2.472239 else if k = 5 then 2.766226 else if k = 6 then 3.075280 else
  if k = 7 then 3.390202 else if k = 8 then 3.707265 else if k = 9 then 4.025116 else 4.343257

/-- Proposed outward Table 2 reflected bounds; these are not yet an adopted source repair. -/
noncomputable def proposedTableTwoReflected (k : ℕ) : ℝ :=
  if k = 1 then 2.069008 else if k = 2 then 2.132266 else if k = 3 then 2.222296 else
  if k = 4 then 2.472236 else if k = 5 then 2.766222 else if k = 6 then 3.075277 else
  if k = 7 then 3.390198 else if k = 8 then 3.707262 else if k = 9 then 4.025113 else 4.343254


/-- Separate full-interval A₀ certificates propagate through both attained global maxima. -/
theorem afe_maxima_le_two_rationals {h A D : ℝ} (hD0 : 0 ≤ D)
    (hA : ∀ σ ∈ Set.Icc (0 : ℝ) 1, afeSourceA0 σ h 10000000000 ≤ A)
    (hD : ∀ σ ∈ Set.Icc (0 : ℝ) (1 / 2), afeSourceA0 σ h 10000000000 ≤ D) :
    afeDirectMaximum h 10000000000 ≤ A + (1 + 1 / 10000000000) / 100000000000000000000 ∧
    afeReflectedMaximum h 10000000000 ≤ D * (1 + 1 / 10000000000) + 1 / 100000000000000000000 := by
  have hn : afeSigmaStrip.Nonempty := ⟨1, by norm_num [afeSigmaStrip]⟩
  have ht : 2 * Real.pi ≤ (10000000000 : ℝ) := by linarith [Real.pi_lt_four]
  have hC (σ : ℝ) (hσ : σ ∈ afeSigmaStrip) := chiC0_le_one_add_inv hσ (t₀ := 10000000000) (by norm_num)
  have hB (σ : ℝ) (hσ : 0 ≤ σ) : afeSourceB0 σ 10000000000 ≤ 1 / 100000000000000000000 := by
    simpa only [show (10000000000 : ℝ) ^ 2 = 100000000000000000000 by norm_num] using afeSourceB0_le_inv_sq hσ ht
  constructor
  · apply csSup_le (hn.image _)
    rintro _ ⟨σ, hσ, rfl⟩
    have hs : σ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hσ.1], hσ.2⟩
    have ha := hA _ hs
    have hp := mul_le_mul (hC σ hσ) (hB σ hs.1) (afeSourceB0_nonneg σ ht)
      (by norm_num : (0 : ℝ) ≤ 1 + 1 / 10000000000)
    dsimp only [afeDirectE0]
    linarith
  · apply csSup_le (hn.image _)
    rintro _ ⟨σ, hσ, rfl⟩
    have hs : 1 - σ ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have ha := hD _ hs
    have hp := mul_le_mul ha (hC σ hσ) (chiC0_pos hσ (by norm_num : (0 : ℝ) < 10000000000)).le hD0
    have hb := hB (1 - σ) hs.1
    dsimp only [afeReflectedE0]
    linarith

/-- Both complete analytic band coefficients are bounded by their certified finite rational expressions. -/
theorem afe_table_two_rational_coefficients {k : ℕ} (hk : 1 ≤ k) (hkmax : k ≤ 10) :
    (k : ℝ) / Real.pi + afeDirectMaximum (afeBandLower k) 10000000000 ≤
      (k : ℝ) / (314159265358979323846 / 100000000000000000000) +
        afeTableRationalA 1 (afeTableTwoLower k) + (1 + 1 / 10000000000) / 100000000000000000000 ∧
    (k : ℝ) * (1 + afeDelta0 10000000000) / Real.pi + afeReflectedMaximum (afeBandLower k) 10000000000 ≤
      ((k : ℝ) / (314159265358979323846 / 100000000000000000000) +
        afeTableRationalA (1 / 2) (afeTableTwoLower k)) * (1 + 1 / 10000000000) + 1 / 100000000000000000000 := by
  have hH := afeTableTwoLower_le_band hk hkmax
  have hHpos : 0 < afeTableTwoLower k := by
    unfold afeTableTwoLower
    split_ifs <;> norm_num
  have hDpos : 0 ≤ afeTableRationalA (1 / 2) (afeTableTwoLower k) := by
    unfold afeTableRationalA
    dsimp only
    norm_num
    positivity
  have hm := afe_maxima_le_two_rationals hDpos
    (fun σ hσ => afeSourceA0_le_table_rational hσ hHpos hH)
    (fun σ hσ => afeSourceA0_le_table_rational hσ hHpos hH)
  have hp : (k : ℝ) / Real.pi ≤ (k : ℝ) / (314159265358979323846 / 100000000000000000000) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by linarith [Real.pi_gt_d20])
  have hd := afeDelta0_le_inv (t₀ := 10000000000) (by norm_num)
  have hd0 := afeDelta0_nonneg (t₀ := 10000000000) (by norm_num)
  have hc := mul_le_mul hp (show 1 + afeDelta0 10000000000 ≤ 1 + 1 / 10000000000 by linarith)
    (show 0 ≤ 1 + afeDelta0 10000000000 by linarith) (by positivity)
  constructor
  · linarith [hm.1]
  · have he : (k : ℝ) * (1 + afeDelta0 10000000000) / Real.pi =
        (k : ℝ) / Real.pi * (1 + afeDelta0 10000000000) := by ring
    rw [he]
    nlinarith [hm.2]

/-- Every proposed outward Table 2 cell is certified on the complete source sigma interval. -/
theorem proposed_table_two_constants {k : ℕ} (hk : 1 ≤ k) (hkmax : k ≤ 10) :
    (k : ℝ) / Real.pi + afeDirectMaximum (afeBandLower k) 10000000000 ≤ proposedTableTwoDirect k ∧
    (k : ℝ) * (1 + afeDelta0 10000000000) / Real.pi + afeReflectedMaximum (afeBandLower k) 10000000000 ≤
      proposedTableTwoReflected k := by
  have h := afe_table_two_rational_coefficients hk hkmax
  constructor
  · apply h.1.trans
    interval_cases k <;> norm_num [afeTableRationalA, afeTableTwoLower, proposedTableTwoDirect]
  · apply h.2.trans
    interval_cases k <;> norm_num [afeTableRationalA, afeTableTwoLower, proposedTableTwoReflected]

/-- The actual direct AFE consumes the certified proposed outward Table 2 bound. -/
theorem proposed_table_two_direct {σ t x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 10000000000 ≤ |t|)
    (hk : 1 ≤ k) (hkmax : k ≤ 10) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hyx : y ≤ x)
    (hband : y ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      (proposedTableTwoDirect k) * (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  have hk1 : 1 ≤ k := by omega
  have hypos : 0 < y := by linarith [afeBandLower_ge hk1]
  have hs := afe_band_direct hσ (show 2 * Real.pi ≤ (10000000000 : ℝ) by linarith [Real.pi_lt_four])
    ht hk1 hx hy hyx hband hxhalf hyhalf hscale
  exact hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (proposed_table_two_constants hk hkmax).1
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg hypos.le _))

/-- The actual reflected AFE consumes the certified proposed outward Table 2 bound. -/
theorem proposed_table_two_reflected {σ t x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 10000000000 ≤ |t|)
    (hk : 1 ≤ k) (hkmax : k ≤ 10) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hxy : x ≤ y)
    (hband : x ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤ (proposedTableTwoReflected k) * x ^ (-σ) := by
  have hk1 : 1 ≤ k := by omega
  have hxpos : 0 < x := by linarith [afeBandLower_ge hk1]
  have hs := afe_band_reflected hσ (show 2 * Real.pi ≤ (10000000000 : ℝ) by linarith [Real.pi_lt_four])
    ht hk1 hx hy hxy hband hxhalf hyhalf hscale
  exact hs.trans (mul_le_mul_of_nonneg_right (proposed_table_two_constants hk hkmax).2
    (Real.rpow_nonneg hxpos.le _))

end DhimanKadiriQuesadaHerrera2026
