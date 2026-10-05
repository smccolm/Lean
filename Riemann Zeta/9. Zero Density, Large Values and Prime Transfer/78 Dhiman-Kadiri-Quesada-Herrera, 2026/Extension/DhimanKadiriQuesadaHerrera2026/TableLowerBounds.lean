import DhimanKadiriQuesadaHerrera2026.AFEBandConstants

namespace DhimanKadiriQuesadaHerrera2026
open Filter
open scoped Topology

/-- A fourth-order corrected trapezoid upper bound from a finite logarithm series. -/
theorem log_succ_sub_upper_fourth_order {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤
      1 / (2 * x) + 1 / (2 * (x + 1)) - (1 / x ^ 2 - 1 / (x + 1) ^ 2) / 12 +
        (1 / x ^ 4 - 1 / (x + 1) ^ 4) / 120 := by
  have hz : 1 / (2 * x + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hl := log_le_logRationalUpper (by positivity : 0 ≤ 1 / (2 * x + 1)) hz 3
  have he : (1 + 1 / (2 * x + 1)) / (1 - 1 / (2 * x + 1)) = (x + 1) / x := by
    field_simp
    ring
  rw [he, Real.log_div (by positivity) hx.ne'] at hl
  have hr : logRationalUpper 3 (1 / (2 * x + 1)) =
      2 / (2 * x + 1) + 2 / (3 * (2 * x + 1) ^ 3) + 2 / (5 * (2 * x + 1) ^ 5) +
        1 / (2 * x * (x + 1) * (2 * x + 1) ^ 5) := by
    have hn : 1 - (1 / (2 * x + 1)) ^ 2 ≠ 0 := by
      have hp : 0 ≤ 1 / (2 * x + 1) := by positivity
      nlinarith
    norm_num [logRationalUpper, logRationalLower, Finset.sum_range_succ]
    field_simp
    ring_nf
    field_simp [show x * 4 + x ^ 2 * 4 ≠ 0 by positivity]
    ring
  rw [hr] at hl
  have hd : (1 / (2 * x) + 1 / (2 * (x + 1)) - (1 / x ^ 2 - 1 / (x + 1) ^ 2) / 12 +
      (1 / x ^ 4 - 1 / (x + 1) ^ 4) / 120) -
      (2 / (2 * x + 1) + 2 / (3 * (2 * x + 1) ^ 3) + 2 / (5 * (2 * x + 1) ^ 5) +
        1 / (2 * x * (x + 1) * (2 * x + 1) ^ 5)) =
      (1 + 14 * x + 76 * x ^ 2 + 164 * x ^ 3 + 182 * x ^ 4 + 120 * x ^ 5 + 40 * x ^ 6) /
        (120 * x ^ 4 * (x + 1) ^ 4 * (2 * x + 1) ^ 5) := by
    field_simp
    ring
  have hp : 0 ≤ (1 + 14 * x + 76 * x ^ 2 + 164 * x ^ 3 + 182 * x ^ 4 + 120 * x ^ 5 + 40 * x ^ 6) /
      (120 * x ^ 4 * (x + 1) ^ 4 * (2 * x + 1) ^ 5) := by positivity
  rw [← hd] at hp
  linarith

/-- The fourth-order endpoint correction telescopes on every positive translate. -/
theorem log_sub_reciprocal_sum_upper_fourth_order {x : ℝ} (hx : 0 < x) (N : ℕ) :
    Real.log ((N : ℝ) + x) - (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + x)) ≤
      Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) + 1 / (120 * x ^ 4) +
      1 / (2 * ((N : ℝ) + x)) + 1 / (12 * ((N : ℝ) + x) ^ 2) -
        1 / (120 * ((N : ℝ) + x) ^ 4) := by
  induction N with
  | zero => simp; ring_nf; exact le_rfl
  | succ N ih =>
    have hu : 0 < (N : ℝ) + x := by positivity
    have hl := log_succ_sub_upper_fourth_order hu
    rw [Finset.sum_range_succ]
    push_cast
    rw [show (N : ℝ) + 1 + x = (N : ℝ) + x + 1 by ring]
    simp only [div_eq_mul_inv, mul_inv_rev] at hl ih ⊢
    linarith

/-- The actual digamma function has a fourth-order upper enclosure on the positive axis. -/
theorem real_digamma_upper_fourth_order {x : ℝ} (hx : 0 < x) :
    (Complex.digamma (x : ℂ)).re ≤ Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) +
      1 / (120 * x ^ 4) := by
  have hinv : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + x)) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hlim := ((tendsto_log_sub_reciprocal_sum hx).sub (hinv.div_const 2)).sub
    ((hinv.pow 2).div_const 12)
  have hlim' := hlim.add ((hinv.pow 4).div_const 120)
  have he : (Complex.digamma (x : ℂ)).re - 0 / 2 - 0 ^ 2 / 12 + 0 ^ 4 / 120 ≤
      Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) + 1 / (120 * x ^ 4) := by
    apply le_of_tendsto hlim'
    apply Eventually.of_forall
    intro N
    have h := log_sub_reciprocal_sum_upper_fourth_order hx N
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, one_mul] at h ⊢
    linarith
  simpa using he

/-- A finite fourth-order lower enclosure for Euler's constant, with a proved analytic remainder. -/
theorem euler_constant_lower_fourth_finite (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)) - Real.log ((N : ℝ) + 1) +
      1 / (2 * ((N : ℝ) + 1)) + 1 / (12 * ((N : ℝ) + 1) ^ 2) -
        1 / (120 * ((N : ℝ) + 1) ^ 4) ≤ Real.eulerMascheroniConstant := by
  have he := real_digamma_upper_fourth_order (by positivity : 0 < (1 : ℝ) + N)
  rw [real_digamma_add_nat (by norm_num : (0 : ℝ) < 1), Complex.ofReal_one, real_digamma_one] at he
  simp_rw [add_comm (1 : ℝ)] at he
  linarith

/-- A precise lower decimal enclosure for Euler's constant is certified by rational arithmetic. -/
theorem euler_constant_ge_table_precision : (577215664 : ℝ) / 1000000000 ≤ Real.eulerMascheroniConstant := by
  have h := euler_constant_lower_fourth_finite 31
  have hl := log_le_logRationalUpper (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 12
  rw [show (1 + (1 / 3 : ℝ)) / (1 - 1 / 3) = 2 by norm_num] at hl
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  norm_num only [Nat.cast_ofNat, show (31 : ℝ) + 1 = 32 by norm_num] at h
  rw [h32] at h
  have hr : (577215664 : ℝ) / 1000000000 ≤
      (∑ n ∈ Finset.range 31, 1 / ((n : ℝ) + 1)) - 5 * logRationalUpper 12 (1 / 3) +
      1 / (2 * 32) + 1 / (12 * 32 ^ 2) - 1 / (120 * 32 ^ 4) := by
    norm_num [logRationalUpper, logRationalLower, Finset.sum_range_succ]
  linarith


/-- A lower logarithm enclosure is certified by its positive finite series. -/
theorem log_two_ge_table_precision : (69314718055 : ℝ) / 100000000000 ≤ Real.log 2 := by
  have h := logRationalLower_le (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 12
  rw [show (1 + (1 / 3 : ℝ)) / (1 - 1 / 3) = 2 by norm_num] at h
  have hr : (69314718055 : ℝ) / 100000000000 ≤ logRationalLower 12 (1 / 3) := by
    norm_num [logRationalLower, Finset.sum_range_succ]
  exact hr.trans h

/-- Every positive term of A₀ at sigma=1 has an explicit lower rational enclosure. -/
theorem afeSourceA0_one_ge_rational {h t₀ P L G X T : ℝ} (hh : 0 < h) (ht : 0 < t₀)
    (hP : Real.pi ≤ P) (hL : L ≤ Real.log 2)
    (hG : G ≤ Real.eulerMascheroniConstant) (hbase : 0 ≤ G + (7 / 2) * L - 3 / 2)
    (hX : max h (Real.sqrt (t₀ / (2 * Real.pi))) ≤ X) (hT : t₀ ≤ T) :
    1 / 4 + (G + (7 / 2) * L - 3 / 2) / P + 115 / (27 * P ^ 2) +
      7 / (4 * P * h) + 3 / (4 * P * (h + 1)) + 7 / (8 * P * h ^ 2) +
      46 / (9 * P ^ 2 * X) + 115 / (54 * P ^ 3 * X ^ 2) +
      1 / (4 * T) + 1 / (2 * P * h ^ 2 * T) + L / (2 * P * T) +
      3 / (4 * P * (h + 1) * T) + 46 / (9 * P ^ 2 * X * T) ≤ afeSourceA0 1 h t₀ := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hx : 0 < max h (Real.sqrt (t₀ / (2 * Real.pi))) := hh.trans_le (le_max_left _ _)
  have hPpos : 0 < P := hπ.trans_le hP
  have hXpos : 0 < X := hx.trans_le hX
  have hTpos : 0 < T := ht.trans_le hT
  unfold afeSourceA0
  dsimp only
  norm_num only [one_add_one_eq_two, mul_one, one_mul]
  gcongr
  first | positivity | linarith

/-- The sigma-one A₀ value is a lower bound for the actual attained direct maximum. -/
theorem afeSourceA0_one_le_directMaximum {h t₀ : ℝ} (ht : 2 * Real.pi ≤ t₀) :
    afeSourceA0 1 h t₀ ≤ afeDirectMaximum h t₀ := by
  have htpos : 0 < t₀ := lt_of_lt_of_le (by positivity : 0 < 2 * Real.pi) ht
  have hb := (afe_source_le_maxima (h := h) htpos (show (1 : ℝ) ∈ afeSigmaStrip by norm_num [afeSigmaStrip])).1
  have hc := chiC0_pos (show (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 by norm_num) htpos
  have hB := afeSourceB0_nonneg 1 ht
  have hp := mul_nonneg hc.le hB
  dsimp only [afeDirectE0] at hb
  linarith

/-- Table 1's displayed direct maximum at 2π is below an actual source value at sigma=1. -/
theorem table_one_two_pi_direct_rounding_fails :
    (2.265204 : ℝ) < afeDirectMaximum (3 / 2) (2 * Real.pi) := by
  have hx : max (3 / 2) (Real.sqrt ((2 * Real.pi) / (2 * Real.pi))) ≤ (3 / 2 : ℝ) := by
    rw [div_self (by positivity : 2 * Real.pi ≠ 0), Real.sqrt_one]
    norm_num
  have hb := afeSourceA0_one_ge_rational (h := 3 / 2) (t₀ := 2 * Real.pi)
    (P := 314159265358979323847 / 100000000000000000000) (L := 69314718055 / 100000000000)
    (G := 577215664 / 1000000000) (X := 3 / 2) (T := 2 * (314159265358979323847 / 100000000000000000000))
    (by norm_num) (by positivity) (by linarith [Real.pi_lt_d20]) log_two_ge_table_precision
    euler_constant_ge_table_precision (by norm_num) hx (by linarith [Real.pi_lt_d20])
  norm_num at hb
  have hm := afeSourceA0_one_le_directMaximum (h := 3 / 2) (le_refl (2 * Real.pi))
  linarith

/-- Table 1's displayed direct maximum at 1000 is below an actual source value at sigma=1. -/
theorem table_one_thousand_direct_rounding_fails :
    (1.792736 : ℝ) < afeDirectMaximum (3 / 2) 1000 := by
  have hx : max (3 / 2) (Real.sqrt (1000 / (2 * Real.pi))) ≤ (126156627 / 10000000 : ℝ) := by
    apply max_le (by norm_num)
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr ?_⟩
    nlinarith [Real.pi_gt_d20]
  have hb := afeSourceA0_one_ge_rational (h := 3 / 2) (t₀ := 1000)
    (P := 314159265358979323847 / 100000000000000000000) (L := 69314718055 / 100000000000)
    (G := 577215664 / 1000000000) (X := 126156627 / 10000000) (T := 1000)
    (by norm_num) (by norm_num) (by linarith [Real.pi_lt_d20]) log_two_ge_table_precision
    euler_constant_ge_table_precision (by norm_num) hx (le_refl _)
  norm_num at hb
  have hm := afeSourceA0_one_le_directMaximum (h := 3 / 2) (t₀ := 1000) (by linarith [Real.pi_lt_four])
  linarith

/-- Table 1's displayed direct maximum at ten billion is below an actual source value at sigma=1. -/
theorem table_one_large_direct_rounding_fails :
    (1.750701 : ℝ) < afeDirectMaximum (3 / 2) 10000000000 := by
  have hx : max (3 / 2) (Real.sqrt (10000000000 / (2 * Real.pi))) ≤ (39895 : ℝ) := by
    apply max_le (by norm_num)
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr ?_⟩
    nlinarith [Real.pi_gt_d20]
  have hb := afeSourceA0_one_ge_rational (h := 3 / 2) (t₀ := 10000000000)
    (P := 314159265358979323847 / 100000000000000000000) (L := 69314718055 / 100000000000)
    (G := 577215664 / 1000000000) (X := 39895) (T := 10000000000)
    (by norm_num) (by norm_num) (by linarith [Real.pi_lt_d20]) log_two_ge_table_precision
    euler_constant_ge_table_precision (by norm_num) hx (le_refl _)
  norm_num at hb
  have hm := afeSourceA0_one_le_directMaximum (h := 3 / 2) (t₀ := 10000000000) (by linarith [Real.pi_lt_four])
  linarith

end DhimanKadiriQuesadaHerrera2026
