import DhimanKadiriQuesadaHerrera2026.AFETableTwo
import DhimanKadiriQuesadaHerrera2026.ChiTableBounds

namespace DhimanKadiriQuesadaHerrera2026

/-- The actual B₀ is bounded directly from a separately certified exponential tail. -/
theorem afeSourceB0_le_exp_bound {σ t₀ E : ℝ} (hσ : 0 ≤ σ) (ht₀ : 2 * Real.pi ≤ t₀) (hE : Real.exp (-Real.pi * t₀) ≤ E) :
    afeSourceB0 σ t₀ ≤ 2 * t₀ ^ 2 * E := by
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
  have hNnon : 0 ≤ (1 / 2) * Real.sqrt z * Real.log z + z ^ ((1 - σ) / 2) := by
    have hl := Real.log_nonneg hz
    positivity
  unfold afeSourceB0
  change (((1 / 2) * Real.sqrt z * Real.log z + z ^ ((1 - σ) / 2)) * Real.exp (-Real.pi * t₀)) /
    (1 - Real.exp (-Real.pi * t₀)) ≤ _
  calc
    _ ≤ (t₀ ^ 2 * E) / (1 / 2) := by
      apply div_le_div₀ (show 0 ≤ t₀ ^ 2 * E by exact mul_nonneg (sq_nonneg _) ((Real.exp_pos _).le.trans hE))
        (mul_le_mul hn hE (Real.exp_pos _).le (sq_nonneg t₀)) (by norm_num) hden
    _ = 2 * t₀ ^ 2 * E := by ring


/-- A full sigma-interval rational certificate for the two pi direct A₀ input. -/
theorem afeSourceA0_two_pi_direct_cap {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    afeSourceA0 σ (3 / 2) (2 * Real.pi) ≤ 2265206295 / 1000000000 := by
  have hx : ((3 / 2) : ℝ) ≤ max (3 / 2) (Real.sqrt ((2 * Real.pi) / (2 * Real.pi))) := by
    exact le_max_left _ _
  have hb := afeSourceA0_le_sigma_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := (3 / 2)) (T := 2 * (314159265358979323846 / 100000000000000000000)) (X := (3 / 2)) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision
    (by norm_num) (le_refl _) (by norm_num) (by linarith [Real.pi_gt_d20])
    (by norm_num) hx euler_constant_le_table_precision
  norm_num at hb
  linarith

/-- A full sigma-interval rational certificate for the two pi reflected A₀ input. -/
theorem afeSourceA0_two_pi_reflected_cap {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    afeSourceA0 σ (3 / 2) (2 * Real.pi) ≤ 2087389451 / 1000000000 := by
  have hx : ((3 / 2) : ℝ) ≤ max (3 / 2) (Real.sqrt ((2 * Real.pi) / (2 * Real.pi))) := by
    exact le_max_left _ _
  have hb := afeSourceA0_le_sigma_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := (3 / 2)) (T := 2 * (314159265358979323846 / 100000000000000000000)) (X := (3 / 2)) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision
    (by norm_num) (le_refl _) (by norm_num) (by linarith [Real.pi_gt_d20])
    (by norm_num) hx euler_constant_le_table_precision
  norm_num at hb
  linarith

/-- A full sigma-interval rational certificate for the thousand direct A₀ input. -/
theorem afeSourceA0_thousand_direct_cap {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    afeSourceA0 σ (3 / 2) (1000) ≤ 1792736529 / 1000000000 := by
  have hx : ((630783 / 50000) : ℝ) ≤ max (3 / 2) (Real.sqrt ((1000) / (2 * Real.pi))) := by
    apply le_trans _ (le_max_right _ _)
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith [Real.pi_lt_d20]
  have hb := afeSourceA0_le_sigma_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := (3 / 2)) (T := 1000) (X := (630783 / 50000)) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision
    (by norm_num) (le_refl _) (by norm_num) (by norm_num)
    (by norm_num) hx euler_constant_le_table_precision
  norm_num at hb
  linarith

/-- A full sigma-interval rational certificate for the thousand reflected A₀ input. -/
theorem afeSourceA0_thousand_reflected_cap {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    afeSourceA0 σ (3 / 2) (1000) ≤ 1781969502 / 1000000000 := by
  have hx : ((630783 / 50000) : ℝ) ≤ max (3 / 2) (Real.sqrt ((1000) / (2 * Real.pi))) := by
    apply le_trans _ (le_max_right _ _)
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith [Real.pi_lt_d20]
  have hb := afeSourceA0_le_sigma_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := (3 / 2)) (T := 1000) (X := (630783 / 50000)) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision
    (by norm_num) (le_refl _) (by norm_num) (by norm_num)
    (by norm_num) hx euler_constant_le_table_precision
  norm_num at hb
  linarith

/-- A full sigma-interval rational certificate for the thousand symmetric A₀ input. -/
theorem afeSourceA0_thousand_symmetric_cap {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    afeSourceA0 σ (25 / 2) (1000) ≤ 1265977128 / 1000000000 := by
  have hx : ((630783 / 50000) : ℝ) ≤ max (25 / 2) (Real.sqrt ((1000) / (2 * Real.pi))) := by
    apply le_trans _ (le_max_right _ _)
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith [Real.pi_lt_d20]
  have hb := afeSourceA0_le_sigma_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := (25 / 2)) (T := 1000) (X := (630783 / 50000)) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision
    (by norm_num) (le_refl _) (by norm_num) (by norm_num)
    (by norm_num) hx euler_constant_le_table_precision
  norm_num at hb
  linarith

/-- A full sigma-interval rational certificate for the large direct A₀ input. -/
theorem afeSourceA0_large_direct_cap {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    afeSourceA0 σ (3 / 2) (10000000000) ≤ 1750701076 / 1000000000 := by
  have hx : (39894 : ℝ) ≤ max (3 / 2) (Real.sqrt ((10000000000) / (2 * Real.pi))) := by
    apply le_trans _ (le_max_right _ _)
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith [Real.pi_lt_d20]
  have hb := afeSourceA0_le_sigma_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := (3 / 2)) (T := 10000000000) (X := 39894) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision
    (by norm_num) (le_refl _) (by norm_num) (by norm_num)
    (by norm_num) hx euler_constant_le_table_precision
  norm_num at hb
  linarith

/-- A full sigma-interval rational certificate for the large reflected A₀ input. -/
theorem afeSourceA0_large_reflected_cap {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    afeSourceA0 σ (3 / 2) (10000000000) ≤ 1750697831 / 1000000000 := by
  have hx : (39894 : ℝ) ≤ max (3 / 2) (Real.sqrt ((10000000000) / (2 * Real.pi))) := by
    apply le_trans _ (le_max_right _ _)
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith [Real.pi_lt_d20]
  have hb := afeSourceA0_le_sigma_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := (3 / 2)) (T := 10000000000) (X := 39894) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision
    (by norm_num) (le_refl _) (by norm_num) (by norm_num)
    (by norm_num) hx euler_constant_le_table_precision
  norm_num at hb
  linarith

/-- A full sigma-interval rational certificate for the large symmetric A₀ input. -/
theorem afeSourceA0_large_symmetric_cap {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    afeSourceA0 σ (79789 / 2) (10000000000) ≤ 1160079345 / 1000000000 := by
  have hx : ((79789 / 2) : ℝ) ≤ max (79789 / 2) (Real.sqrt ((10000000000) / (2 * Real.pi))) := by
    exact le_max_left _ _
  have hb := afeSourceA0_le_sigma_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := (79789 / 2)) (T := 10000000000) (X := (79789 / 2)) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision
    (by norm_num) (le_refl _) (by norm_num) (by norm_num)
    (by norm_num) hx euler_constant_le_table_precision
  norm_num at hb
  linarith

/-- A full sigma-interval rational certificate for the trillion direct A₀ input. -/
theorem afeSourceA0_trillion_direct_cap {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    afeSourceA0 σ (3 / 2) (3000000000000) ≤ 1750688844 / 1000000000 := by
  have hx : (690988 : ℝ) ≤ max (3 / 2) (Real.sqrt ((3000000000000) / (2 * Real.pi))) := by
    apply le_trans _ (le_max_right _ _)
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith [Real.pi_lt_d20]
  have hb := afeSourceA0_le_sigma_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := (3 / 2)) (T := 3000000000000) (X := 690988) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision
    (by norm_num) (le_refl _) (by norm_num) (by norm_num)
    (by norm_num) hx euler_constant_le_table_precision
  norm_num at hb
  linarith

/-- A full sigma-interval rational certificate for the trillion reflected A₀ input. -/
theorem afeSourceA0_trillion_reflected_cap {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    afeSourceA0 σ (3 / 2) (3000000000000) ≤ 1750688657 / 1000000000 := by
  have hx : (690988 : ℝ) ≤ max (3 / 2) (Real.sqrt ((3000000000000) / (2 * Real.pi))) := by
    apply le_trans _ (le_max_right _ _)
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith [Real.pi_lt_d20]
  have hb := afeSourceA0_le_sigma_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := (3 / 2)) (T := 3000000000000) (X := 690988) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision
    (by norm_num) (le_refl _) (by norm_num) (by norm_num)
    (by norm_num) hx euler_constant_le_table_precision
  norm_num at hb
  linarith

/-- A full sigma-interval rational certificate for the trillion symmetric A₀ input. -/
theorem afeSourceA0_trillion_symmetric_cap {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    afeSourceA0 σ (1381977 / 2) (3000000000000) ≤ 1160048318 / 1000000000 := by
  have hx : ((1381977 / 2) : ℝ) ≤ max (1381977 / 2) (Real.sqrt ((3000000000000) / (2 * Real.pi))) := by
    exact le_max_left _ _
  have hb := afeSourceA0_le_sigma_rational hσ
    (P := 314159265358979323846 / 100000000000000000000) (L := 693147181 / 1000000000)
    (H := (1381977 / 2)) (T := 3000000000000) (X := (1381977 / 2)) (G := 577215674 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20]) log_two_le_table_precision
    (by norm_num) (le_refl _) (by norm_num) (by norm_num)
    (by norm_num) hx euler_constant_le_table_precision
  norm_num at hb
  linarith

/-- Distinct half-integers have separation at least one. -/
theorem half_integer_gap {x H : ℝ} (hx : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hH : ∃ j : ℤ, H = (j : ℝ) + 1 / 2) (hlt : x < H) : x + 1 ≤ H := by
  obtain ⟨j, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := hH
  have hjk : (j : ℝ) < k := by linarith
  have hjk' : j < k := by exact_mod_cast hjk
  have hjk'' : (j : ℝ) + 1 ≤ k := by exact_mod_cast (show j + 1 ≤ k by omega)
  linarith

/-- The physical product scale forces a half-integer symmetric cutoff above an explicit threshold. -/
theorem symmetric_cutoff_ge_of_square {x H t₀ : ℝ} (hx : 0 ≤ x)
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2) (hHhalf : ∃ j : ℤ, H = (j : ℝ) + 1 / 2)
    (ht : t₀ ≤ 2 * Real.pi * x * x) (hbelow : 2 * Real.pi * (H - 1) ^ 2 < t₀) : H ≤ x := by
  by_contra h
  have hg := half_integer_gap hxhalf hHhalf (lt_of_not_ge h)
  have hp : x ^ 2 ≤ (H - 1) ^ 2 := pow_le_pow_left₀ hx (by linarith) 2
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * Real.pi by positivity)
  nlinarith only [hm, ht, hbelow]

/-- The source symmetric cutoff at threshold 1000 follows from the physical scale. -/
theorem symmetric_cutoff_ge_thousand {x : ℝ} (hx : 0 ≤ x)
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2) (ht : 1000 ≤ 2 * Real.pi * x * x) : (25 / 2 : ℝ) ≤ x := by
  apply symmetric_cutoff_ge_of_square hx hxhalf ⟨12, by norm_num⟩ ht
  nlinarith [Real.pi_lt_d20]

/-- The source symmetric cutoff at threshold 10¹⁰ follows from the physical scale. -/
theorem symmetric_cutoff_ge_large {x : ℝ} (hx : 0 ≤ x)
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2) (ht : 10000000000 ≤ 2 * Real.pi * x * x) : (79789 / 2 : ℝ) ≤ x := by
  apply symmetric_cutoff_ge_of_square hx hxhalf ⟨39894, by norm_num⟩ ht
  nlinarith [Real.pi_lt_d20]

/-- The source symmetric cutoff at threshold 3·10¹² follows from the physical scale. -/
theorem symmetric_cutoff_ge_trillion {x : ℝ} (hx : 0 ≤ x)
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2) (ht : 3000000000000 ≤ 2 * Real.pi * x * x) : (1381977 / 2 : ℝ) ≤ x := by
  apply symmetric_cutoff_ge_of_square hx hxhalf ⟨690988, by norm_num⟩ ht
  nlinarith [Real.pi_lt_d20]


/-- Uniform A₀, B₀ and C₀ estimates propagate to both actual global source maxima. -/
theorem afe_maxima_of_table_certificates {t₀ h A R B D : ℝ} (ht : 2 * Real.pi ≤ t₀)
    (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hA : ∀ σ ∈ Set.Icc (0 : ℝ) 1, afeSourceA0 σ h t₀ ≤ A)
    (hAR : ∀ σ ∈ Set.Icc (0 : ℝ) (1 / 2), afeSourceA0 σ h t₀ ≤ R)
    (hB : ∀ σ, 0 ≤ σ → afeSourceB0 σ t₀ ≤ B)
    (hC : ∀ σ ∈ afeSigmaStrip, chiC0 σ t₀ ≤ 1 + D) :
    afeDirectMaximum h t₀ ≤ A + (1 + D) * B ∧ afeReflectedMaximum h t₀ ≤ R * (1 + D) + B := by
  have hn : afeSigmaStrip.Nonempty := ⟨1, by norm_num [afeSigmaStrip]⟩
  have htpos : 0 < t₀ := lt_of_lt_of_le (by positivity : 0 < 2 * Real.pi) ht
  constructor
  · apply csSup_le (hn.image _)
    rintro _ ⟨σ, hσ, rfl⟩
    have hs : σ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hσ.1], hσ.2⟩
    have ha := hA _ hs
    have hp := mul_le_mul (hC σ hσ) (hB σ hs.1) (afeSourceB0_nonneg σ ht) (by linarith : 0 ≤ 1 + D)
    dsimp only [afeDirectE0]
    linarith
  · apply csSup_le (hn.image _)
    rintro _ ⟨σ, hσ, rfl⟩
    have hs : 1 - σ ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have ha := hAR _ hs
    have hp := mul_le_mul ha (hC σ hσ) (chiC0_pos hσ htpos).le hR
    have hb := hB (1 - σ) hs.1
    dsimp only [afeReflectedE0]
    linarith

/-- A coarse but sufficient rational bound on B₀ at exact 2π. -/
theorem afeSourceB0_two_pi_cap {σ : ℝ} (hσ : 0 ≤ σ) :
    afeSourceB0 σ (2 * Real.pi) ≤ 1 / 2500000 := by
  have h := afeSourceB0_le_exp_bound hσ (le_refl (2 * Real.pi)) exp_neg_two_pi_table
  nlinarith [Real.pi_lt_four, Real.pi_pos, sq_nonneg (Real.pi - 4)]

/-- The finite exponential certificate makes B₀ at 1000 smaller than 10⁻¹². -/
theorem afeSourceB0_thousand_cap {σ : ℝ} (hσ : 0 ≤ σ) :
    afeSourceB0 σ 1000 ≤ 1 / 1000000000000 := by
  have h := afeSourceB0_le_exp_bound hσ (t₀ := 1000) (by linarith [Real.pi_lt_four])
    (exp_neg_large_table (by norm_num))
  norm_num at h
  linarith

/-- The four exact source thresholds, with exact 2π in the first row. -/
noncomputable def tableOneHeight (r : ℕ) : ℝ :=
  if r = 0 then 2 * Real.pi else if r = 1 then 1000 else if r = 2 then 10000000000 else 3000000000000

/-- The source half-integer lower cutoffs for the symmetric column. -/
noncomputable def tableOneSymmetricCutoff (r : ℕ) : ℝ :=
  if r = 0 then 1.5 else if r = 1 then 12.5 else if r = 2 then 39894.5 else 690988.5

/-- Proposed outward direct Table 1 bounds; source adoption remains separate. -/
noncomputable def proposedTableOneDirect (r : ℕ) : ℝ :=
  if r = 0 then 2.265207 else if r = 1 then 1.792737 else if r = 2 then 1.750702 else 1.750689

/-- The unchanged printed reflected Table 1 bounds. -/
noncomputable def proposedTableOneReflected (r : ℕ) : ℝ :=
  if r = 0 then 2.264445 else if r = 1 then 1.792711 else if r = 2 then 1.750701 else 1.750689

/-- Proposed outward symmetric Table 1 bounds; source adoption remains separate. -/
noncomputable def proposedTableOneSymmetric (r : ℕ) : ℝ :=
  if r = 0 then 2.265207 else if r = 1 then 1.265978 else if r = 2 then 1.160080 else 1.160049

/-- Certified chi corrections for the four source rows, including two proposed outward repairs. -/
noncomputable def proposedTableOneDelta (r : ℕ) : ℝ :=
  if r = 0 then 0.05961930 else if r = 1 then 0.0003692901 else
  if r = 2 then 3692588 / 100000000000000000 else 1230863 / 10000000000000000000

/-- Every table row has the physical height and lower-cutoff requirements of the analytic AFE. -/
theorem table_one_parameters {r : ℕ} (hr : r ≤ 3) :
    2 * Real.pi ≤ tableOneHeight r ∧ 3 / 2 ≤ tableOneSymmetricCutoff r := by
  interval_cases r <;> norm_num [tableOneHeight, tableOneSymmetricCutoff] <;> linarith [Real.pi_lt_four]

/-- The physical symmetric scale yields each displayed source cutoff, without a new cutoff premise. -/
theorem table_one_symmetric_cutoff {r : ℕ} {x : ℝ} (hr : r ≤ 3) (hx : 1 ≤ x)
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2) (ht : tableOneHeight r ≤ 2 * Real.pi * x * x) :
    tableOneSymmetricCutoff r ≤ x := by
  interval_cases r <;> norm_num [tableOneHeight, tableOneSymmetricCutoff] at ht ⊢
  · exact half_integer_ge_three_halves hx hxhalf
  · exact symmetric_cutoff_ge_thousand (by linarith) hxhalf ht
  · exact symmetric_cutoff_ge_large (by linarith) hxhalf ht
  · exact symmetric_cutoff_ge_trillion (by linarith) hxhalf ht

/-- All sixteen proposed Table 1 cells bound the actual global source maxima on the entire closed strip. -/
theorem proposed_table_one_constants {r : ℕ} (hr : r ≤ 3) :
    afeDirectMaximum (3 / 2) (tableOneHeight r) ≤ proposedTableOneDirect r ∧
    afeReflectedMaximum (3 / 2) (tableOneHeight r) ≤ proposedTableOneReflected r ∧
    afeDirectMaximum (tableOneSymmetricCutoff r) (tableOneHeight r) ≤ proposedTableOneSymmetric r ∧
    afeDelta0 (tableOneHeight r) ≤ proposedTableOneDelta r := by
  interval_cases r
  · have hb (σ : ℝ) (hσ : 0 ≤ σ) : afeSourceB0 σ (2 * Real.pi) ≤ (1 / 2500000) := by
      exact afeSourceB0_two_pi_cap hσ
    have hm := afe_maxima_of_table_certificates (h := 3 / 2) (t₀ := 2 * Real.pi)
      (A := 2265206295 / 1000000000) (R := 2087389451 / 1000000000) (B := (1 / 2500000)) (D := (596193 / 10000000))
      (by exact le_refl _) (by norm_num) (by norm_num)
      (fun σ hσ => afeSourceA0_two_pi_direct_cap hσ)
      (fun σ hσ => afeSourceA0_two_pi_reflected_cap hσ) hb (fun σ hσ => chiC0_le_two_pi_table hσ)
    have hs := afe_maxima_of_table_certificates (h := (3 / 2)) (t₀ := 2 * Real.pi)
      (A := 2265206295 / 1000000000) (R := 2265206295 / 1000000000) (B := (1 / 2500000)) (D := (596193 / 10000000))
      (by exact le_refl _) (by norm_num) (by norm_num)
      (fun σ hσ => afeSourceA0_two_pi_direct_cap hσ)
      (fun σ hσ => afeSourceA0_two_pi_direct_cap ⟨hσ.1, by linarith [hσ.2]⟩) hb
      (fun σ hσ => chiC0_le_two_pi_table hσ)
    have hd := afeDelta0_le_two_pi_table
    norm_num [tableOneHeight, tableOneSymmetricCutoff, proposedTableOneDirect, proposedTableOneReflected,
      proposedTableOneSymmetric, proposedTableOneDelta] at hm hs hd ⊢
    exact ⟨by linarith [hm.1], by linarith [hm.2], by linarith [hs.1], hd⟩
  · have hb (σ : ℝ) (hσ : 0 ≤ σ) : afeSourceB0 σ (1000) ≤ (1 / 1000000000000) := by
      exact afeSourceB0_thousand_cap hσ
    have hm := afe_maxima_of_table_certificates (h := 3 / 2) (t₀ := 1000)
      (A := 1792736529 / 1000000000) (R := 1781969502 / 1000000000) (B := (1 / 1000000000000)) (D := (3692901 / 10000000000))
      (by linarith [Real.pi_lt_four]) (by norm_num) (by norm_num)
      (fun σ hσ => afeSourceA0_thousand_direct_cap hσ)
      (fun σ hσ => afeSourceA0_thousand_reflected_cap hσ) hb (fun σ hσ => chiC0_le_thousand_table hσ)
    have hs := afe_maxima_of_table_certificates (h := (25 / 2)) (t₀ := 1000)
      (A := 1265977128 / 1000000000) (R := 1265977128 / 1000000000) (B := (1 / 1000000000000)) (D := (3692901 / 10000000000))
      (by linarith [Real.pi_lt_four]) (by norm_num) (by norm_num)
      (fun σ hσ => afeSourceA0_thousand_symmetric_cap hσ)
      (fun σ hσ => afeSourceA0_thousand_symmetric_cap ⟨hσ.1, by linarith [hσ.2]⟩) hb
      (fun σ hσ => chiC0_le_thousand_table hσ)
    have hd := afeDelta0_le_thousand_table
    norm_num [tableOneHeight, tableOneSymmetricCutoff, proposedTableOneDirect, proposedTableOneReflected,
      proposedTableOneSymmetric, proposedTableOneDelta] at hm hs hd ⊢
    exact ⟨by linarith [hm.1], by linarith [hm.2], by linarith [hs.1], hd⟩
  · have hb (σ : ℝ) (hσ : 0 ≤ σ) : afeSourceB0 σ (10000000000) ≤ (1 / 1000000000000) := by
      have hb := afeSourceB0_le_inv_sq hσ (t₀ := 10000000000) (by linarith [Real.pi_lt_four])
      norm_num at hb
      linarith
    have hm := afe_maxima_of_table_certificates (h := 3 / 2) (t₀ := 10000000000)
      (A := 1750701076 / 1000000000) (R := 1750697831 / 1000000000) (B := (1 / 1000000000000)) (D := (923147 / 25000000000000000))
      (by linarith [Real.pi_lt_four]) (by norm_num) (by norm_num)
      (fun σ hσ => afeSourceA0_large_direct_cap hσ)
      (fun σ hσ => afeSourceA0_large_reflected_cap hσ) hb (fun σ hσ => chiC0_le_large_table hσ)
    have hs := afe_maxima_of_table_certificates (h := (79789 / 2)) (t₀ := 10000000000)
      (A := 1160079345 / 1000000000) (R := 1160079345 / 1000000000) (B := (1 / 1000000000000)) (D := (923147 / 25000000000000000))
      (by linarith [Real.pi_lt_four]) (by norm_num) (by norm_num)
      (fun σ hσ => afeSourceA0_large_symmetric_cap hσ)
      (fun σ hσ => afeSourceA0_large_symmetric_cap ⟨hσ.1, by linarith [hσ.2]⟩) hb
      (fun σ hσ => chiC0_le_large_table hσ)
    have hd := afeDelta0_le_large_table
    norm_num [tableOneHeight, tableOneSymmetricCutoff, proposedTableOneDirect, proposedTableOneReflected,
      proposedTableOneSymmetric, proposedTableOneDelta] at hm hs hd ⊢
    exact ⟨by linarith [hm.1], by linarith [hm.2], by linarith [hs.1], hd⟩
  · have hb (σ : ℝ) (hσ : 0 ≤ σ) : afeSourceB0 σ (3000000000000) ≤ (1 / 1000000000000) := by
      have hb := afeSourceB0_le_inv_sq hσ (t₀ := 3000000000000) (by linarith [Real.pi_lt_four])
      norm_num at hb
      linarith
    have hm := afe_maxima_of_table_certificates (h := 3 / 2) (t₀ := 3000000000000)
      (A := 1750688844 / 1000000000) (R := 1750688657 / 1000000000) (B := (1 / 1000000000000)) (D := (1230863 / 10000000000000000000))
      (by linarith [Real.pi_lt_four]) (by norm_num) (by norm_num)
      (fun σ hσ => afeSourceA0_trillion_direct_cap hσ)
      (fun σ hσ => afeSourceA0_trillion_reflected_cap hσ) hb (fun σ hσ => chiC0_le_trillion_table hσ)
    have hs := afe_maxima_of_table_certificates (h := (1381977 / 2)) (t₀ := 3000000000000)
      (A := 1160048318 / 1000000000) (R := 1160048318 / 1000000000) (B := (1 / 1000000000000)) (D := (1230863 / 10000000000000000000))
      (by linarith [Real.pi_lt_four]) (by norm_num) (by norm_num)
      (fun σ hσ => afeSourceA0_trillion_symmetric_cap hσ)
      (fun σ hσ => afeSourceA0_trillion_symmetric_cap ⟨hσ.1, by linarith [hσ.2]⟩) hb
      (fun σ hσ => chiC0_le_trillion_table hσ)
    have hd := afeDelta0_le_trillion_table
    norm_num [tableOneHeight, tableOneSymmetricCutoff, proposedTableOneDirect, proposedTableOneReflected,
      proposedTableOneSymmetric, proposedTableOneDelta] at hm hs hd ⊢
    exact ⟨by linarith [hm.1], by linarith [hm.2], by linarith [hs.1], hd⟩


/-- The proposed direct Table 1 column bounds the actual two-polynomial AFE at every source height. -/
theorem proposed_table_one_direct {σ t x y : ℝ} {r : ℕ} (hr : r ≤ 3)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : tableOneHeight r ≤ |t|)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2) (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2)
    (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      (Real.log y / Real.pi + proposedTableOneDirect r) *
        (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  have hparams := table_one_parameters hr
  have hs := afe_uniform_max_direct hσ hparams.1 ht (by norm_num : (3 / 2 : ℝ) ≤ 3 / 2)
    (half_integer_ge_three_halves hx hxhalf) (half_integer_ge_three_halves hy hyhalf) hyx hxhalf hyhalf hscale
  have hm := (proposed_table_one_constants hr).1
  have hc : Real.log y / Real.pi + afeDirectMaximum (3 / 2) (tableOneHeight r) ≤
      Real.log y / Real.pi + proposedTableOneDirect r := by linarith
  exact hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by linarith : 0 ≤ y) _))

/-- The proposed reflected Table 1 column retains both the certified logarithmic coefficient and remainder. -/
theorem proposed_table_one_reflected {σ t x y : ℝ} {r : ℕ} (hr : r ≤ 3)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : tableOneHeight r ≤ |t|)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x ≤ y)
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2) (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2)
    (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      ((1 + proposedTableOneDelta r) / Real.pi * Real.log x + proposedTableOneReflected r) * x ^ (-σ) := by
  have hparams := table_one_parameters hr
  have hs := afe_uniform_max_reflected hσ hparams.1 ht (by norm_num : (3 / 2 : ℝ) ≤ 3 / 2)
    (half_integer_ge_three_halves hx hxhalf) (half_integer_ge_three_halves hy hyhalf) hxy hxhalf hyhalf hscale
  have hm := proposed_table_one_constants hr
  have hc := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
    (show 1 + afeDelta0 (tableOneHeight r) ≤ 1 + proposedTableOneDelta r by linarith [hm.2.2.2])
    Real.pi_pos.le) (Real.log_nonneg hx)
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith : 0 ≤ x) _)
  linarith [hm.2.1]

/-- The proposed symmetric Table 1 column uses the cutoff forced by height and the actual diagonal scale. -/
theorem proposed_table_one_symmetric {σ t x : ℝ} {r : ℕ} (hr : r ≤ 3)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : tableOneHeight r ≤ |t|) (hx : 1 ≤ x)
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * x = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x x‖ ≤
      (Real.log x / Real.pi + proposedTableOneSymmetric r) * x ^ (-σ) := by
  have hparams := table_one_parameters hr
  have hxpos : 0 < x := by linarith
  have hcut := table_one_symmetric_cutoff hr hx hxhalf (show tableOneHeight r ≤ 2 * Real.pi * x * x by rwa [hscale])
  have hs := afe_uniform_max_direct hσ hparams.1 ht hparams.2 hcut hcut (le_refl x) hxhalf hxhalf hscale
  rw [mul_assoc, afe_scale_power_identity σ hxpos hxpos hscale,
    div_self (Real.rpow_pos_of_pos hxpos (1 / 2 : ℝ)).ne', mul_one] at hs
  have hm := (proposed_table_one_constants hr).2.2.1
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxpos.le _)
  linarith


/-- The symmetric cutoff values equal the paper's literal floor-of-square-root formula. -/
theorem table_one_symmetric_cutoff_eq_source {r : ℕ} (hr : r ≤ 3) :
    tableOneSymmetricCutoff r = (⌊Real.sqrt (tableOneHeight r / (2 * Real.pi))⌋₊ : ℝ) + 1 / 2 := by
  interval_cases r
  · norm_num [tableOneSymmetricCutoff, tableOneHeight, div_self (by positivity : 2 * Real.pi ≠ 0)]
  · have hf : ⌊Real.sqrt ((1000 : ℝ) / (2 * Real.pi))⌋₊ = 12 := by
      apply (Nat.floor_eq_iff (Real.sqrt_nonneg _)).mpr
      constructor
      · apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
        apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
        norm_num
        nlinarith [Real.pi_lt_d20]
      · apply (Real.sqrt_lt (by positivity) (by norm_num)).mpr
        apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
        norm_num
        nlinarith [Real.pi_gt_d20]
    have he : ((25 : ℝ) / 2) = (⌊Real.sqrt ((1000 : ℝ) / (2 * Real.pi))⌋₊ : ℝ) + 1 / 2 := by
      rw [hf]
      norm_num
    convert he using 1
    norm_num [tableOneSymmetricCutoff, tableOneHeight]
  · have hf : ⌊Real.sqrt ((10000000000 : ℝ) / (2 * Real.pi))⌋₊ = 39894 := by
      apply (Nat.floor_eq_iff (Real.sqrt_nonneg _)).mpr
      constructor
      · apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
        apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
        norm_num
        nlinarith [Real.pi_lt_d20]
      · apply (Real.sqrt_lt (by positivity) (by norm_num)).mpr
        apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
        norm_num
        nlinarith [Real.pi_gt_d20]
    have he : ((79789 : ℝ) / 2) = (⌊Real.sqrt ((10000000000 : ℝ) / (2 * Real.pi))⌋₊ : ℝ) + 1 / 2 := by
      rw [hf]
      norm_num
    convert he using 1
    norm_num [tableOneSymmetricCutoff, tableOneHeight]
  · have hf : ⌊Real.sqrt ((3000000000000 : ℝ) / (2 * Real.pi))⌋₊ = 690988 := by
      apply (Nat.floor_eq_iff (Real.sqrt_nonneg _)).mpr
      constructor
      · apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
        apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
        norm_num
        nlinarith [Real.pi_lt_d20]
      · apply (Real.sqrt_lt (by positivity) (by norm_num)).mpr
        apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
        norm_num
        nlinarith [Real.pi_gt_d20]
    have he : ((1381977 : ℝ) / 2) = (⌊Real.sqrt ((3000000000000 : ℝ) / (2 * Real.pi))⌋₊ : ℝ) + 1 / 2 := by
      rw [hf]
      norm_num
    convert he using 1
    norm_num [tableOneSymmetricCutoff, tableOneHeight]

end DhimanKadiriQuesadaHerrera2026
