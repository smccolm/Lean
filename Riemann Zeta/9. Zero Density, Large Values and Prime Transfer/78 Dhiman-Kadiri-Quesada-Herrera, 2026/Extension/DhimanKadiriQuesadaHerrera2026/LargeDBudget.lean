import DhimanKadiriQuesadaHerrera2026.CubicFour
import DhimanKadiriQuesadaHerrera2026.AFEBandConstants

namespace DhimanKadiriQuesadaHerrera2026

/-- A rational lower estimate for the exact stationary scale factor. -/
theorem stationary_scale_lower :
    (0.969 : ℝ) ≤ (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ) := by
  let q := (3 / Real.pi) ^ (2 / 3 : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq3 : q ^ 3 = (3 / Real.pi) ^ 2 := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 3 / Real.pi)]
    norm_num
  have hp : Real.pi ^ 2 ≤ 9.87 := by nlinarith [Real.pi_lt_d6, Real.pi_pos]
  have hq3' : q ^ 3 * Real.pi ^ 2 = 9 := by rw [hq3]; field_simp; ring
  have hh : (0.969 : ℝ) ≤ q := by
    by_contra hn
    have hcube : q ^ 3 < (0.969 : ℝ) ^ 3 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 0.969 - q) (sq_nonneg q)]
    have hm := mul_le_mul_of_nonneg_right hp (pow_nonneg hq 3)
    nlinarith
  simpa only [q, Real.div_rpow (by norm_num : (0 : ℝ) ≤ 3) Real.pi_pos.le] using hh

/-- The unused 0.11 stationary coefficient supplies a fixed length allowance when D≥4. -/
theorem large_D_nonlinear_lower {D : ℝ} (hD : 4 ≤ D) :
    (0.169 : ℝ) ≤ (0.11 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) := by
  have hDn : 0 ≤ D := by linarith
  let r := D ^ (1 / 3 : ℝ)
  have hr : 0 ≤ r := Real.rpow_nonneg hDn _
  have hr3 : r ^ 3 = D := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hDn]
    norm_num
  have hrlo : (1.587 : ℝ) ≤ r := by
    by_contra hn
    have hm := mul_nonneg (by linarith : 0 ≤ 1.587 - r) (sq_nonneg r)
    nlinarith
  have hh := mul_le_mul_of_nonneg_right stationary_scale_lower hr
  change 0.169 ≤ (0.11 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * r
  norm_num only [div_eq_mul_inv] at hh ⊢
  nlinarith only [hh, hrlo]

/-- The digamma series lies above its chord from one to two. -/
theorem digamma_unit_chord {d : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    d - Real.eulerMascheroniConstant ≤ (Complex.digamma (1 + d : ℝ)).re := by
  have h := hasSum_real_digamma (by positivity : 0 < 1 + d)
  have htwo := hasSum_real_digamma (by norm_num : (0 : ℝ) < 2)
  have hv := real_digamma_add_one (by norm_num : (0 : ℝ) < 1)
  norm_num only [Complex.ofReal_one, real_digamma_one, one_div_one] at hv
  have hs := htwo.mul_left d
  have ht (n : ℕ) : d * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) ≤
      1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + (1 + d)) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have he : 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + (1 + d)) =
        d / (((n : ℝ) + 1) * ((n : ℝ) + (1 + d))) := by field_simp; ring
    have he' : d * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) =
        d / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by field_simp; ring
    rw [he, he']
    apply div_le_div_of_nonneg_left hd (by positivity)
    nlinarith
  have hh := hs.summable.tsum_le_tsum ht h.summable
  rw [hs.tsum_eq, h.tsum_eq] at hh
  rw [hv] at hh
  linarith

/-- Half of each near-frequency bound is paid by a small quadratic allowance. -/
theorem large_D_near_budget {x w d : ℝ} (hw : 0 < w) :
    min (0.6715 * x) (1 / (Real.pi * d)) ≤
      0.1585 * x + 0.01 * w * x ^ 2 + 1 / (2 * Real.pi * d) + 0.786 / w := by
  have h₁ := min_le_left (0.6715 * x) (1 / (Real.pi * d))
  have h₂ := min_le_right (0.6715 * x) (1 / (Real.pi * d))
  have hquad : 0.17725 * x ≤ 0.01 * w * x ^ 2 + 0.786 / w := by
    apply (mul_le_mul_iff_left₀ hw).mp
    have he : (0.01 * w * x ^ 2 + 0.786 / w) * w = 0.01 * (w * x) ^ 2 + 0.786 := by field_simp
    rw [he]
    nlinarith [sq_nonneg (w * x - 8.8625)]
  have he : 1 / (2 * Real.pi * d) = (1 / (Real.pi * d)) / 2 := by ring
  rw [he]
  linarith

/-- A rational residual after the logarithmic tangent estimate. -/
theorem large_D_rational_residual {w : ℝ} (hw : 25 ≤ w) :
    0.786 / w - 0.397 / (w + 3) ≤ 0.018 := by
  have hp : 0 < w := by linarith
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < w * (w + 3))).mp
  have he : (0.786 / w - 0.397 / (w + 3)) * (w * (w + 3)) = 0.389 * w + 2.358 := by field_simp; ring
  rw [he]
  nlinarith [mul_nonneg (by linarith : 0 ≤ w - 25) hp.le]


/-- A global tangent bound for the logarithm of a shifted square above five. -/
theorem log_square_tangent_six {u : ℝ} (hu : 5 ≤ u) :
    Real.log (u ^ 2 + 2) ≤ (6 / 19 : ℝ) * u + Real.log 38 - 36 / 19 := by
  have hd (v : ℝ) : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + 2)) (2 * v / (v ^ 2 + 2)) v := by
    convert (((hasDerivAt_id v).pow 2).add_const 2).log (by positivity : v ^ 2 + 2 ≠ 0) using 1
    norm_num
  by_cases h6 : u ≤ 6
  · have h := (convex_Icc u 6).mul_sub_le_image_sub_of_le_deriv (C := (6 / 19 : ℝ))
      (fun v _ => (hd v).continuousAt.continuousWithinAt)
      (fun v _ => (hd v).differentiableAt.differentiableWithinAt)
      (fun v hv => by
        rw [(hd v).deriv]
        apply (le_div_iff₀ (by positivity : 0 < v ^ 2 + 2)).mpr
        have hvs : v ∈ Set.Ioo u 6 := by simpa only [interior_Icc] using hv
        obtain ⟨hvl, hvr⟩ := hvs
        nlinarith [mul_nonneg (by linarith : 0 ≤ 6 - v) (by linarith : 0 ≤ v - 1 / 3)])
      u (Set.left_mem_Icc.mpr h6) 6 (Set.right_mem_Icc.mpr h6) h6
    norm_num at h
    linarith
  · have h6' : 6 ≤ u := le_of_not_ge h6
    have h := (convex_Icc 6 u).image_sub_le_mul_sub_of_deriv_le (C := (6 / 19 : ℝ))
      (fun v _ => (hd v).continuousAt.continuousWithinAt)
      (fun v _ => (hd v).differentiableAt.differentiableWithinAt)
      (fun v hv => by
        rw [(hd v).deriv]
        apply (div_le_iff₀ (by positivity : 0 < v ^ 2 + 2)).mpr
        have hvs : v ∈ Set.Ioo 6 u := by simpa only [interior_Icc] using hv
        obtain ⟨hvl, hvr⟩ := hvs
        nlinarith [mul_nonneg (by linarith : 0 ≤ v - 6) (by linarith : 0 ≤ v - 1 / 3)])
      6 (Set.left_mem_Icc.mpr h6') u (Set.right_mem_Icc.mpr h6') h6'
    norm_num at h
    linarith

/-- A global rational square-root logarithm estimate with a certified anchor. -/
theorem log_square_sharp {u : ℝ} (hu : 5 ≤ u) :
    Real.log (u ^ 2 + 2) ≤ 0.314 * u + 1.754 := by
  have hlog : Real.log (38 : ℝ) ≤ 3.6376 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 38)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3.6376) 22
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hshort {v : ℝ} (hv : 5 ≤ v) (hv' : v ≤ 6.1) : Real.log (v ^ 2 + 2) ≤ 0.314 * v + 1.754 := by
    have ht := log_square_tangent_six hv
    linarith
  by_cases h6 : u ≤ 6.1
  · exact hshort hu h6
  · have h6' : 6.1 ≤ u := le_of_not_ge h6
    have hd (v : ℝ) : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + 2)) (2 * v / (v ^ 2 + 2)) v := by
      convert (((hasDerivAt_id v).pow 2).add_const 2).log (by positivity : v ^ 2 + 2 ≠ 0) using 1
      norm_num
    have h := (convex_Icc 6.1 u).image_sub_le_mul_sub_of_deriv_le (C := (0.314 : ℝ))
      (fun v _ => (hd v).continuousAt.continuousWithinAt)
      (fun v _ => (hd v).differentiableAt.differentiableWithinAt)
      (fun v hv => by
        rw [(hd v).deriv]
        apply (div_le_iff₀ (by positivity : 0 < v ^ 2 + 2)).mpr
        have hvs : v ∈ Set.Ioo 6.1 u := by simpa only [interior_Icc] using hv
        obtain ⟨hvl, hvr⟩ := hvs
        nlinarith [mul_nonneg (by linarith : 0 ≤ v - 6.1) (by linarith : 0 ≤ v - 6.1)])
      6.1 (Set.left_mem_Icc.mpr h6') u (Set.right_mem_Icc.mpr h6') h6'
    have ha := hshort (v := 6.1) (by norm_num) (le_refl _)
    linarith

/-- The far-frequency logarithm is controlled with explicit rational constants. -/
theorem large_D_log_bound {β : ℝ} (hβ : 26 ≤ β) :
    Real.log (β + 1) ≤ 0.314 * Real.sqrt (β - 1) + 1.754 := by
  have hb : 0 ≤ β - 1 := by linarith
  have hs := Real.sq_sqrt hb
  have hp := Real.sqrt_nonneg (β - 1)
  have h := log_square_sharp (u := Real.sqrt (β - 1)) (by nlinarith)
  simpa only [hs, show β - 1 + 2 = β + 1 by ring] using h

/-- The complete elementary gap/logarithm expression fits the square-root budget above frequency 26. -/
theorem large_D_log_gap_budget {β d : ℝ} (hβ : 26 ≤ β) (hd : 0 < d) (hd1 : d ≤ 1) :
    (2 * Real.log (β + 1) + 2.433432 - d - 1.25 / (β + 2)) / Real.pi - 1.751 +
      1 / (2 * Real.pi * d) + 0.786 / (β - 1) ≤ 0.2 * Real.sqrt (β - 1) / d := by
  have hbp : 0 < β - 1 := by linarith
  have hlog := large_D_log_bound hβ
  have hres := large_D_rational_residual (w := β - 1) (by linarith)
  have hs := Real.sqrt_nonneg (β - 1)
  have hlo : 3 ≤ Real.log (β + 1) := by
    have hl3 : (1 : ℝ) ≤ Real.log 3 := by
      apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).mpr
      exact Real.exp_one_lt_d9.le.trans (by norm_num)
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 27) (by linarith : 27 ≤ β + 1)
    have he : Real.log (27 : ℝ) = 3 * Real.log 3 := by rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
    rw [he] at hl
    linarith
  have hrat : 1.25 / (β + 2) ≤ 0.05 := by
    apply (div_le_iff₀ (by linarith : 0 < β + 2)).mpr
    linarith
  let A := (2 * Real.log (β + 1) + 2.433432 - 1.25 / (β + 2)) / Real.pi - 1.751 + 0.786 / (β - 1)
  have hA : 2 / Real.pi ≤ A := by
    have hpos : 0 ≤ 0.786 / (β - 1) := by positivity
    apply (mul_le_mul_iff_left₀ Real.pi_pos).mp
    dsimp [A]
    have hp := mul_nonneg hpos Real.pi_pos.le
    simp only [add_mul, sub_mul, div_mul_cancel₀ _ Real.pi_ne_zero]
    nlinarith [Real.pi_lt_d2]
  have hline : (2 * Real.log (β + 1) + 1.933432) / Real.pi - 1.751 ≤
      0.2 * Real.sqrt (β - 1) - 0.018 := by
    have h := mul_nonneg (by linarith [Real.pi_gt_d2] : 0 ≤ Real.pi - 3.14) hs
    apply (mul_le_mul_iff_left₀ Real.pi_pos).mp
    simp only [sub_mul, div_mul_cancel₀ _ Real.pi_ne_zero]
    nlinarith [Real.pi_gt_d2]
  have hrec : 0.397 / (β + 2) ≤ 1.25 / (Real.pi * (β + 2)) := by
    apply (div_le_div_iff₀ (by linarith : 0 < β + 2) (by positivity : 0 < Real.pi * (β + 2))).mpr
    have h := mul_nonneg (by linarith [Real.pi_lt_d6] : 0 ≤ 1.25 - 0.397 * Real.pi) (by linarith : 0 ≤ β + 2)
    nlinarith only [h]
  have hmain : A - 1 / (2 * Real.pi) ≤ 0.2 * Real.sqrt (β - 1) := by
    dsimp [A]
    rw [show β - 1 + 3 = β + 2 by ring] at hres
    norm_num only [div_eq_mul_inv, mul_inv_rev] at hline hrec hres ⊢
    nlinarith only [hline, hrec, hres]
  have hprod := mul_nonneg (sub_nonneg.mpr hd1)
    (show 0 ≤ A - (1 + d) / Real.pi by
      have hh := div_le_div_of_nonneg_right (by linarith : 1 + d ≤ 2) Real.pi_pos.le
      linarith)
  apply (mul_le_mul_iff_left₀ hd).mp
  have he : ((2 * Real.log (β + 1) + 2.433432 - d - 1.25 / (β + 2)) / Real.pi - 1.751 +
      1 / (2 * Real.pi * d) + 0.786 / (β - 1)) * d =
      A * d - d ^ 2 / Real.pi + 1 / (2 * Real.pi) := by dsimp [A]; field_simp; ring
  rw [he, div_mul_cancel₀ _ hd.ne']
  norm_num only [div_eq_mul_inv, mul_inv_rev] at hprod hmain ⊢
  nlinarith only [hprod, hmain]

/-- The source curvature coefficient retains a quadratic gap allowance above frequency 26. -/
theorem large_D_curvature_coefficient {β : ℝ} (hβ : 26 ≤ β) :
    (10 / 159 : ℝ) / ((⌊β⌋₊ : ℝ) + 1 - β) ^ 2 ≤
      (printedPartIIE1 β / β + partIICubeCoefficient β) / (2 * Real.pi ^ 2) := by
  have hbp : 0 < β := by linarith
  let d := (⌊β⌋₊ : ℝ) + 1 - β
  have hd : 0 < d := by dsimp [d]; linarith [Nat.lt_floor_add_one β]
  have hd1 : d ≤ 1 := by dsimp [d]; linarith [Nat.floor_le hbp.le]
  have he := printed_constant_coefficient_expansion hbp
  change _ = 1 / d ^ 3 + 1 / (d + 1) ^ 3 + 1 / (2 * (d + 1) ^ 2) +
    1 / (β * (d + 1) ^ 2) + 1 / (2 * ((⌊β⌋₊ : ℝ) + 1) * β ^ 2) - 1 / (2 * (1 + β) ^ 2) at he
  have h₃ : (1 / 8 : ℝ) ≤ 1 / (d + 1) ^ 3 := by
    apply (le_div_iff₀ (by positivity : 0 < (d + 1) ^ 3)).mpr
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ d + 1) (by linarith : d + 1 ≤ 2) 3
    nlinarith
  have h₂ : (1 / 8 : ℝ) ≤ 1 / (2 * (d + 1) ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (d + 1) ^ 2)).mpr
    nlinarith
  have hneg : 1 / (2 * (1 + β) ^ 2) ≤ 0.001 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + β) ^ 2)).mpr
    nlinarith
  have hpos₁ : 0 ≤ 1 / (β * (d + 1) ^ 2) := by positivity
  have hpos₂ : 0 ≤ 1 / (2 * ((⌊β⌋₊ : ℝ) + 1) * β ^ 2) := by positivity
  have hF : 1 / d ^ 3 + 0.249 ≤ printedPartIIE1 β / β + partIICubeCoefficient β := by linarith
  have hpoly : 1.242 * d ≤ 1 + 0.249 * d ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (d - 1)) (by positivity : 0 ≤ d + 2)]
  have hbase : 1.242 / d ^ 2 ≤ 1 / d ^ 3 + 0.249 := by
    apply (mul_le_mul_iff_left₀ (pow_pos hd 3)).mp
    have h₁ : (1.242 / d ^ 2) * d ^ 3 = 1.242 * d := by field_simp
    have h₂ : (1 / d ^ 3 + 0.249) * d ^ 3 = 1 + 0.249 * d ^ 3 := by field_simp
    rw [h₁, h₂]
    exact hpoly
  have hp : Real.pi ^ 2 ≤ 9.87 := by nlinarith [Real.pi_lt_d6, Real.pi_pos]
  have hconst : (10 / 159 : ℝ) ≤ 1.242 / (2 * Real.pi ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi ^ 2)).mpr
    nlinarith
  have hb := div_le_div_of_nonneg_right (hbase.trans hF) (by positivity : 0 ≤ 2 * Real.pi ^ 2)
  have hc := div_le_div_of_nonneg_right hconst (sq_nonneg d)
  change (10 / 159 : ℝ) / d ^ 2 ≤ _
  have hh : (1.242 / (2 * Real.pi ^ 2)) / d ^ 2 = (1.242 / d ^ 2) / (2 * Real.pi ^ 2) := by ring
  exact (hc.trans_eq hh).trans hb

/-- A rational weighted arithmetic/geometric mean estimate. -/
theorem large_D_amgm {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hprod : w ≤ u * v) :
    0.2 * Real.sqrt w ≤ 0.159 * u + (10 / 159 : ℝ) * v := by
  have hs := Real.sq_sqrt hw
  have hn := Real.sqrt_nonneg w
  nlinarith [sq_nonneg (0.159 * u - (10 / 159 : ℝ) * v)]

/-- The small-frequency direct-sum quadratic has the required absolute allowance. -/
theorem large_D_small_quadratic {β x : ℝ} (hβ : 2 ≤ β) (hβ18 : β ≤ 18) :
    (β - 2.686) * x ≤ 2 * (β - 1) * x ^ 2 + 1.75 := by
  have hp : 0 < β - 1 := by linarith
  have hdisc : (β - 2.686) ^ 2 ≤ 14 * (β - 1) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ β - 2) (by linarith : 0 ≤ 18 - β)]
  have hs := sq_nonneg (4 * (β - 1) * x - (β - 2.686))
  have hm : 0 ≤ (2 * (β - 1) * x ^ 2 + 1.75 - (β - 2.686) * x) * (8 * (β - 1)) := by
    nlinarith only [hs, hdisc]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (by positivity : 0 < 8 * (β - 1))).mp hm)

/-- The middle-frequency direct-sum quadratic uses one extra unit of the positive logarithm. -/
theorem large_D_middle_quadratic {β x : ℝ} (hβ : 18 ≤ β) (hβ26 : β ≤ 26) :
    (β - 2.686) * x ≤ 2 * (β - 1) * x ^ 2 + 2.75 := by
  have hp : 0 < β - 1 := by linarith
  have hdisc : (β - 2.686) ^ 2 ≤ 22 * (β - 1) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ β - 18) (by linarith : 0 ≤ 26 - β)]
  have hs := sq_nonneg (4 * (β - 1) * x - (β - 2.686))
  have hm : 0 ≤ (2 * (β - 1) * x ^ 2 + 2.75 - (β - 2.686) * x) * (8 * (β - 1)) := by
    nlinarith only [hs, hdisc]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (by positivity : 0 < 8 * (β - 1))).mp hm)

/-- The exact enlarged-cutoff Poisson expression has a sharp elementary logarithmic majorant. -/
theorem large_D_poisson_excess {α β : ℝ} (hαp : 0 < α) (hα : α < 1) (hβ : 26 ≤ β) :
    let d := (⌊β⌋₊ : ℝ) + 1 - β
    let P := (Real.log ((⌊β⌋₊ : ℝ) + 2) - 1 / (2 * ((⌊β⌋₊ : ℝ) + 2)) -
      (Complex.digamma ((⌊β⌋₊ : ℝ) + 2 - β : ℝ)).re + Real.eulerMascheroniConstant +
      Real.log (1 + β) - 1 / (2 * (1 + β)) + Real.log 2 + 1 / ((⌊β⌋₊ : ℝ) + 1)) / Real.pi
    let H := (α * halfSecondEndpointBound ⌊β⌋₊ α + β * halfSecondEndpointBound ⌊β⌋₊ β) / (2 * Real.pi) +
      1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi)
    2 / Real.pi + P - H ≤
      (2 * Real.log (β + 1) + 2.433432 - d - 1.25 / (β + 2)) / Real.pi - 1.751 := by
  have hbp : 0 < β := by linarith
  let d := (⌊β⌋₊ : ℝ) + 1 - β
  have hd : 0 < d := by dsimp [d]; linarith [Nat.lt_floor_add_one β]
  have hd1 : d ≤ 1 := by dsimp [d]; linarith [Nat.floor_le hbp.le]
  have hψ := digamma_unit_chord hd.le hd1
  have hdeq : 1 + d = (⌊β⌋₊ : ℝ) + 2 - β := by dsimp [d]; ring
  rw [hdeq] at hψ
  have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < (((⌊β⌋₊ : ℝ) + 2) / (β + 1)))
  rw [Real.log_div (by positivity : (⌊β⌋₊ : ℝ) + 2 ≠ 0) (by positivity : β + 1 ≠ 0)] at hl
  have he : ((⌊β⌋₊ : ℝ) + 2) / (β + 1) - 1 = d / (β + 1) := by dsimp [d]; field_simp; ring
  rw [he] at hl
  have hαq : (0.375 : ℝ) ≤ 0.75 / (α + 1) := by
    apply (le_div_iff₀ (by positivity : 0 < α + 1)).mpr
    linarith
  have hrat₁ : 0.25 / (β + 2) ≤ 0.25 / (β + 1) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hrat₂ : 0.5 / (β + 2) ≤ 0.5 / β := div_le_div_of_nonneg_left (by norm_num) hbp (by linarith)
  have hrat₃ : 0.5 / (β + 2) ≤ 1 / (2 * ((⌊β⌋₊ : ℝ) + 2)) := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 0.5)
      (by positivity : 0 < (⌊β⌋₊ : ℝ) + 2) (by linarith [Nat.floor_le hbp.le] : (⌊β⌋₊ : ℝ) + 2 ≤ β + 2)
    convert h using 1
    field_simp
    norm_num
  have hratd := div_le_div_of_nonneg_right hd1 (by positivity : 0 ≤ β + 1)
  have hh := printed_half_remainder_expand hαp hbp ⌊β⌋₊
  dsimp only
  rw [hh]
  apply (mul_le_mul_iff_left₀ Real.pi_pos).mp
  have hlog2 : (0.692 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnum : 2 + Real.log ((⌊β⌋₊ : ℝ) + 2) - 1 / (2 * ((⌊β⌋₊ : ℝ) + 2)) -
      (Complex.digamma ((⌊β⌋₊ : ℝ) + 2 - β : ℝ)).re + Real.eulerMascheroniConstant +
      Real.log (β + 1) - 1 / (2 * (β + 1)) + Real.log 2 + 1 / ((⌊β⌋₊ : ℝ) + 1) -
      (1 / ((⌊β⌋₊ : ℝ) + 1) + 1.5 * Real.log 2 + 0.75 / (α + 1) + 0.75 / (β + 1) + 0.5 / β) ≤
      2 * Real.log (β + 1) + 2.433432 - d - 1.25 / (β + 2) := by
    norm_num only [div_eq_mul_inv, mul_inv_rev] at hl hrat₁ hrat₂ hrat₃ hratd hαq ⊢
    nlinarith only [hl, hrat₁, hrat₂, hrat₃, hratd, hαq, hψ, hlog2, euler_constant_le_precise]
  simp only [add_mul, sub_mul, div_mul_cancel₀ _ Real.pi_ne_zero]
  norm_num only [show 1 + β = β + 1 by ring, div_eq_mul_inv, mul_inv_rev] at hnum ⊢
  dsimp [d] at hnum
  nlinarith only [hnum]

/-- The curvature and length terms jointly pay the complete far-frequency square-root budget. -/
theorem large_D_curvature_length {β K κ : ℝ} (hβ : 26 ≤ β) (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hprod : β - 1 ≤ K * κ) :
    0.2 * Real.sqrt (β - 1) / ((⌊β⌋₊ : ℝ) + 1 - β) ≤
      0.159 * K + κ / (2 * Real.pi ^ 2) * (printedPartIIE1 β / β + partIICubeCoefficient β) := by
  let d := (⌊β⌋₊ : ℝ) + 1 - β
  have hd : 0 < d := by dsimp [d]; linarith [Nat.lt_floor_add_one β]
  have ha := large_D_amgm (u := K * d) (v := κ / d) (w := β - 1)
    (by positivity) (by positivity) (by linarith) (by convert hprod using 1; field_simp)
  have ha' := div_le_div_of_nonneg_right ha hd.le
  have hc := mul_le_mul_of_nonneg_left (large_D_curvature_coefficient hβ) hκ
  change κ * ((10 / 159 : ℝ) / d ^ 2) ≤ _ at hc
  change 0.2 * Real.sqrt (β - 1) / d ≤ _
  have he : (0.159 * (K * d) + (10 / 159 : ℝ) * (κ / d)) / d = 0.159 * K + κ * ((10 / 159 : ℝ) / d ^ 2) := by field_simp
  rw [he] at ha'
  norm_num only [div_eq_mul_inv, mul_inv_rev] at ha' hc ⊢
  nlinarith only [ha', hc]

end DhimanKadiriQuesadaHerrera2026
