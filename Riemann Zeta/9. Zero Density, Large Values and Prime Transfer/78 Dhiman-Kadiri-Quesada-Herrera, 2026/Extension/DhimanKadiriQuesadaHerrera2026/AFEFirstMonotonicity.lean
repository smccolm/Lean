import DhimanKadiriQuesadaHerrera2026.AFEFirstKind

/-! # Analytic monotonicity for the real-cutoff AFE1 transfer -/

namespace DhimanKadiriQuesadaHerrera2026

/-- The actual real digamma function is monotone on the positive axis, by its convergent series. -/
theorem real_digamma_monotone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (Complex.digamma (x : ℂ)).re ≤ (Complex.digamma (y : ℂ)).re := by
  have hd := hasSum_digamma_difference hx (hx.trans_le hxy)
  have hn : 0 ≤ ∑' n : ℕ, (1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + y)) := by
    apply tsum_nonneg
    intro n
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [hd.tsum_eq] at hn
  exact sub_nonneg.mp hn

/-- An explicit finite-difference bound for digamma, without assuming a numerical derivative. -/
theorem real_digamma_difference_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (Complex.digamma (y : ℂ)).re - (Complex.digamma (x : ℂ)).re ≤
      (y - x) * (1 / x ^ 2 + 1 / x) := by
  have hy := hx.trans_le hxy
  have hd := hasSum_digamma_difference hx hy
  have hs := reciprocal_square_series_bounds hx
  have hterm (n : ℕ) : 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + y) ≤
      (y - x) * (1 / ((n : ℝ) + x) ^ 2) := by
    have hx' : 0 < (n : ℝ) + x := by positivity
    have hy' : 0 < (n : ℝ) + y := by positivity
    have he : 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + y) =
        (y - x) / (((n : ℝ) + x) * ((n : ℝ) + y)) := by
      field_simp
      ring
    rw [he, mul_one_div]
    apply div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) (sq_pos_of_pos hx')
    nlinarith
  have he := hd.summable.tsum_le_tsum hterm (hs.1.mul_left (y - x))
  rw [hd.tsum_eq, tsum_mul_left] at he
  exact he.trans (mul_le_mul_of_nonneg_left hs.2.2 (sub_nonneg.mpr hxy))

/-- The exact AFE factor increases on its entire allowed interval. -/
theorem afePartIFactor_monotone {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1) :
    afePartIFactor u ≤ afePartIFactor v := by
  have hl := Real.log_le_log (by linarith : 0 < 1 + u) (by linarith : 1 + u ≤ 1 + v)
  have hd := real_digamma_monotone (by linarith : 0 < 1 - v) (by linarith : 1 - v ≤ 1 - u)
  have hr := one_div_le_one_div_of_le (by linarith : 0 < 2 * (1 + u))
    (by linarith : 2 * (1 + u) ≤ 2 * (1 + v))
  unfold afePartIFactor
  linarith

/-- The ratio m(c)/c decreases for every allowed c, with no sampled monotonicity premise. -/
theorem afeFirstConstant_div_antitone {c d t₀ : ℝ} (ht₀ : 0 < t₀)
    (hc : 1 / (2 * Real.pi) < c) (hcd : c ≤ d) :
    afeFirstConstant d t₀ / d ≤ afeFirstConstant c t₀ / c := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hcpos : 0 < c := (one_div_pos.mpr hπ).trans hc
  have hdpos : 0 < d := hcpos.trans_le hcd
  have hud : 0 < 1 / (2 * Real.pi * d) := by positivity
  have huc1 : 1 / (2 * Real.pi * c) < 1 := by
    apply (div_lt_one (mul_pos hπ hcpos)).mpr
    have he := (div_lt_iff₀ hπ).mp hc
    nlinarith
  have hdu : 1 / (2 * Real.pi * d) ≤ 1 / (2 * Real.pi * c) :=
    one_div_le_one_div_of_le (mul_pos hπ hcpos) (mul_le_mul_of_nonneg_left hcd hπ.le)
  have hf := afePartIFactor_monotone hud hdu huc1
  have hfn := afePartIFactor_nonneg (by positivity) huc1
  have hquot : afePartIFactor (1 / (2 * Real.pi * d)) / d ≤
      afePartIFactor (1 / (2 * Real.pi * c)) / c :=
    (div_le_div_of_nonneg_right hf hdpos.le).trans
      (div_le_div_of_nonneg_left hfn hcpos hcd)
  have he := mul_le_mul_of_nonneg_left hquot
    (show 0 ≤ (1 / Real.pi) * (1 / t₀ + 1) by positivity)
  unfold afeFirstConstant
  have hcne := hcpos.ne'
  have hdne := hdpos.ne'
  field_simp at he ⊢
  nlinarith

/-- A uniform finite-difference estimate for the exact factor on the small-frequency interval. -/
theorem afePartIFactor_difference_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1 / 6) :
    afePartIFactor v - afePartIFactor u ≤ 5 * (v - u) := by
  have hvpos : 0 < v := hu.trans_le huv
  have hx : 0 < 1 - v := by linarith
  have hxlo : (5 / 6 : ℝ) ≤ 1 - v := by linarith
  have hrec := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5 / 6) hxlo
  have hsquare := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (5 / 6 : ℝ) ^ 2)
    (show (5 / 6 : ℝ) ^ 2 ≤ (1 - v) ^ 2 by nlinarith)
  norm_num at hrec hsquare
  have hd := real_digamma_difference_le hx (show 1 - v ≤ 1 - u by linarith)
  have hψ : (Complex.digamma ((1 - u : ℝ) : ℂ)).re -
      (Complex.digamma ((1 - v : ℝ) : ℂ)).re ≤ 3 * (v - u) := by
    have hb : 1 / (1 - v) ^ 2 + 1 / (1 - v) ≤ 3 := by
      simp only [one_div]
      linarith
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ v - u by linarith)
    have he : 1 - u - (1 - v) = v - u := by ring
    rw [he] at hd
    nlinarith
  have hu1 : 0 < 1 + u := by linarith
  have hv1 : 0 < 1 + v := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hv1 hu1)
  rw [Real.log_div hv1.ne' hu1.ne'] at hl
  have hlrat : (1 + v) / (1 + u) - 1 ≤ v - u := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hu1).mpr
    nlinarith [mul_nonneg hu.le (sub_nonneg.mpr huv)]
  have hlog : Real.log (1 + v) - Real.log (1 + u) ≤ v - u := hl.trans hlrat
  have he : 1 / (2 * (1 + u)) - 1 / (2 * (1 + v)) =
      (v - u) / (2 * (1 + u) * (1 + v)) := by
    field_simp
    ring
  have hden : 1 ≤ 2 * (1 + u) * (1 + v) := by nlinarith [mul_pos hu hvpos]
  have hrat : 1 / (2 * (1 + u)) - 1 / (2 * (1 + v)) ≤ v - u := by
    rw [he]
    exact div_le_self (sub_nonneg.mpr huv) hden
  unfold afePartIFactor
  linarith

/-- The exact m(c) increases for c≥1 and t₀≥1; this includes the entire source transfer interval. -/
theorem afeFirstConstant_monotone {c d t₀ : ℝ} (ht₀ : 1 ≤ t₀) (hc : 1 ≤ c) (hcd : c ≤ d) :
    afeFirstConstant c t₀ ≤ afeFirstConstant d t₀ := by
  have hcpos : 0 < c := by linarith
  have hdpos : 0 < d := by linarith
  have htpos : 0 < t₀ := by linarith
  have hπ : 0 < 2 * Real.pi := by positivity
  have hud : 0 < 1 / (2 * Real.pi * d) := by positivity
  have hdu : 1 / (2 * Real.pi * d) ≤ 1 / (2 * Real.pi * c) :=
    one_div_le_one_div_of_le (mul_pos hπ hcpos) (mul_le_mul_of_nonneg_left hcd hπ.le)
  have hπ3 : 3 < Real.pi := Real.pi_gt_three
  have huc6 : 1 / (2 * Real.pi * c) ≤ 1 / 6 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hf := afePartIFactor_difference_le hud hdu huc6
  have hu_diff : 1 / (2 * Real.pi * c) - 1 / (2 * Real.pi * d) ≤ (d - c) / 6 := by
    have he : 1 / (2 * Real.pi * c) - 1 / (2 * Real.pi * d) =
        (d - c) / (2 * Real.pi * c * d) := by field_simp
    rw [he]
    apply div_le_div_of_nonneg_left (sub_nonneg.mpr hcd) (by norm_num)
    have hprod : 1 ≤ c * d := by nlinarith
    nlinarith
  have hF : afePartIFactor (1 / (2 * Real.pi * c)) -
      afePartIFactor (1 / (2 * Real.pi * d)) ≤ (5 / 6) * (d - c) := by
    linarith
  have hK0 : 0 ≤ (1 / Real.pi) * (1 / t₀ + 1) := by positivity
  have hK1 : (1 / Real.pi) * (1 / t₀ + 1) ≤ 1 := by
    have hti : 1 / t₀ ≤ 1 := (div_le_one htpos).mpr ht₀
    rw [show (1 / Real.pi) * (1 / t₀ + 1) = (1 / t₀ + 1) / Real.pi by ring]
    exact (div_le_one Real.pi_pos).mpr (by linarith)
  have hnonneg : 0 ≤ (5 / 6 : ℝ) * (d - c) := by positivity
  have he := (mul_le_mul_of_nonneg_left hF hK0).trans
    (mul_le_mul_of_nonneg_right hK1 hnonneg)
  unfold afeFirstConstant
  nlinarith

/-- The actual first-AFE constant is positive throughout its source domain. -/
theorem afeFirstConstant_pos {c t₀ : ℝ} (ht₀ : 0 < t₀) (hc : 1 / (2 * Real.pi) < c) :
    0 < afeFirstConstant c t₀ := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hcpos : 0 < c := (one_div_pos.mpr hπ).trans hc
  have hu1 : 1 / (2 * Real.pi * c) < 1 := by
    apply (div_lt_one (mul_pos hπ hcpos)).mpr
    have he := (div_lt_iff₀ hπ).mp hc
    nlinarith
  have hf := afePartIFactor_nonneg (by positivity) hu1
  unfold afeFirstConstant
  positivity

/-- Above unit scale the weight loses no factor. -/
theorem afeFirstConstant_mul_rpow_le_self {c t₀ sigma : ℝ} (ht₀ : 0 < t₀)
    (hc : 1 ≤ c) (hsigma : 0 ≤ sigma) :
    afeFirstConstant c t₀ * c ^ (-sigma) ≤ afeFirstConstant c t₀ := by
  have hthreshold : 1 / (2 * Real.pi) < c := by
    have hπ : 0 < 2 * Real.pi := by positivity
    apply (div_lt_iff₀ hπ).mpr
    nlinarith [Real.pi_gt_three]
  exact mul_le_of_le_one_right (afeFirstConstant_pos ht₀ hthreshold).le
    (Real.rpow_le_one_of_one_le_of_nonpos hc (neg_nonpos.mpr hsigma))

/-- Below unit scale the full σ interval is controlled by m(c)/c. -/
theorem afeFirstConstant_mul_rpow_le_div {c t₀ sigma : ℝ} (ht₀ : 0 < t₀)
    (hc : 1 / (2 * Real.pi) < c) (hc1 : c ≤ 1) (hsigma : sigma ≤ 1) :
    afeFirstConstant c t₀ * c ^ (-sigma) ≤ afeFirstConstant c t₀ / c := by
  have hcpos : 0 < c := (one_div_pos.mpr (by positivity : 0 < 2 * Real.pi)).trans hc
  have hr := Real.rpow_le_rpow_of_exponent_ge hcpos hc1 (show (-1 : ℝ) ≤ -sigma by linarith)
  rw [Real.rpow_neg_one] at hr
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hr (afeFirstConstant_pos ht₀ hc).le

end DhimanKadiriQuesadaHerrera2026
