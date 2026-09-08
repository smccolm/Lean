import GafniTao.SharpPerronContour

/-!
# Quantitative edge estimates for sharp Perron rectangles

The horizontal estimates keep the exact `q^s/s` integrand.  Their real
majorant is integrated exactly, so the logarithmic distance from the Perron
discontinuity remains visible.
-/

open Complex Set MeasureTheory Filter
open scoped Interval

namespace GafniTao

/-- Exact integral of a positive constant to a real power. -/
theorem intervalIntegral_const_rpow
    {q a b : ℝ} (hq : 0 < q) (hq1 : q ≠ 1) :
    (∫ u in a..b, q ^ u) = (q ^ b - q ^ a) / Real.log q := by
  have hlog : Real.log q ≠ 0 := (Real.log_ne_zero_of_pos_of_ne_one hq hq1)
  have hderiv : ∀ u : ℝ,
      HasDerivAt (fun v : ℝ => q ^ v / Real.log q) (q ^ u) u := by
    intro u
    convert ((hasDerivAt_id u).const_rpow hq).div_const (Real.log q) using 1
    simp only [id_eq]
    field_simp [hlog]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _hu => hderiv u)
    ((Real.continuous_const_rpow hq.ne').intervalIntegrable a b)]
  ring

private theorem norm_perron_horizontal_integrand_le
    {q T u : ℝ} (hq : 0 < q) (hT : 0 < T) (sign : ℝ)
    (hsign : |sign| = 1) :
    ‖(q : ℂ) ^ ((u : ℂ) + (sign * T : ℝ) * Complex.I) /
        ((u : ℂ) + (sign * T : ℝ) * Complex.I)‖ ≤
      q ^ u / T := by
  have hqnorm :
      ‖(q : ℂ) ^ ((u : ℂ) + (sign * T : ℝ) * Complex.I)‖ = q ^ u := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hq
      ((u : ℂ) + (sign * T : ℝ) * Complex.I)
  have hden : T ≤ ‖(u : ℂ) + (sign * T : ℝ) * Complex.I‖ := by
    have him := Complex.abs_im_le_norm
      ((u : ℂ) + (sign * T : ℝ) * Complex.I)
    have habs : |sign * T| = T := by
      rw [abs_mul, hsign, one_mul, abs_of_pos hT]
    simpa [habs] using him
  rw [norm_div, hqnorm]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hq.le u) hT hden

/-- A horizontal normalized rectangle edge is bounded by the exact integral
of its real-power majorant.  The sign is specialized to the two actual edges.
-/
theorem norm_HIntegral'_perron_le
    {q a b T sign : ℝ} (hq : 0 < q) (hab : a ≤ b) (hT : 0 < T)
    (hsign : |sign| = 1) :
    ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) a b (sign * T)‖ ≤
      (1 / (2 * Real.pi)) * (∫ u in a..b, q ^ u / T) := by
  have hgint : IntervalIntegrable (fun u : ℝ => q ^ u / T)
      MeasureTheory.volume a b :=
    ((Real.continuous_const_rpow hq.ne').div_const T).intervalIntegrable a b
  have hmajor := intervalIntegral.norm_integral_le_of_norm_le
    (μ := MeasureTheory.volume) (a := a) (b := b) (f := fun u : ℝ =>
      (q : ℂ) ^ ((u : ℂ) + (sign * T : ℝ) * Complex.I) /
        ((u : ℂ) + (sign * T : ℝ) * Complex.I)) hab
    (g := fun u : ℝ => q ^ u / T)
    (ae_of_all _ fun u _hu =>
      norm_perron_horizontal_integrand_le hq hT sign hsign)
    hgint
  have hscalar : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I))‖ =
      1 / (2 * Real.pi) := by
    simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I]
    ring
  rw [HIntegral', HIntegral]
  change ‖(1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      (∫ u in a..b,
        (q : ℂ) ^ ((u : ℂ) + (sign * T : ℝ) * Complex.I) /
          ((u : ℂ) + (sign * T : ℝ) * Complex.I))‖ ≤
    (1 / (2 * Real.pi)) * (∫ u in a..b, q ^ u / T)
  rw [norm_mul, hscalar]
  exact mul_le_mul_of_nonneg_left hmajor (by positivity)

/-- Upper horizontal edge bound for `q>1`, uniform in the remote left edge. -/
theorem norm_HIntegral'_perron_top_le_of_one_lt
    {q left c T : ℝ} (hq : 1 < q) (hleft : left ≤ c) (hT : 0 < T) :
    ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) left c T‖ ≤
      q ^ c / (2 * Real.pi * T * Real.log q) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hlog : 0 < Real.log q := Real.log_pos hq
  have h := norm_HIntegral'_perron_le hq0 hleft hT
    (sign := 1) (by norm_num)
  simp only [one_mul] at h
  rw [intervalIntegral.integral_div, intervalIntegral_const_rpow hq0 hq.ne'] at h
  calc
    ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) left c T‖
        ≤ (1 / (2 * Real.pi)) * (((q ^ c - q ^ left) / Real.log q) / T) := h
    _ ≤ q ^ c / (2 * Real.pi * T * Real.log q) := by
      have hpow : 0 ≤ q ^ left := Real.rpow_nonneg hq0.le left
      have hpi : 0 < Real.pi := Real.pi_pos
      have halg :
          (1 / (2 * Real.pi)) * (((q ^ c - q ^ left) / Real.log q) / T) =
            (q ^ c - q ^ left) / (2 * Real.pi * T * Real.log q) := by
        field_simp [ne_of_gt hpi, ne_of_gt hT, ne_of_gt hlog]
      rw [halg, div_le_div_iff_of_pos_right
        (by positivity : 0 < 2 * Real.pi * T * Real.log q)]
      exact sub_le_self _ hpow

/-- Lower horizontal edge bound for `q>1`; it has the same norm as the upper
bound because only the sign of the height changes. -/
theorem norm_HIntegral'_perron_bottom_le_of_one_lt
    {q left c T : ℝ} (hq : 1 < q) (hleft : left ≤ c) (hT : 0 < T) :
    ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) left c (-T)‖ ≤
      q ^ c / (2 * Real.pi * T * Real.log q) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hlog : 0 < Real.log q := Real.log_pos hq
  have h := norm_HIntegral'_perron_le hq0 hleft hT
    (sign := -1) (by norm_num)
  simp only [neg_one_mul] at h
  rw [intervalIntegral.integral_div, intervalIntegral_const_rpow hq0 hq.ne'] at h
  calc
    ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) left c (-T)‖
        ≤ (1 / (2 * Real.pi)) * (((q ^ c - q ^ left) / Real.log q) / T) := h
    _ ≤ q ^ c / (2 * Real.pi * T * Real.log q) := by
      have hpow : 0 ≤ q ^ left := Real.rpow_nonneg hq0.le left
      have hpi : 0 < Real.pi := Real.pi_pos
      have halg :
          (1 / (2 * Real.pi)) * (((q ^ c - q ^ left) / Real.log q) / T) =
            (q ^ c - q ^ left) / (2 * Real.pi * T * Real.log q) := by
        field_simp [ne_of_gt hpi, ne_of_gt hT, ne_of_gt hlog]
      rw [halg, div_le_div_iff_of_pos_right
        (by positivity : 0 < 2 * Real.pi * T * Real.log q)]
      exact sub_le_self _ hpow

/-- Upper horizontal edge bound for `0<q<1`, uniform in the remote right
edge. -/
theorem norm_HIntegral'_perron_top_le_of_lt_one
    {q c right T : ℝ} (hq0 : 0 < q) (hq : q < 1)
    (hcr : c ≤ right) (hT : 0 < T) :
    ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c right T‖ ≤
      q ^ c / (2 * Real.pi * T * (-Real.log q)) := by
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq
  have hneglog : 0 < -Real.log q := neg_pos.mpr hlog
  have h := norm_HIntegral'_perron_le hq0 hcr hT
    (sign := 1) (by norm_num)
  simp only [one_mul] at h
  rw [intervalIntegral.integral_div,
    intervalIntegral_const_rpow hq0 hq.ne] at h
  calc
    ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c right T‖
        ≤ (1 / (2 * Real.pi)) * (((q ^ right - q ^ c) / Real.log q) / T) := h
    _ = (q ^ c - q ^ right) / (2 * Real.pi * T * (-Real.log q)) := by
      field_simp [Real.pi_ne_zero, ne_of_gt hT, ne_of_lt hlog]
      ring
    _ ≤ q ^ c / (2 * Real.pi * T * (-Real.log q)) := by
      rw [div_le_div_iff_of_pos_right
        (mul_pos (mul_pos (mul_pos zero_lt_two Real.pi_pos) hT) hneglog)]
      exact sub_le_self _ (Real.rpow_nonneg hq0.le right)

/-- Lower horizontal edge bound for `0<q<1`. -/
theorem norm_HIntegral'_perron_bottom_le_of_lt_one
    {q c right T : ℝ} (hq0 : 0 < q) (hq : q < 1)
    (hcr : c ≤ right) (hT : 0 < T) :
    ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c right (-T)‖ ≤
      q ^ c / (2 * Real.pi * T * (-Real.log q)) := by
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq
  have hneglog : 0 < -Real.log q := neg_pos.mpr hlog
  have h := norm_HIntegral'_perron_le hq0 hcr hT
    (sign := -1) (by norm_num)
  simp only [neg_one_mul] at h
  rw [intervalIntegral.integral_div,
    intervalIntegral_const_rpow hq0 hq.ne] at h
  calc
    ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c right (-T)‖
        ≤ (1 / (2 * Real.pi)) * (((q ^ right - q ^ c) / Real.log q) / T) := h
    _ = (q ^ c - q ^ right) / (2 * Real.pi * T * (-Real.log q)) := by
      field_simp [Real.pi_ne_zero, ne_of_gt hT, ne_of_lt hlog]
      ring
    _ ≤ q ^ c / (2 * Real.pi * T * (-Real.log q)) := by
      rw [div_le_div_iff_of_pos_right
        (mul_pos (mul_pos (mul_pos zero_lt_two Real.pi_pos) hT) hneglog)]
      exact sub_le_self _ (Real.rpow_nonneg hq0.le right)

/-- Uniform norm bound for a normalized vertical edge away from the pole. -/
theorem norm_VIntegral'_perron_le
    {q r T : ℝ} (hq : 0 < q) (hr : r ≠ 0) :
    ‖VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) r (-T) T‖ ≤
      q ^ r * |T| / (Real.pi * |r|) := by
  have hrabs : 0 < |r| := abs_pos.mpr hr
  have hpoint : ∀ t : ℝ,
      ‖(q : ℂ) ^ ((r : ℂ) + (t : ℂ) * Complex.I) /
          ((r : ℂ) + (t : ℂ) * Complex.I)‖ ≤ q ^ r / |r| := by
    intro t
    have hqnorm :
        ‖(q : ℂ) ^ ((r : ℂ) + (t : ℂ) * Complex.I)‖ = q ^ r := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos hq
        ((r : ℂ) + (t : ℂ) * Complex.I)
    have hden : |r| ≤ ‖(r : ℂ) + (t : ℂ) * Complex.I‖ := by
      simpa using Complex.abs_re_le_norm
        ((r : ℂ) + (t : ℂ) * Complex.I)
    rw [norm_div, hqnorm]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hq.le r) hrabs hden
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T)
    (C := q ^ r / |r|)
    (f := fun t : ℝ =>
      (q : ℂ) ^ ((r : ℂ) + (t : ℂ) * Complex.I) /
        ((r : ℂ) + (t : ℂ) * Complex.I))
    (fun t _ht => hpoint t)
  have hscalar : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I))‖ =
      1 / (2 * Real.pi) := by
    simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I]
    ring
  rw [VIntegral', VIntegral]
  simp only [smul_eq_mul, norm_mul, Complex.norm_I, one_mul, hscalar]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ t in (-T)..T,
          (q : ℂ) ^ ((r : ℂ) + (t : ℂ) * Complex.I) /
            ((r : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (1 / (2 * Real.pi)) * ((q ^ r / |r|) * |T - (-T)|) := by
        gcongr
    _ = q ^ r * |T| / (Real.pi * |r|) := by
      rw [show T - -T = 2 * T by ring, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp [Real.pi_ne_zero, hrabs.ne']

/-- For `0<q<1`, the remote right vertical edge vanishes. -/
theorem tendsto_VIntegral'_perron_atTop_of_lt_one
    {q T : ℝ} (hq0 : 0 < q) (hq : q < 1) :
    Tendsto
      (fun r : ℝ =>
        VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) r (-T) T)
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hqpow : Tendsto (fun r : ℝ => q ^ r) Filter.atTop (nhds 0) :=
    tendsto_rpow_atTop_of_base_lt_one q (by linarith) hq
  have hupper : Tendsto (fun r : ℝ => q ^ r * (|T| / Real.pi))
      Filter.atTop (nhds 0) := by
    simpa using hqpow.mul_const (|T| / Real.pi)
  refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le hr)
  have hv := norm_VIntegral'_perron_le (q := q) (r := r) (T := T) hq0 hr0
  refine hv.trans ?_
  rw [abs_of_nonneg (zero_le_one.trans hr)]
  have hqr : 0 ≤ q ^ r := Real.rpow_nonneg hq0.le r
  have hTpi : 0 ≤ |T| / Real.pi := div_nonneg (abs_nonneg T) Real.pi_pos.le
  calc
    q ^ r * |T| / (Real.pi * r) = q ^ r * (|T| / Real.pi) / r := by ring
    _ ≤ q ^ r * (|T| / Real.pi) :=
      (div_le_self (mul_nonneg hqr hTpi) hr)

/-- Classical sharp Perron estimate below the discontinuity.  It is obtained
from the exact no-residue rectangle, the two horizontal logarithmic bounds,
and the proved vanishing of the remote vertical edge. -/
theorem norm_sharpPerronRatioKernel_le_of_lt_one
    {q c T : ℝ} (hq0 : 0 < q) (hq : q < 1) (hc : 0 < c) (hT : 0 < T) :
    ‖sharpPerronRatioKernel c T q‖ ≤
      q ^ c / (Real.pi * T * (-Real.log q)) := by
  let C : ℝ := q ^ c / (2 * Real.pi * T * (-Real.log q))
  have hvlim := (tendsto_VIntegral'_perron_atTop_of_lt_one
    (T := T) hq0 hq).norm
  have hlim : Tendsto
      (fun r : ℝ => C + C +
        ‖VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) r (-T) T‖)
      atTop (nhds (C + C)) := by
    simpa using (tendsto_const_nhds.add tendsto_const_nhds).add hvlim
  have hevent : ∀ᶠ r : ℝ in atTop,
      ‖sharpPerronRatioKernel c T q‖ ≤ C + C +
        ‖VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) r (-T) T‖ := by
    filter_upwards [eventually_gt_atTop c] with r hcr
    have hdecomp := sharpPerronRatioKernel_eq_edges_of_right_shift
      (q := q) (c := c) (right := r) (T := T) hq0 hc hcr
    have hbottom := norm_HIntegral'_perron_bottom_le_of_lt_one
      hq0 hq hcr.le hT
    have htop := norm_HIntegral'_perron_top_le_of_lt_one
      hq0 hq hcr.le hT
    change _ ≤ C + C + _
    rw [hdecomp]
    calc
      ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c r (-T) -
          HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c r T +
            VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) r (-T) T‖
        ≤ ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c r (-T) -
              HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c r T‖ +
            ‖VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) r (-T) T‖ :=
          norm_add_le _ _
      _ ≤ (‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c r (-T)‖ +
              ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c r T‖) +
            ‖VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) r (-T) T‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ C + C +
            ‖VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) r (-T) T‖ := by
          dsimp only [C]
          gcongr
  have hbound : ‖sharpPerronRatioKernel c T q‖ ≤ C + C :=
    ge_of_tendsto hlim hevent
  calc
    ‖sharpPerronRatioKernel c T q‖ ≤ C + C := hbound
    _ = q ^ c / (Real.pi * T * (-Real.log q)) := by
      dsimp only [C]
      field_simp [Real.pi_ne_zero, ne_of_gt hT,
        ne_of_gt (neg_pos.mpr (Real.log_neg hq0 hq))]
      ring

/-- For `q>1`, the remote left vertical edge vanishes when written as the
edge at real part `-R` and `R → +∞`. -/
theorem tendsto_VIntegral'_perron_neg_atTop_of_one_lt
    {q T : ℝ} (hq : 1 < q) :
    Tendsto
      (fun R : ℝ =>
        VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) (-T) T)
      atTop (nhds 0) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hqinv0 : 0 < q⁻¹ := inv_pos.mpr hq0
  have hqinv1 : q⁻¹ < 1 := (inv_lt_one₀ hq0).2 hq
  have hqpow : Tendsto (fun R : ℝ => q ^ (-R)) atTop (nhds 0) := by
    have hinv : Tendsto (fun R : ℝ => q⁻¹ ^ R) atTop (nhds 0) :=
      tendsto_rpow_atTop_of_base_lt_one q⁻¹ (by linarith) hqinv1
    convert hinv using 1
    ext R
    rw [Real.rpow_neg hq0.le, Real.inv_rpow hq0.le]
  have hupper : Tendsto (fun R : ℝ => q ^ (-R) * (|T| / Real.pi))
      atTop (nhds 0) := by
    simpa using hqpow.mul_const (|T| / Real.pi)
  refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hR0 : -R ≠ 0 := neg_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le hR))
  have hv := norm_VIntegral'_perron_le
    (q := q) (r := -R) (T := T) hq0 hR0
  refine hv.trans ?_
  rw [abs_neg, abs_of_nonneg (zero_le_one.trans hR)]
  have hqr : 0 ≤ q ^ (-R) := Real.rpow_nonneg hq0.le (-R)
  have hTpi : 0 ≤ |T| / Real.pi := div_nonneg (abs_nonneg T) Real.pi_pos.le
  calc
    q ^ (-R) * |T| / (Real.pi * R) = q ^ (-R) * (|T| / Real.pi) / R := by ring
    _ ≤ q ^ (-R) * (|T| / Real.pi) :=
      div_le_self (mul_nonneg hqr hTpi) hR

/-- Classical sharp Perron estimate above the discontinuity. -/
theorem norm_sharpPerronRatioKernel_sub_one_le_of_one_lt
    {q c T : ℝ} (hq : 1 < q) (hc : 0 < c) (hT : 0 < T) :
    ‖sharpPerronRatioKernel c T q - 1‖ ≤
      q ^ c / (Real.pi * T * Real.log q) := by
  let C : ℝ := q ^ c / (2 * Real.pi * T * Real.log q)
  have hvlim := (tendsto_VIntegral'_perron_neg_atTop_of_one_lt
    (T := T) hq).norm
  have hlim : Tendsto
      (fun R : ℝ => C + C +
        ‖VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) (-T) T‖)
      atTop (nhds (C + C)) := by
    simpa using (tendsto_const_nhds.add tendsto_const_nhds).add hvlim
  have hevent : ∀ᶠ R : ℝ in atTop,
      ‖sharpPerronRatioKernel c T q - 1‖ ≤ C + C +
        ‖VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) (-T) T‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hdecomp := sharpPerronRatioKernel_eq_residue_add_edges
      (q := q) (left := -R) (c := c) (T := T) (zero_lt_one.trans hq)
      (neg_lt_zero.mpr hR) hc hT
    have hleftc : -R ≤ c := by linarith
    have hbottom := norm_HIntegral'_perron_bottom_le_of_one_lt
      hq hleftc hT
    have htop := norm_HIntegral'_perron_top_le_of_one_lt
      hq hleftc hT
    change _ ≤ C + C + _
    rw [hdecomp]
    calc
      ‖1 - HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c (-T) +
          HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c T +
            VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) (-T) T - 1‖
        = ‖-HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c (-T) +
          HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c T +
            VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) (-T) T‖ := by
              congr 1
              ring
      _ ≤ ‖-HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c (-T) +
              HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c T‖ +
            ‖VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) (-T) T‖ :=
          norm_add_le _ _
      _ ≤ (‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c (-T)‖ +
              ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c T‖) +
            ‖VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) (-T) T‖ := by
          have hh := norm_add_le
            (-HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c (-T))
            (HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c T)
          have hh' :
              ‖-HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c (-T) +
                  HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c T‖ ≤
                ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c (-T)‖ +
                  ‖HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) c T‖ := by
            simpa only [norm_neg] using hh
          exact add_le_add hh' (le_refl _)
      _ ≤ C + C +
            ‖VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) (-R) (-T) T‖ := by
          dsimp only [C]
          gcongr
  have hbound : ‖sharpPerronRatioKernel c T q - 1‖ ≤ C + C :=
    ge_of_tendsto hlim hevent
  calc
    ‖sharpPerronRatioKernel c T q - 1‖ ≤ C + C := hbound
    _ = q ^ c / (Real.pi * T * Real.log q) := by
      dsimp only [C]
      field_simp [Real.pi_ne_zero, ne_of_gt hT, ne_of_gt (Real.log_pos hq)]
      ring

end GafniTao
