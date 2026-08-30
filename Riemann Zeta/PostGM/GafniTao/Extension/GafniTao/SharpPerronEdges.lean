import GafniTao.SharpPerronContour

/-!
# Quantitative edge estimates for sharp Perron rectangles

The horizontal estimates keep the exact `q^s/s` integrand.  Their real
majorant is integrated exactly, so the logarithmic distance from the Perron
discontinuity remains visible.
-/

open Complex Set MeasureTheory
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
    convert ((hasDerivAt_id u).const_rpow hq).div_const (Real.log q) using 1 <;>
      simp only [id_eq] <;> field_simp [hlog]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _hu => hderiv u) (Real.continuous_const_rpow hq.ne').intervalIntegrable]
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
  have hmajor := intervalIntegral.norm_integral_le_of_norm_le
    (a := a) (b := b) (f := fun u : ℝ =>
      (q : ℂ) ^ ((u : ℂ) + (sign * T : ℝ) * Complex.I) /
        ((u : ℂ) + (sign * T : ℝ) * Complex.I)) hab
    (g := fun u : ℝ => q ^ u / T)
    (ae_of_all _ fun u _hu =>
      norm_perron_horizontal_integrand_le hq hT sign hsign)
    ((Real.continuous_const_rpow hq.ne').div_const T).intervalIntegrable
  have hscalar : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I))‖ =
      1 / (2 * Real.pi) := by
    simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I]
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

end GafniTao
