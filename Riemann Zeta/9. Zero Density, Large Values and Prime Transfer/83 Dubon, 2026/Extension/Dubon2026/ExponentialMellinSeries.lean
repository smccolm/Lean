import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.LSeries.Basic

/-! # Exact Mellin transform for an absolutely convergent exponential coefficient series -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- Absolute convergence of a genuine L-series supplies the scaled Mellin norm majorant. -/
theorem summable_scaled_mellin_coefficients {a : ℕ → ℂ} (ha : a 0 = 0)
    {s : ℂ} (hs : LSeriesSummable a s) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => ‖a n‖ / (c * n) ^ s.re) := by
  apply (hs.norm.mul_left (c ^ (-s.re))).congr
  intro n
  by_cases hn : n = 0
  · simp [hn, ha]
  · rw [LSeries.norm_term_eq, if_neg hn, Real.mul_rpow hc.le (Nat.cast_nonneg n),
      Real.rpow_neg hc.le]
    ring

/-- A literal exponential Fourier series has its exact Gamma-scaled L-series Mellin transform. -/
theorem mellin_exponential_series {a : ℕ → ℂ} (ha : a 0 = 0)
    {s : ℂ} (hs : 0 < s.re) (hsum : LSeriesSummable a s) {c : ℝ} (hc : 0 < c)
    {F : ℝ → ℂ}
    (hF : ∀ y ∈ Ioi 0, HasSum (fun n : ℕ => a n * (Real.exp (-(c * n) * y) : ℂ)) (F y)) :
    mellin F s = (c : ℂ) ^ (-s) * Gamma s * LSeries a s := by
  have hp (n : ℕ) : a n = 0 ∨ 0 < c * n := by
    by_cases hn : n = 0
    · exact Or.inl (hn ▸ ha)
    · exact Or.inr (mul_pos hc (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
  have hi := hasSum_mellin hp hs hF (summable_scaled_mellin_coefficients ha hsum hc)
  have he (n : ℕ) : Gamma s * a n / ((c * n : ℝ) : ℂ) ^ s =
      ((c : ℂ) ^ (-s) * Gamma s) * LSeries.term a s n := by
    by_cases hn : n = 0
    · simp [hn, ha]
    · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hc.le (Nat.cast_nonneg n), Complex.cpow_neg]
      push_cast
      ring
  simp_rw [he] at hi
  exact hi.unique (hsum.hasSum.mul_left _)

/-- Absolute summability of the true integral norms gives Bochner integrability of the complex series itself. -/
theorem integrable_complex_tsum_of_integral_norm {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {μ : Measure α} {F : ι → α → ℂ} (hi : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ)) : Integrable (fun x => ∑' i, F i x) μ := by
  constructor
  · exact (AEMeasurable.tsum (fun i => (hi i).aemeasurable)).aestronglyMeasurable
  · have he (i : ι) : (∫⁻ x, ‖F i x‖ₑ ∂μ) = ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hi i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (F i x)))]
      simp only [coe_nnnorm]
    have ht : (∑' i, ∫⁻ x, ‖F i x‖ₑ ∂μ) < ⊤ := by
      rw [funext he, lt_top_iff_ne_top]
      exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
    apply lt_of_le_of_lt _ ht
    calc
      (∫⁻ x, ‖∑' i, F i x‖ₑ ∂μ) ≤ ∫⁻ x, ∑' i, ‖F i x‖ₑ ∂μ :=
        lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
      _ = _ := lintegral_tsum (fun i => (hi i).1.enorm)

/-- The scaled exponential Mellin identity uses a genuinely absolutely convergent integral. -/
theorem integrableOn_exponential_series_mellin {a : ℕ → ℂ} (ha : a 0 = 0)
    {s : ℂ} (hs : 0 < s.re) (hsum : LSeriesSummable a s) {c : ℝ} (hc : 0 < c)
    {F : ℝ → ℂ}
    (hF : ∀ y ∈ Ioi 0, HasSum (fun n : ℕ => a n * (Real.exp (-(c * n) * y) : ℂ)) (F y)) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1) * F y) (Ioi 0) := by
  let p (n : ℕ) : ℝ := c * n
  have hp (n : ℕ) : a n = 0 ∨ 0 < p n := by
    by_cases hn : n = 0
    · exact Or.inl (hn ▸ ha)
    · exact Or.inr (mul_pos hc (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
  let T (n : ℕ) (y : ℝ) : ℂ := (y : ℂ) ^ (s - 1) * (a n * (Real.exp (-p n * y) : ℂ))
  have hi (n : ℕ) : IntegrableOn (T n) (Ioi 0) := by
    rcases hp n with hn | hn
    · simp [T, hn]
    · have ht := Complex.GammaIntegral_convergent hs
      rw [← mul_zero (p n), ← integrableOn_Ioi_comp_mul_left_iff _ _ hn] at ht
      have hh := IntegrableOn.congr_fun (ht.const_mul (1 / (p n : ℂ) ^ (s - 1)))
        (g := fun y : ℝ => (y : ℂ) ^ (s - 1) * (Real.exp (-p n * y) : ℂ)) (fun y hy => by
          simp_rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
          rw [Complex.mul_cpow_ofReal_nonneg hn.le hy.le]
          have hz : (p n : ℂ) ^ (s - 1) ≠ 0 :=
            Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hn.ne'))
          push_cast
          field_simp [hz]) measurableSet_Ioi
      apply (hh.const_mul (a n)).congr
      filter_upwards with y
      dsimp [T]
      ring
  have hn (n : ℕ) : (∫ y : ℝ in Ioi 0, ‖T n y‖) =
      Real.Gamma s.re * (‖a n‖ / (p n) ^ s.re) := by
    rcases hp n with ha | hp
    · simp [T, ha]
    · have ht := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hp
      calc
        _ = ‖a n‖ * ∫ y : ℝ in Ioi 0, y ^ (s.re - 1) * Real.exp (-(p n * y)) := by
          rw [← integral_const_mul]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y hy
          simp only [T, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
            Complex.sub_re, Complex.one_re, Complex.norm_of_nonneg (Real.exp_pos _).le]
          rw [neg_mul (p n) y]
          ring
        _ = _ := by
          rw [ht, one_div, Real.inv_rpow hp.le, ← Real.rpow_neg hp.le, Real.rpow_neg hp.le]
          ring
  have hiS := integrable_complex_tsum_of_integral_norm hi
    (by simp_rw [hn]; exact (summable_scaled_mellin_coefficients ha hsum hc).mul_left _)
  apply hiS.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact ((hF y hy).mul_left ((y : ℂ) ^ (s - 1))).tsum_eq

end
end Dubon2026
