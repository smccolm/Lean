import Dubon2026.GaussianDensityLimit

/-! # Gaussian approximate identity against actual integrable test functions -/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section

theorem planarGaussian_sub_comm (c : ℝ) (x y : ℂ) :
    planarGaussian c (x - y) = planarGaussian c (y - x) := by
  unfold planarGaussian
  rw [norm_sub_rev]

theorem integrable_planarGaussian_sub {c : ℝ} (hc : 0 < c) (y : ℂ) :
    Integrable (fun x : ℂ => planarGaussian c (x - y)) :=
  (integrable_planarGaussian hc).comp_sub_right y

theorem integral_planarGaussian_sub {c : ℝ} (hc : 0 < c) (y : ℂ) :
    ∫ x : ℂ, planarGaussian c (x - y) = 1 := by
  rw [integral_sub_right_eq_self, integral_planarGaussian hc]

theorem tendsto_planarGaussian_test_complex {f : ℂ → ℂ} (hf : Integrable f)
    {y : ℂ} (hy : ContinuousAt f y) :
    Tendsto (fun c : ℝ => ∫ x : ℂ, (planarGaussian c (y - x) : ℂ) * f x)
      atTop (𝓝 (f y)) := by
  have ht := (Real.tendsto_integral_gaussian_smul' hf hy).comp
    (Tendsto.atTop_div_const (sq_pos_of_pos Real.pi_pos) tendsto_id)
  convert ht using 1
  ext c
  congr 1
  ext x
  simp only [id_eq, Complex.finrank_real_complex, Nat.cast_ofNat,
    div_self (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one, smul_eq_mul]
  unfold planarGaussian
  push_cast
  congr 1
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  congr 1
  · field_simp
  · congr 1
    field_simp

theorem tendsto_planarGaussian_test {f : ℂ → ℝ} (hf : Integrable f)
    {y : ℂ} (hy : ContinuousAt f y) :
    Tendsto (fun c : ℝ => ∫ x : ℂ, planarGaussian c (y - x) * f x)
      atTop (𝓝 (f y)) := by
  have ht := tendsto_planarGaussian_test_complex hf.ofReal (Complex.continuous_ofReal.continuousAt.comp hy)
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  change Tendsto (fun c : ℝ => (∫ x : ℂ,
    (planarGaussian c (y - x) : ℂ) * (f x : ℂ)).re) atTop (𝓝 (f y)) at hr
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_re] using hr

theorem norm_integral_planarGaussian_test_le {c B : ℝ} (hc : 0 < c)
    (f : ℂ → ℝ) (hf : ∀ x, |f x| ≤ B) (y : ℂ) :
    |∫ x : ℂ, planarGaussian c (x - y) * f x| ≤ B := by
  calc
    |∫ x : ℂ, planarGaussian c (x - y) * f x| ≤
        ∫ x : ℂ, ‖planarGaussian c (x - y) * f x‖ := by
          simpa only [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (fun x : ℂ => planarGaussian c (x - y) * f x)
    _ ≤ ∫ x : ℂ, planarGaussian c (x - y) * B := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun _ => norm_nonneg _)
      · exact (integrable_planarGaussian_sub hc y).mul_const B
      · filter_upwards with x
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (planarGaussian_nonneg hc.le _), Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hf x) (planarGaussian_nonneg hc.le _)
    _ = B := by rw [integral_mul_const, integral_planarGaussian_sub hc, one_mul]

end

end Dubon2026
