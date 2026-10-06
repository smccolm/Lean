import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Order.Field

/-! # Symmetric means of integrable periodic functions, including logarithmic singularities -/

namespace Dubon2026

open Filter MeasureTheory Set
open scoped Topology

theorem periodic_centered_primitive {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P)
    (hf : Function.Periodic f P) (hi : IntervalIntegrable f volume 0 P) :
    Function.Periodic (fun t => (∫ x in 0..t, f x) - t * ((∫ x in 0..P, f x) / P)) P := by
  intro t
  dsimp only
  rw [hf.intervalIntegral_add_eq_add 0 t (hf.intervalIntegrable₀ hP.ne' hi), zero_add]
  field_simp
  ring

theorem exists_periodic_integral_error_bound {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P)
    (hf : Function.Periodic f P) (hi : IntervalIntegrable f volume 0 P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ,
      |(∫ x in -T..T, f x) - (2 * T) * ((∫ x in 0..P, f x) / P)| ≤ C := by
  let A := (∫ x in 0..P, f x) / P
  let G := fun t => (∫ x in 0..t, f x) - t * A
  have hall := hf.intervalIntegrable₀ hP.ne' hi
  have hc : Continuous G := (intervalIntegral.continuous_primitive hall 0).sub
    (continuous_id.mul_const A)
  have hp : Function.Periodic G P := periodic_centered_primitive hP hf hi
  obtain ⟨C, hC⟩ := (hp.isBounded_of_continuous hP.ne' hc).exists_norm_le
  have hb (t : ℝ) : |G t| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (G t) (mem_range_self t)
  have hC0 : 0 ≤ C := (abs_nonneg (G 0)).trans (hb 0)
  refine ⟨2 * C, mul_nonneg (by norm_num) hC0, ?_⟩
  intro T
  have he : (∫ x in -T..T, f x) - (2 * T) * A = G T - G (-T) := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hall 0 (-T)) (hall (-T) T)
    dsimp [G]
    linarith
  change |(∫ x in -T..T, f x) - (2 * T) * A| ≤ 2 * C
  rw [he]
  exact (abs_sub (G T) (G (-T))).trans (by linarith [hb T, hb (-T)])

theorem tendsto_periodic_symmetric_mean {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P)
    (hf : Function.Periodic f P) (hi : IntervalIntegrable f volume 0 P) :
    Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ x in -T..T, f x) atTop
      (𝓝 ((∫ x in 0..P, f x) / P)) := by
  let A := (∫ x in 0..P, f x) / P
  obtain ⟨C, _hC, hb⟩ := exists_periodic_integral_error_bound hP hf hi
  have hz : Tendsto (fun T : ℝ => (2 * T)⁻¹ * (∫ x in -T..T, f x) - A)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_
      ((tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)).const_div_atTop C)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T ht
    have hpos : 0 < 2 * T := by linarith
    have he : (2 * T)⁻¹ * (∫ x in -T..T, f x) - A =
        ((∫ x in -T..T, f x) - (2 * T) * A) / (2 * T) := by
      field_simp
    rw [he, Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (hb T) hpos.le
  have ha := hz.add_const A
  simpa only [sub_add_cancel, zero_add, A] using ha

theorem real_symmetric_mean_comp_pos (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (T : ℝ) :
    (2 * T)⁻¹ * (∫ t in -T..T, f (c * t)) =
      (2 * (c * T))⁻¹ * (∫ t in -(c * T)..c * T, f t) := by
  rw [intervalIntegral.integral_comp_mul_left f hc.ne']
  simp only [mul_neg, smul_eq_mul, mul_inv_rev]
  ring

theorem real_symmetric_mean_comp_neg (f : ℝ → ℝ) (T : ℝ) :
    (2 * T)⁻¹ * (∫ t in -T..T, f (-t)) = (2 * T)⁻¹ * (∫ t in -T..T, f t) := by
  rw [intervalIntegral.integral_comp_neg]
  simp only [neg_neg]

theorem tendsto_real_symmetric_mean_comp_negative {f : ℝ → ℝ} {c L : ℝ} (hc : 0 < c)
    (hf : Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ t in -T..T, f t) atTop (𝓝 L)) :
    Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ t in -T..T, f (-c * t)) atTop (𝓝 L) := by
  have he (T : ℝ) : (2 * T)⁻¹ * (∫ t in -T..T, f (-c * t)) =
      (2 * (c * T))⁻¹ * (∫ t in -(c * T)..c * T, f t) := by
    simp_rw [neg_mul, ← mul_neg c]
    rw [real_symmetric_mean_comp_neg (fun t => f (c * t)), real_symmetric_mean_comp_pos f hc]
    rw [mul_neg]
  simp_rw [he]
  exact hf.comp (tendsto_id.const_mul_atTop hc)

end Dubon2026
