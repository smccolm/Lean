import Dubon2026.TrigammaIntegral

/-! # A uniform inverse-height-squared error for the genuine trigamma function -/

namespace Dubon2026

open Complex Filter Finset RiemannZeta.GuthMaynard
open scoped Topology

noncomputable section

/-- A telescoping majorant for the actual unit-interval trigamma errors. -/
theorem sum_trigamma_error_majorant_le {y : ℝ} (hy : 1 ≤ y) (N : ℕ) :
    (∑ n ∈ range N, 16 / ((n : ℝ) + y) ^ 3) ≤ 32 / y ^ 2 := by
  have hstep (n : ℕ) : 16 / ((n : ℝ) + y) ^ 3 ≤
      32 * ((((n : ℝ) + y)⁻¹) ^ 2 - (((n : ℝ) + y + 1)⁻¹) ^ 2) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp : 0 < (n : ℝ) + y := by linarith
    have hp1 : 0 < (n : ℝ) + y + 1 := by linarith
    field_simp
    nlinarith [sq_nonneg ((n : ℝ) + y - 1)]
  calc
    _ ≤ ∑ n ∈ range N, 32 * ((((n : ℝ) + y)⁻¹) ^ 2 - (((n : ℝ) + y + 1)⁻¹) ^ 2) :=
      sum_le_sum (fun n _ => hstep n)
    _ = 32 * (y⁻¹ ^ 2 - ((N : ℝ) + y)⁻¹ ^ 2) := by
      rw [← mul_sum]
      congr 1
      induction N with
      | zero => simp
      | succ N ih => rw [sum_range_succ, ih]; push_cast; ring
    _ ≤ 32 / y ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow]
      nlinarith [sq_nonneg (((N : ℝ) + y)⁻¹)]

/-- The literal finite trigamma sum differs from its exact integral by at most 32/|Im z|². -/
theorem norm_sum_trigamma_sub_integral_le {z : ℂ} (hz : 0 < z.re)
    (hy : 1 ≤ |z.im|) (N : ℕ) :
    ‖(∑ n ∈ range N, (z + n)⁻¹ ^ 2) - (z⁻¹ - (z + N)⁻¹)‖ ≤ 32 / |z.im| ^ 2 := by
  have he : (∑ n ∈ range N, (z + n)⁻¹ ^ 2) - (z⁻¹ - (z + N)⁻¹) =
      ∑ n ∈ range N, ((z + n)⁻¹ ^ 2 - ((z + n)⁻¹ - (z + (n + 1 : ℕ))⁻¹)) := by
    induction N with
    | zero => simp
    | succ N ih => simp only [sum_range_succ]; rw [← ih]; ring
  rw [he]
  exact (norm_sum_le _ _).trans ((sum_le_sum (fun n _ =>
    norm_trigamma_integral_step_le hz (lt_of_lt_of_le zero_lt_one hy) n)).trans
      (sum_trigamma_error_majorant_le hy N))

/-- The genuine reciprocal of a shifted natural argument tends to zero in the complex plane. -/
theorem tendsto_inv_nat_shift (z : ℂ) :
    Tendsto (fun N : ℕ => (z + N)⁻¹) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (N : ℂ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have hd : Tendsto (fun N : ℕ => 1 + z * (N : ℂ)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hi.const_mul z)
  have hh := hi.div hd (one_ne_zero : (1 : ℂ) ≠ 0)
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he : z + N = (N : ℂ) * (1 + z * (N : ℂ)⁻¹) := by field_simp; ring
  rw [he, mul_inv, div_eq_mul_inv]
  rfl

/-- The actual absolutely convergent quadratic polygamma series has its reciprocal leading term with uniform second-order error. -/
theorem norm_trigamma_series_sub_inv_le {z : ℂ} (hz : 0 < z.re) (hy : 1 ≤ |z.im|) :
    ‖hughesYoungPolygammaSeries 1 z - z⁻¹‖ ≤ 32 / |z.im| ^ 2 := by
  have hs : Tendsto (fun N : ℕ => ∑ n ∈ range N, (z + n)⁻¹ ^ 2)
      atTop (𝓝 (hughesYoungPolygammaSeries 1 z)) := by
    simpa only [hughesYoungPolygammaSeries, Nat.reduceAdd, add_comm] using
      (summable_norm_hughesYoungPolygammaTerm hz (j := 1) (by omega)).of_norm.hasSum.tendsto_sum_nat
  have hh := hs.sub ((tendsto_const_nhds (x := z⁻¹)).sub (tendsto_inv_nat_shift z))
  simp only [sub_zero] at hh
  exact le_of_tendsto hh.norm (Eventually.of_forall (fun N => norm_sum_trigamma_sub_integral_le hz hy N))

/-- The derivative of the genuine digamma function has the explicit reciprocal asymptotic required for phase curvature. -/
theorem norm_deriv_digamma_sub_inv_le {z : ℂ} (hz : 0 < z.re) (hy : 1 ≤ |z.im|) :
    ‖deriv digamma z - z⁻¹‖ ≤ 32 / |z.im| ^ 2 := by
  rw [(hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one hz).deriv]
  exact norm_trigamma_series_sub_inv_le hz hy

end
end Dubon2026
