import RiemannZeta.GuthMaynard.DFIY0Abel

open Complex Set MeasureTheory Filter
open scoped Topology Interval

namespace RiemannZeta.GuthMaynard

theorem probe_tendsto_cpow_I_sub
    (s : ℂ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => ((ε : ℂ) - I * a) ^ (-s)) (𝓝[>] 0)
      (𝓝 ((-I * a) ^ (-s))) := by
  have hslit : -I * (a : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simp [ha.ne']
  have hbase : Tendsto (fun ε : ℝ => (ε : ℂ) - I * a) (𝓝 0)
      (𝓝 (-I * a)) := by
    simpa using ((Complex.continuous_ofReal.sub continuous_const).tendsto 0)
  exact ((continuousAt_cpow_const hslit).tendsto.comp hbase).mono_left inf_le_left

theorem probe_tendsto_cpow_I_add
    (s : ℂ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => ((ε : ℂ) + I * a) ^ (-s)) (𝓝[>] 0)
      (𝓝 ((I * a) ^ (-s))) := by
  have hslit : I * (a : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simp [ha.ne']
  have hbase : Tendsto (fun ε : ℝ => (ε : ℂ) + I * a) (𝓝 0)
      (𝓝 (I * a)) := by
    simpa using ((Complex.continuous_ofReal.add continuous_const).tendsto 0)
  exact ((continuousAt_cpow_const hslit).tendsto.comp hbase).mono_left inf_le_left

theorem probe_tendsto_damped_sin_factor
    (s : ℂ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ =>
        (((ε : ℂ) - I * a) ^ (-s) - ((ε : ℂ) + I * a) ^ (-s)) / (2 * I))
      (𝓝[>] 0)
      (𝓝 (((-I * a) ^ (-s) - (I * a) ^ (-s)) / (2 * I))) := by
  exact ((probe_tendsto_cpow_I_sub s ha).sub
    (probe_tendsto_cpow_I_add s ha)).div_const (2 * I)

theorem probe_abel_sin_limit_eq
    (s : ℂ) {a : ℝ} (ha : 0 < a) :
    (((-I * a) ^ (-s) - (I * a) ^ (-s)) / (2 * I)) =
      (a : ℂ) ^ (-s) * Complex.sin (Real.pi * s / 2) := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hnegI : (-I : ℂ) ≠ 0 := by simp
  have hI : (I : ℂ) ≠ 0 := by simp
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hnegI haC),
    Complex.cpow_def_of_ne_zero (mul_ne_zero hI haC),
    Complex.cpow_def_of_ne_zero haC,
    Complex.log_mul_ofReal a ha (-I) hnegI,
    Complex.log_mul_ofReal a ha I hI,
    Complex.log_neg_I, Complex.log_I]
  rw [show (Real.log a + -(Real.pi / 2) * I) * -s =
      Real.log a * -s + I * (Real.pi * s / 2) by ring,
    show (Real.log a + Real.pi / 2 * I) * -s =
      Real.log a * -s + -(I * (Real.pi * s / 2)) by ring,
    Complex.exp_add, Complex.exp_add]
  simp only [Complex.sin]
  rw [Complex.ofReal_log ha.le]
  have hp : cexp (I * (Real.pi * s / 2)) =
      cexp (Real.pi * s / 2 * I) := by congr 1 <;> ring
  have hm : cexp (-(I * (Real.pi * s / 2))) =
      cexp (-(Real.pi * s / 2) * I) := by congr 1 <;> ring
  rw [hp, hm]
  field_simp
  have hIsq : I ^ 2 = (-1 : ℂ) := by rw [pow_two, Complex.I_mul_I]
  rw [hIsq]
  ring

end RiemannZeta.GuthMaynard
