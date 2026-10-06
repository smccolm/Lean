import Dubon2026.CirclePolynomialLog
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # The actual circle characteristic integral underlying the source's Bessel function

This module starts with the circle law itself. Its identification with the source's
power-series definition of J0 is a separate obligation.
-/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology ComplexConjugate

noncomputable section

/-- The character in the real coordinate direction for a uniform unit-circle point. -/
def circleExponential (u : ℝ) : C(UnitAddCircle, ℂ) where
  toFun z := Complex.exp (Complex.I * ((u * (fourier 1 z).re : ℝ) : ℂ))
  continuous_toFun := by fun_prop

/-- The normalized Haar characteristic function, before the series identification. -/
def circleCharacteristic (u : ℝ) : ℂ :=
  ∫ z : UnitAddCircle, circleExponential u z ∂AddCircle.haarAddCircle

theorem norm_circleExponential (u : ℝ) (z : UnitAddCircle) :
    ‖circleExponential u z‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

theorem circleExponential_coe (u t : ℝ) :
    circleExponential u (t : UnitAddCircle) =
      Complex.exp (Complex.I * ((u * Real.cos (2 * Real.pi * t) : ℝ) : ℂ)) := by
  simp only [circleExponential, ContinuousMap.coe_mk, fourier_one_eq_circleMap,
    circleMap_zero_re, one_mul]

theorem integrable_circleExponential (u : ℝ) :
    Integrable (circleExponential u) AddCircle.haarAddCircle :=
  (circleExponential u).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem circleCharacteristic_zero : circleCharacteristic 0 = 1 := by
  simp [circleCharacteristic, circleExponential]

theorem norm_circleCharacteristic_le_one (u : ℝ) : ‖circleCharacteristic u‖ ≤ 1 := by
  simpa only [circleCharacteristic, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
      (Filter.Eventually.of_forall (fun z => (norm_circleExponential u z).le)))

theorem continuous_circleCharacteristic : Continuous circleCharacteristic := by
  rw [continuous_iff_continuousAt]
  intro u
  apply tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall (fun v => (integrable_circleExponential v).aestronglyMeasurable)
  · exact ⟨1, Filter.Eventually.of_forall (fun v =>
      Filter.Eventually.of_forall (fun z => (norm_circleExponential v z).le))⟩
  · apply Filter.Eventually.of_forall
    intro z
    change Tendsto (fun v : ℝ => Complex.exp (Complex.I * ((v * (fourier 1 z).re : ℝ) : ℂ)))
      (𝓝 u) (𝓝 _)
    exact (by fun_prop : Continuous (fun v : ℝ =>
      Complex.exp (Complex.I * ((v * (fourier 1 z).re : ℝ) : ℂ)))).continuousAt.tendsto

theorem circleCharacteristic_eq_interval (u : ℝ) :
    circleCharacteristic u = (2 * Real.pi)⁻¹ • ∫ θ in 0..2 * Real.pi,
      Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ)) := by
  rw [circleCharacteristic, ← unitCircle_volume_eq_haar,
    ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0, zero_add]
  simp_rw [circleExponential_coe]
  rw [intervalIntegral.integral_comp_mul_left
    (fun θ : ℝ => Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ)))
    (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
  simp only [mul_zero, mul_one]

theorem circleExponential_half_shift (u : ℝ) (z : UnitAddCircle) :
    circleExponential u (z + ((1 / 2 : ℝ) : UnitAddCircle)) = conj (circleExponential u z) := by
  have hf : fourier 1 (z + ((1 / 2 : ℝ) : UnitAddCircle)) = -fourier 1 z := by
    simpa only [Int.cast_one, div_one] using
      fourier_add_half_inv_index (T := (1 : ℝ)) (n := 1) (by norm_num) (by norm_num) z
  simp only [circleExponential, ContinuousMap.coe_mk, hf, Complex.neg_re,
    ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

theorem circleCharacteristic_conj (u : ℝ) : conj (circleCharacteristic u) = circleCharacteristic u := by
  rw [circleCharacteristic, ← integral_conj]
  simp_rw [← circleExponential_half_shift]
  exact integral_add_right_eq_self (fun z => circleExponential u z) ((1 / 2 : ℝ) : UnitAddCircle)

theorem circleCharacteristic_im (u : ℝ) : (circleCharacteristic u).im = 0 := by
  have hh := congrArg Complex.im (circleCharacteristic_conj u)
  simp only [Complex.conj_im] at hh
  linarith

theorem circleExponential_angle (u θ : ℝ) :
    circleExponential u ((θ / (2 * Real.pi) : ℝ) : UnitAddCircle) =
      Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ)) := by
  rw [circleExponential_coe,
    show 2 * Real.pi * (θ / (2 * Real.pi)) = θ by field_simp]

theorem circleExponential_not_constant {u : ℝ} (hu : u ≠ 0) :
    ¬∃ c : ℂ, ∀ z : UnitAddCircle, circleExponential u z = c := by
  rintro ⟨c, hc⟩
  have he : (fun θ : ℝ => Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ))) =
      (fun _ : ℝ => c) := by
    funext θ
    rw [← circleExponential_angle]
    exact hc _
  have hd : HasDerivAt
      (fun θ : ℝ => Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ)))
      (-Complex.I * (u : ℂ)) (Real.pi / 2) := by
    simpa using ((((Real.hasDerivAt_cos (Real.pi / 2)).const_mul u).ofReal_comp.const_mul Complex.I).cexp)
  have hz : -Complex.I * (u : ℂ) = 0 := by
    rw [← hd.deriv, he, deriv_const]
  exact (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hu)) hz

theorem norm_circleCharacteristic_lt_one {u : ℝ} (hu : u ≠ 0) :
    ‖circleCharacteristic u‖ < 1 := by
  have hh := ae_eq_const_or_norm_integral_lt_of_norm_le_const
    (μ := AddCircle.haarAddCircle)
    (Filter.Eventually.of_forall (fun z => (norm_circleExponential u z).le))
  rcases hh with he | hl
  · have he' := MeasureTheory.Measure.eq_of_ae_eq he (circleExponential u).continuous continuous_const
    exact (circleExponential_not_constant hu
      ⟨_, fun z => congrFun he' z⟩).elim
  · simpa only [circleCharacteristic, probReal_univ, mul_one] using hl

end

end Dubon2026
