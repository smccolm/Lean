import Dubon2026.BesselJ0
import Dubon2026.CircleOscillation

/-! # An absolute inverse-square-root bound for the source's J0 function -/

namespace Dubon2026

open MeasureTheory

theorem norm_cosine_phase_quarter_split {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ)
    (hδb : δ < Real.pi / 2) :
    ‖∫ θ in 0..Real.pi / 2, Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ))‖ ≤
      δ + 2 / (u * Real.sin δ) := by
  let f : ℝ → ℂ := fun θ => Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ))
  have hf : Continuous f := by fun_prop
  have hb : ‖∫ θ in 0..δ, f θ‖ ≤ δ := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ)
      (f := f) (C := 1) (fun θ _ => (Complex.norm_exp_I_mul_ofReal _).le)
    simpa only [sub_zero, abs_of_pos hδ, one_mul] using hh
  have ht := norm_cosine_phase_tail hu hδ hδb
  change ‖∫ θ in 0..Real.pi / 2, f θ‖ ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 δ) (hf.intervalIntegrable δ (Real.pi / 2))]
  exact (norm_add_le _ _).trans (add_le_add hb ht)

theorem norm_circleCharacteristic_le_inv_sqrt {u : ℝ} (hu : 1 ≤ u) :
    ‖circleCharacteristic u‖ ≤ (4 + 1 / Real.pi) / Real.sqrt u := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hs0 : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hs1 : 1 ≤ Real.sqrt u := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hu
  let δ : ℝ := 1 / (2 * Real.sqrt u)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 / 2 := by
    dsimp [δ]
    apply div_le_div_of_nonneg_left zero_le_one (by norm_num)
    linarith
  have hδb : δ < Real.pi / 2 := by linarith [Real.two_le_pi]
  have hsin : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hslow : 2 / Real.pi * δ ≤ Real.sin δ := Real.mul_le_sin hδ.le hδb.le
  have ht : 2 / (u * Real.sin δ) ≤ Real.pi / (u * δ) := by
    calc
      _ ≤ 2 / (u * ((2 / Real.pi) * δ)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left hslow hu0.le)
      _ = _ := by field_simp
  calc
    ‖circleCharacteristic u‖ ≤ (2 / Real.pi) *
      ‖∫ θ in 0..Real.pi / 2, Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ))‖ :=
        norm_circleCharacteristic_le_quarter u
    _ ≤ (2 / Real.pi) * (δ + 2 / (u * Real.sin δ)) :=
      mul_le_mul_of_nonneg_left (norm_cosine_phase_quarter_split hu0 hδ hδb) (by positivity)
    _ ≤ (2 / Real.pi) * (δ + Real.pi / (u * δ)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl ht) (by positivity)
    _ = (4 + 1 / Real.pi) / Real.sqrt u := by
      dsimp [δ]
      field_simp
      nlinarith [Real.sq_sqrt hu0.le]

theorem abs_besselJ0_le_inv_sqrt {u : ℝ} (hu : 1 ≤ u) :
    |besselJ0 u| ≤ (4 + 1 / Real.pi) / Real.sqrt u := by
  rw [besselJ0_eq_re_circleCharacteristic, ← norm_circleCharacteristic_eq_abs_re]
  exact norm_circleCharacteristic_le_inv_sqrt hu

theorem abs_besselJ0_le_rpow {u : ℝ} (hu : 1 ≤ u) :
    |besselJ0 u| ≤ (4 + 1 / Real.pi) * u ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg (by linarith : 0 ≤ u), ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  exact abs_besselJ0_le_inv_sqrt hu

end Dubon2026
