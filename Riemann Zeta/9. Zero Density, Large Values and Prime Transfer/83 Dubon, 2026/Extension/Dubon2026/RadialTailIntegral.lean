import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Exact integrals for the radial majorants used in the Steinhaus estimate -/

namespace Dubon2026

open MeasureTheory Set

theorem sqrt_pow_eq_rpow (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt r ^ m = r ^ ((m : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hr]
  congr 1
  ring

theorem radial_sqrt_power_eq (C : ℝ) (m : ℕ) {r : ℝ} (hr : 0 < r) :
    r * (C / Real.sqrt r) ^ m = C ^ m * r ^ (1 - (m : ℝ) / 2) := by
  rw [div_pow, sqrt_pow_eq_rpow m hr.le, Real.rpow_sub hr, Real.rpow_one]
  ring

theorem radial_tail_integrable (C : ℝ) {m : ℕ} (hm : 5 ≤ m) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun r : ℝ => r * (C / Real.sqrt r) ^ m) (Ioi R) := by
  have hm' : (4 : ℝ) < m := by exact_mod_cast (by omega : 4 < m)
  have he : 1 - (m : ℝ) / 2 < -1 := by linarith
  have hi : IntegrableOn (fun r : ℝ => C ^ m * r ^ (1 - (m : ℝ) / 2)) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt he hR).const_mul (C ^ m)
  exact hi.congr_fun (fun r hr => (radial_sqrt_power_eq C m (hR.trans hr)).symm) measurableSet_Ioi

theorem integral_radial_tail_exact (C : ℝ) {m : ℕ} (hm : 5 ≤ m) {R : ℝ} (hR : 0 < R) :
    (∫ r : ℝ in Ioi R, r * (C / Real.sqrt r) ^ m) =
      R ^ 2 * (C / Real.sqrt R) ^ m / ((m : ℝ) / 2 - 2) := by
  have hm' : (4 : ℝ) < m := by exact_mod_cast (by omega : 4 < m)
  have he : 1 - (m : ℝ) / 2 < -1 := by linarith
  have hi : (∫ r : ℝ in Ioi R, r * (C / Real.sqrt r) ^ m) =
      C ^ m * ∫ r : ℝ in Ioi R, r ^ (1 - (m : ℝ) / 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    exact radial_sqrt_power_eq C m (hR.trans hr)
  rw [hi, integral_Ioi_rpow_of_lt he hR,
    show 1 - (m : ℝ) / 2 + 1 = 2 - (m : ℝ) / 2 by ring,
    Real.rpow_sub hR, Real.rpow_two, div_pow, sqrt_pow_eq_rpow m hR.le]
  rw [show 2 - (m : ℝ) / 2 = -((m : ℝ) / 2 - 2) by ring, div_neg]
  ring

theorem integral_radial_tail_le {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R) (hCR : C ^ 2 ≤ R)
    {m : ℕ} (hm : 5 ≤ m) :
    (m : ℝ) * (∫ r : ℝ in Ioi R, r * (C / Real.sqrt r) ^ m) ≤ 10 * R ^ 2 := by
  have hm' : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : 0 < (m : ℝ) / 2 - 2 := by linarith
  have hs : C ≤ Real.sqrt R := by
    apply (sq_le_sq₀ hC (Real.sqrt_nonneg R)).1
    rw [Real.sq_sqrt hR.le]
    exact hCR
  have hq : (C / Real.sqrt R) ^ m ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one (Real.sqrt_pos.2 hR)).2 hs)
  rw [integral_radial_tail_exact C hm hR]
  calc
    _ ≤ (m : ℝ) * (R ^ 2 * 1 / ((m : ℝ) / 2 - 2)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq (sq_nonneg R)) hd.le) (by positivity)
    _ ≤ 10 * R ^ 2 := by
      rw [mul_one, ← mul_div_assoc, div_le_iff₀ hd]
      nlinarith [sq_nonneg R]

theorem integral_radial_tail_scaled (C R : ℝ) (m : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ r : ℝ in Ioi (R / a), r * (C / Real.sqrt (a * r)) ^ m) =
      a⁻¹ ^ 2 * ∫ r : ℝ in Ioi R, r * (C / Real.sqrt r) ^ m := by
  have he (r : ℝ) : r * (C / Real.sqrt (a * r)) ^ m =
      a⁻¹ * ((a * r) * (C / Real.sqrt (a * r)) ^ m) := by
    field_simp
  simp_rw [he]
  rw [integral_const_mul, integral_comp_mul_left_Ioi
    (fun r : ℝ => r * (C / Real.sqrt r) ^ m) (R / a) ha,
    mul_div_cancel₀ R ha.ne']
  simp only [smul_eq_mul]
  ring

theorem integral_radial_tail_comparable_le {C R K : ℝ}
    (hC : 0 ≤ C) (hR : 0 < R) (hCR : C ^ 2 ≤ R) (hK : 0 < K)
    {m : ℕ} (hm : 5 ≤ m) :
    (∫ r : ℝ in Ioi (R * K * Real.sqrt m),
      r * (C / Real.sqrt ((1 / (K * Real.sqrt m)) * r)) ^ m) ≤ 10 * K ^ 2 * R ^ 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have he : R * K * Real.sqrt m = R / (1 / (K * Real.sqrt m)) := by field_simp
  rw [he, integral_radial_tail_scaled C R m (by positivity)]
  have hscale : (1 / (K * Real.sqrt m))⁻¹ ^ 2 = K ^ 2 * (m : ℝ) := by
    rw [one_div, inv_inv, mul_pow, Real.sq_sqrt hm0.le]
  rw [hscale]
  calc
    _ = K ^ 2 * ((m : ℝ) * ∫ r : ℝ in Ioi R, r * (C / Real.sqrt r) ^ m) := by ring
    _ ≤ K ^ 2 * (10 * R ^ 2) :=
      mul_le_mul_of_nonneg_left (integral_radial_tail_le hC hR hCR hm) (sq_nonneg K)
    _ = _ := by ring

theorem radial_tail_scaled_integrable (C : ℝ) {m : ℕ} (hm : 5 ≤ m)
    {R a : ℝ} (hR : 0 < R) (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r * (C / Real.sqrt (a * r)) ^ m) (Ioi (R / a)) := by
  have hi : IntegrableOn (fun r : ℝ => (a * r) * (C / Real.sqrt (a * r)) ^ m)
      (Ioi (R / a)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun r : ℝ => r * (C / Real.sqrt r) ^ m) (R / a) ha).2
    rw [mul_div_cancel₀ R ha.ne']
    exact radial_tail_integrable C hm hR
  have hj : IntegrableOn (fun r : ℝ => a⁻¹ * ((a * r) * (C / Real.sqrt (a * r)) ^ m))
      (Ioi (R / a)) := hi.const_mul a⁻¹
  apply hj.congr_fun _ measurableSet_Ioi
  intro r _
  field_simp

end Dubon2026
