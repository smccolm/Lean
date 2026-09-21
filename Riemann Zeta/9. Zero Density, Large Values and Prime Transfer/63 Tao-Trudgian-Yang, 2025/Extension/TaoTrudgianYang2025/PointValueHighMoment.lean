import TaoTrudgianYang2025.PointValueTailIntegral

/-!
# The complete high-value part of the actual critical twelfth moment

Every high-value point is included in the measured superlevel set.
The proved finite peak count, full measure covering, actual growth and
layer cake are composed without any analytic theorem parameter.
-/

noncomputable section

open MeasureTheory Filter Set

namespace TaoTrudgianYang2025

theorem log_height_cube_div_le {H A : ℝ} (hH : 1 ≤ H) (hA : 1 ≤ A) :
    Real.log (H^3/A) ≤ 3*Real.log H := by
  have hH0 : 0 < H := by linarith
  have hA0 : 0 < A := by linarith
  rw [Real.log_div (by positivity : H^3 ≠ 0) hA0.ne',Real.log_pow]
  have hlog := Real.log_nonneg hA
  norm_num
  linarith

theorem eventually_zeta_high_log_budget {η ε : ℝ} (hgap : η < ε) :
    ∀ᶠ H : ℝ in atTop,
      2*H^(2+η)*(1+3*Real.log H) ≤ H^(2+ε) := by
  have h0 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 4) (a := 2+η) (b := 2+ε) (by norm_num) 0 (by linarith)
  have h1 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 12) (a := 2+η) (b := 2+ε) (by norm_num) 1 (by linarith)
  filter_upwards [h0,h1,eventually_ge_atTop (1:ℝ)] with H h0 h1 hH
  simp only [pow_zero,mul_one,pow_one] at h0 h1
  have hlog : Real.log H ≤ Real.log (3*H) :=
    Real.log_le_log (by linarith) (by linarith)
  have hm := mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ H^(2+η))
  nlinarith

theorem exists_zeta_twelfth_high_integral_le {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      (∫ t in pointValueSuperlevel H (H^(1/8+ε)),
        zetaMomentCriticalNorm t^12) ≤ H^(2+ε) := by
  let η : ℝ := min (ε/2) (1/100)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηsmall : η ≤ 1/100 := min_le_right _ _
  have hηε : η < ε := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨B,hB,hcount⟩ := exists_volume_pointValueSuperlevel_le hη
  obtain ⟨B₁,hB₁,hGrowth⟩ := exists_zeta_twelfth_power_le_height_cube
  obtain ⟨B₂,hB₂⟩ := eventually_atTop.mp (eventually_zeta_high_log_budget hηε)
  refine ⟨max B (max B₁ B₂),le_max_of_le_left hB,?_⟩
  intro H hH
  have hHB : B ≤ H := (le_max_left _ _).trans hH
  have hHB₁ : B₁ ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hHB₂ : B₂ ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hH1 : 1 ≤ H := by linarith [hB.trans hHB]
  have hH0 : 0 < H := by linarith
  let V : ℝ := H^(1/8+η)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hV1 : 1 ≤ V := Real.one_le_rpow hH1 (by linarith)
  have hA1 : 1 ≤ V^12 := one_le_pow₀ hV1
  have hVM : V^12 ≤ H^3 := by
    dsimp only [V]
    rw [← Real.rpow_mul_natCast hH0.le]
    calc
      H^((1/8+η)*(12:ℝ)) ≤ H^(3:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
      _ = H^3 := Real.rpow_natCast H 3
  have hvol : ∀ U : ℝ, V ≤ U →
      volume (pointValueSuperlevel H U) ≤ ENNReal.ofReal ((2*H^(2+η))/U^12) := by
    intro U hVU
    exact hcount H U hHB (hV.trans_le hVU) hVU
  have hi := zeta_twelfth_high_integral_le_log hV hVM
    (by positivity : 0 ≤ 2*H^(2+η))
    (fun t ht => hGrowth H t hHB₁ ht.1 ht.2.1) hvol
  have hlog := log_height_cube_div_le hH1 hA1
  have hsubset :
      pointValueSuperlevel H (H^(1/8+ε)) ⊆ pointValueSuperlevel H V := by
    intro t ht
    refine ⟨ht.1,ht.2.1,?_⟩
    exact (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)).trans ht.2.2
  calc
    (∫ t in pointValueSuperlevel H (H^(1/8+ε)), zetaMomentCriticalNorm t^12) ≤
        ∫ t in pointValueSuperlevel H V, zetaMomentCriticalNorm t^12 :=
      setIntegral_mono_set (integrableOn_zeta_twelfth_pointValueSuperlevel H V)
        (Filter.Eventually.of_forall (fun _ => by positivity))
        (Filter.Eventually.of_forall hsubset)
    _ ≤ (2*H^(2+η))*(1+Real.log (H^3/V^12)) := hi
    _ ≤ 2*H^(2+η)*(1+3*Real.log H) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ H^(2+ε) := hB₂ H hHB₂

end TaoTrudgianYang2025
