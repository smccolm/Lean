import TaoTrudgianYang2025.IvicSixthTailIntegral
import TaoTrudgianYang2025.PointValueHighMoment

/-! Actual sixth moment above the 11/72 threshold, with arbitrary power loss. -/

noncomputable section
open MeasureTheory Filter Set
namespace TaoTrudgianYang2025

theorem eventually_ivicSixth_high_log_budget {η ε : ℝ} (hgap : η < ε) :
    ∀ᶠ H : ℝ in atTop,
      2*H^(1+η)*(1+3*Real.log H) ≤ H^(1+ε) := by
  have h0 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 4) (a := 1+η) (b := 1+ε) (by norm_num) 0 (by linarith)
  have h1 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 12) (a := 1+η) (b := 1+ε) (by norm_num) 1 (by linarith)
  filter_upwards [h0,h1,eventually_ge_atTop (1:ℝ)] with H h0 h1 hH
  simp only [pow_zero,mul_one,pow_one] at h0 h1
  have hlog : Real.log H ≤ Real.log (3*H) :=
    Real.log_le_log (by linarith) (by linarith)
  have hm := mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ H^(1+η))
  nlinarith

theorem exists_ivicSixth_restricted_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      (∫ t in pointValueSuperlevel H (H^(11/72+ε)),
        zetaMomentCriticalNorm t^6) ≤ H^(1+ε) := by
  let η : ℝ := min (ε/2) (1/100)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηsmall : η ≤ 1/100 := min_le_right _ _
  have hηε : η < ε := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨B,hB,hcount⟩ := exists_ivicSixth_volume_superlevel_le hη
  obtain ⟨B₁,hB₁,hGrowth⟩ := exists_ivicSixth_power_le_height_cube
  obtain ⟨B₂,hB₂⟩ := eventually_atTop.mp (eventually_ivicSixth_high_log_budget hηε)
  refine ⟨max B (max B₁ B₂),le_max_of_le_left hB,?_⟩
  intro H hH
  have hHB : B ≤ H := (le_max_left _ _).trans hH
  have hHB₁ : B₁ ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hHB₂ : B₂ ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hH1 : 1 ≤ H := by linarith [hB.trans hHB]
  have hH0 : 0 < H := by linarith
  let V : ℝ := H^(11/72+η)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hV1 : 1 ≤ V := Real.one_le_rpow hH1 (by linarith)
  have hA1 : 1 ≤ V^6 := one_le_pow₀ hV1
  have hVM : V^6 ≤ H^3 := by
    dsimp only [V]
    rw [← Real.rpow_mul_natCast hH0.le]
    calc
      H^((11/72+η)*(6:ℝ)) ≤ H^(3:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
      _ = H^3 := Real.rpow_natCast H 3
  have hvol : ∀ U : ℝ, V ≤ U →
      volume (pointValueSuperlevel H U) ≤ ENNReal.ofReal ((2*H^(1+η))/U^6) := by
    intro U hVU
    exact hcount H U hHB (hV.trans_le hVU) hVU
  have hi := ivicSixth_high_integral_le_log hV hVM
    (by positivity : 0 ≤ 2*H^(1+η))
    (fun t ht => hGrowth H t hHB₁ ht.1 ht.2.1) hvol
  have hlog := log_height_cube_div_le hH1 hA1
  have hsubset :
      pointValueSuperlevel H (H^(11/72+ε)) ⊆ pointValueSuperlevel H V := by
    intro t ht
    refine ⟨ht.1,ht.2.1,?_⟩
    exact (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)).trans ht.2.2
  calc
    (∫ t in pointValueSuperlevel H (H^(11/72+ε)), zetaMomentCriticalNorm t^6) ≤
        ∫ t in pointValueSuperlevel H V, zetaMomentCriticalNorm t^6 :=
      setIntegral_mono_set (integrableOn_ivicSixth_pointValueSuperlevel H V)
        (Filter.Eventually.of_forall (fun _ => by positivity))
        (Filter.Eventually.of_forall hsubset)
    _ ≤ (2*H^(1+η))*(1+Real.log (H^3/V^6)) := hi
    _ ≤ 2*H^(1+η)*(1+3*Real.log H) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ H^(1+ε) := hB₂ H hHB₂

end TaoTrudgianYang2025
