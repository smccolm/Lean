import TaoTrudgianYang2025.AtkinsonEvaluatedPhases

/-!
# Uniform power saving for the actual small-frequency carriers

The stationary radius is chosen from the physical parameters, rather than
left as an extra analytic hypothesis. This is a per-carrier estimate, not
yet a summable error theorem for the full divisor series.
-/

noncomputable section

open Complex Filter

namespace TaoTrudgianYang2025

theorem atkinsonStationary_error_le_of_power_balance {S G X : ℝ}
    (hS : 0 < S) (hX : 0 < X) (hGX : G * X ^ 3 ≤ S) (hXS : X ^ 5 ≤ S) :
    4 / ((X / 12) * Real.pi) + 4 * (G / S) * (X / 12) ^ 2 +
      432 * (X / 12) ^ 4 / S ≤ 20 / X := by
  have hfirst : 4 / ((X / 12) * Real.pi) ≤ 16 / X := by
    apply (div_le_div_iff₀ (by positivity) hX).2
    nlinarith [Real.pi_gt_three]
  have hsecond : 4 * (G / S) * (X / 12) ^ 2 ≤ 1 / (36 * X) := by
    apply (le_div_iff₀ (by positivity)).2
    apply (mul_le_mul_iff_left₀ hS).mp
    field_simp
    nlinarith
  have hthird : 432 * (X / 12) ^ 4 / S ≤ 1 / (48 * X) := by
    apply (div_le_div_iff₀ hS (by positivity)).2
    nlinarith
  calc
    _ ≤ 16 / X + 1 / (36 * X) + 1 / (48 * X) := by linarith
    _ ≤ 20 / X := by
      apply (mul_le_mul_iff_left₀ hX).mp
      field_simp
      norm_num

theorem exists_atkinsonPowerIntegral_small_frequency_power_saving (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η T G L b : ℝ, 0 < η → η ≤ 1 / 10 → 1 ≤ T →
      1 ≤ G → G ≤ T ^ (1 / 2 - 3 * η) → 1 ≤ L → 8 * L ≤ G →
      |b| ≤ Real.sqrt T / 100 →
      ‖atkinsonPowerIntegral T G L α b - atkinsonStationaryMain T G L α b‖ ≤
        C * G * T ^ (-α) * T ^ (-η) := by
  obtain ⟨C, hC, hbound⟩ := exists_atkinsonPowerIntegral_small_frequency_stationary α
  refine ⟨20 * C, by positivity, ?_⟩
  intro η T G L b hη hηmax hT hG hGT hL hwidth hb
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hX : 0 < T ^ η := Real.rpow_pos_of_pos hTp η
  have hS : 0 < Real.sqrt T := Real.sqrt_pos.2 hTp
  have hXS : T ^ η ≤ Real.sqrt T := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hGS : G ≤ Real.sqrt T := by
    apply hGT.trans
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hGsq : G ^ 2 ≤ 2 * T := by
    nlinarith [Real.sq_sqrt hTp.le]
  have hGX : G * (T ^ η) ^ 3 ≤ Real.sqrt T := by
    calc
      _ ≤ T ^ (1 / 2 - 3 * η) * (T ^ η) ^ 3 := by gcongr
      _ = Real.sqrt T := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTp.le, ← Real.rpow_add hTp,
          Real.sqrt_eq_rpow]
        congr 1
        ring
  have hX5 : (T ^ η) ^ 5 ≤ Real.sqrt T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTp.le, Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hT
    norm_num
    linarith
  have herr := atkinsonStationary_error_le_of_power_balance hS hX hGX hX5
  have h := hbound T G L b (T ^ η / 12) hTp hG hGsq hL hwidth
    (by positivity) (by linarith) hb
  apply h.trans
  calc
    _ ≤ C * G * T ^ (-α) * (20 / T ^ η) :=
      mul_le_mul_of_nonneg_left herr (by positivity)
    _ = _ := by rw [Real.rpow_neg hTp.le η]; ring

theorem exists_atkinsonPowerIntegral_source_power_saving (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) → ∀ n : ℕ, 10000 * (n : ℝ) ≤ T →
      ‖atkinsonPowerIntegral T G (Real.log T) α (Real.sqrt n) -
        atkinsonStationaryMain T G (Real.log T) α (Real.sqrt n)‖ ≤
          C * G * T ^ (-α) * T ^ (-min (δ / 3) (1 / 10)) ∧
      ‖atkinsonPowerIntegral T G (Real.log T) α (-Real.sqrt n) -
        atkinsonStationaryMain T G (Real.log T) α (-Real.sqrt n)‖ ≤
          C * G * T ^ (-α) * T ^ (-min (δ / 3) (1 / 10)) := by
  obtain ⟨C, hC, hbound⟩ := exists_atkinsonPowerIntegral_small_frequency_power_saving α
  have hη : 0 < min (δ / 3) (1 / 10 : ℝ) := lt_min (by positivity) (by norm_num)
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ∀ b : ℝ, |b| ≤ Real.sqrt T / 100 →
      ‖atkinsonPowerIntegral T G (Real.log T) α b -
        atkinsonStationaryMain T G (Real.log T) α b‖ ≤
          C * G * T ^ (-α) * T ^ (-min (δ / 3) (1 / 10)) := by
    filter_upwards [eventually_zetaSmoothDivisorTest_support_physical hδ,
      eventually_zeta_source_log_window_scales hδ] with T hsupport hscale
    intro G hlower hupper b hb
    have hT : 1 ≤ T := by linarith [hsupport.1]
    obtain ⟨_, _, hwidth, _⟩ := hsupport.2 G hlower
    apply hbound (min (δ / 3) (1 / 10)) T G (Real.log T) b hη
      (min_le_right _ _) hT ((Real.one_le_rpow hT hδ.le).trans hlower) _
      hscale.2.1 hwidth hb
    apply hupper.trans (Real.rpow_le_rpow_of_exponent_le hT _)
    linarith [min_le_left (δ / 3) (1 / 10 : ℝ)]
  obtain ⟨B, hB⟩ := eventually_atTop.mp hev
  refine ⟨C, hC, max 16 B, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper n hn
  have hTp : 0 < T := by linarith [le_max_left 16 B]
  have hb := sqrt_nat_small_frequency hTp n hn
  have h := hB T ((le_max_right _ _).trans hT) G hlower hupper
  exact ⟨h (Real.sqrt n) hb, h (-Real.sqrt n) (by simpa only [abs_neg])⟩

end TaoTrudgianYang2025
