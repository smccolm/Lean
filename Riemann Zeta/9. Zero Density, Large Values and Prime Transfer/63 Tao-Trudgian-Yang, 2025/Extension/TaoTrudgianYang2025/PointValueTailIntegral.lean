import TaoTrudgianYang2025.PointValueMeasure
import TaoTrudgianYang2025.TruncatedLayerCake

/-!
# Integrating the actual high-value zeta distribution

The power-tail measure is derived from the actual zeta superlevels.
The layer-cake consumer retains the full high-value set and all endpoints.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem pointValueSuperlevel_subset_Icc (H V : ℝ) :
    pointValueSuperlevel H V ⊆ Icc H (2*H) :=
  fun _ ht => ⟨ht.1,ht.2.1⟩

theorem integrableOn_zeta_twelfth_pointValueSuperlevel (H V : ℝ) :
    IntegrableOn (fun t => zetaMomentCriticalNorm t^12) (pointValueSuperlevel H V) :=
  ((continuous_zetaMomentCriticalNorm.pow 12).continuousOn.integrableOn_Icc).mono_set
    (pointValueSuperlevel_subset_Icc H V)

theorem pointValue_power_tail_measure_le {H V s C : ℝ}
    (hV : 0 < V) (hs : 0 < s) (hC : 0 ≤ C)
    (hcount : ∀ U : ℝ, V ≤ U →
      volume (pointValueSuperlevel H U) ≤ ENNReal.ofReal (C/U^12)) :
    (volume.restrict (pointValueSuperlevel H V)).real
      {t | s ≤ zetaMomentCriticalNorm t^12} ≤ C/max (V^12) s := by
  have hevent : MeasurableSet {t | s ≤ zetaMomentCriticalNorm t^12} :=
    (isClosed_le continuous_const (continuous_zetaMomentCriticalNorm.pow 12)).measurableSet
  have hmeasure :
      (volume.restrict (pointValueSuperlevel H V))
        {t | s ≤ zetaMomentCriticalNorm t^12} ≤ ENNReal.ofReal (C/max (V^12) s) := by
    rw [Measure.restrict_apply hevent]
    by_cases hsmall : s ≤ V^12
    · rw [max_eq_left hsmall]
      exact (measure_mono inter_subset_right).trans (hcount V le_rfl)
    · have hVs : V^12 ≤ s := (lt_of_not_ge hsmall).le
      let U : ℝ := s^((12:ℝ)⁻¹)
      have hU : 0 < U := by dsimp only [U]; positivity
      have hUpow : U^12 = s := Real.rpow_inv_natCast_pow hs.le (by norm_num)
      have hVU : V ≤ U := le_of_pow_le_pow_left₀ (by norm_num : (12:ℕ) ≠ 0)
        hU.le (by simpa only [hUpow] using hVs)
      have hsub : {t | s ≤ zetaMomentCriticalNorm t^12} ∩
          pointValueSuperlevel H V ⊆ pointValueSuperlevel H U := by
        intro t ht
        refine ⟨ht.2.1,ht.2.2.1,?_⟩
        apply le_of_pow_le_pow_left₀ (by norm_num : (12:ℕ) ≠ 0)
          (show 0 ≤ zetaMomentCriticalNorm t from norm_nonneg _)
        simpa only [hUpow] using ht.1
      rw [max_eq_right hVs]
      exact (measure_mono hsub).trans (by simpa only [hUpow] using hcount U hVU)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rw [ENNReal.toReal_ofReal (div_nonneg hC ((pow_nonneg hV.le 12).trans (le_max_left _ _)))] at ht
  exact ht

theorem zeta_twelfth_high_integral_le_log {H V M C : ℝ}
    (hV : 0 < V) (hVM : V^12 ≤ M) (hC : 0 ≤ C)
    (hGrowth : ∀ t ∈ pointValueSuperlevel H V, zetaMomentCriticalNorm t^12 ≤ M)
    (hcount : ∀ U : ℝ, V ≤ U →
      volume (pointValueSuperlevel H U) ≤ ENNReal.ofReal (C/U^12)) :
    (∫ t in pointValueSuperlevel H V, zetaMomentCriticalNorm t^12) ≤
      C*(1+Real.log (M/V^12)) := by
  apply integral_le_log_of_truncated_tail (by positivity) hVM
    (integrableOn_zeta_twelfth_pointValueSuperlevel H V)
    (Filter.Eventually.of_forall (fun _ => by positivity))
  · filter_upwards [self_mem_ae_restrict (measurableSet_pointValueSuperlevel H V)] with t ht
    exact hGrowth t ht
  · intro s hs _
    exact pointValue_power_tail_measure_le hV hs hC hcount

theorem exists_zeta_twelfth_power_le_height_cube :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H t : ℝ,
      H₀ ≤ H → H ≤ t → t ≤ 2*H →
      zetaMomentCriticalNorm t^12 ≤ H^3 := by
  obtain ⟨H₀,hH₀,hGrowth⟩ :=
    exists_zetaMomentCriticalNorm_lt_sixth_power (ε := (1/48:ℝ)) (by norm_num)
  refine ⟨H₀,hH₀,?_⟩
  intro H t hH htlo hthi
  have hH1 : 1 ≤ H := by linarith [hH₀.trans hH]
  have hp := pow_le_pow_left₀ (norm_nonneg _) (hGrowth H t hH htlo hthi).le 12
  have he : (H^((1/6:ℝ)+1/48))^12 = H^(9/4:ℝ) := by
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ H)]
    norm_num
  rw [he] at hp
  calc
    zetaMomentCriticalNorm t^12 ≤ H^(9/4:ℝ) := hp
    _ ≤ H^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hH1 (by norm_num)
    _ = H^3 := Real.rpow_natCast H 3

end TaoTrudgianYang2025
