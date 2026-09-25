import TaoTrudgianYang2025.IvicSixthRestrictedMoment
import TaoTrudgianYang2025.ZetaRealMomentKernel

/-! Continuous truncation of the actual critical-line zeta norm. -/

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

def ivicSixthExcess (U u : ℝ) : ℝ :=
  max 0 (zetaMomentCriticalNorm u-U)

theorem continuous_ivicSixthExcess (U : ℝ) : Continuous (ivicSixthExcess U) :=
  continuous_const.max (continuous_zetaMomentCriticalNorm.sub continuous_const)

theorem ivicSixthExcess_nonneg (U u : ℝ) : 0 ≤ ivicSixthExcess U u :=
  le_max_left _ _

theorem ivicSixthExcess_eq_zero {U u : ℝ} (h : zetaMomentCriticalNorm u ≤ U) :
    ivicSixthExcess U u = 0 := by
  exact max_eq_left (sub_nonpos.mpr h)

theorem ivicSixthExcess_le_norm {U : ℝ} (hU : 0 ≤ U) (u : ℝ) :
    ivicSixthExcess U u ≤ zetaMomentCriticalNorm u := by
  exact max_le (show 0 ≤ zetaMomentCriticalNorm u from norm_nonneg _) (sub_le_self _ hU)

theorem zetaMomentCriticalNorm_le_threshold_add_excess (U u : ℝ) :
    zetaMomentCriticalNorm u ≤ U+ivicSixthExcess U u := by
  have h : zetaMomentCriticalNorm u-U ≤ ivicSixthExcess U u := le_max_right _ _
  linarith

theorem ivicSixthExcess_dyadic_integral_le {H U V : ℝ}
    (hH : 0 ≤ H) (hV : 0 ≤ V) (hVU : V ≤ U) :
    (∫ u in H..2*H, ivicSixthExcess U u^6) ≤
      ∫ u in pointValueSuperlevel H V, zetaMomentCriticalNorm u^6 := by
  classical
  let S := pointValueSuperlevel H V
  have hS : MeasurableSet S := measurableSet_pointValueSuperlevel H V
  have hf : IntegrableOn (fun u => ivicSixthExcess U u^6) (Icc H (2*H)) :=
    ((continuous_ivicSixthExcess U).pow 6).continuousOn.integrableOn_Icc
  have hg : IntegrableOn (fun u => zetaMomentCriticalNorm u^6) (Icc H (2*H)) :=
    (continuous_zetaMomentCriticalNorm.pow 6).continuousOn.integrableOn_Icc
  have hb := setIntegral_mono_on hf (hg.indicator hS) measurableSet_Icc
    (show ∀ u ∈ Icc H (2*H), ivicSixthExcess U u^6 ≤
      S.indicator (fun u => zetaMomentCriticalNorm u^6) u from by
      intro u hu
      by_cases hs : u ∈ S
      · rw [Set.indicator_of_mem hs]
        exact pow_le_pow_left₀ (ivicSixthExcess_nonneg U u)
          (ivicSixthExcess_le_norm (hV.trans hVU) u) 6
      · rw [Set.indicator_of_notMem hs]
        have hlu : zetaMomentCriticalNorm u < V := by
          by_contra hn
          exact hs ⟨hu.1,hu.2,le_of_not_gt hn⟩
        rw [ivicSixthExcess_eq_zero (hlu.le.trans hVU)]
        norm_num)
  rw [setIntegral_indicator hS,inter_eq_right.mpr
    (show S ⊆ Icc H (2*H) from pointValueSuperlevel_subset_Icc H V)] at hb
  simpa only [intervalIntegral.integral_of_le (show H ≤ 2*H by linarith),
    ← integral_Icc_eq_integral_Ioc] using hb

theorem exists_ivicSixthExcess_dyadic_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H U : ℝ, H₀ ≤ H →
      H^(11/72+ε) ≤ U →
      (∫ u in H..2*H, ivicSixthExcess U u^6) ≤ H^(1+ε) := by
  obtain ⟨H₀,hH₀,hbound⟩ := exists_ivicSixth_restricted_moment hε
  refine ⟨H₀,hH₀,?_⟩
  intro H U hH hU
  have hH0 : 0 ≤ H := by linarith [hH₀.trans hH]
  exact (ivicSixthExcess_dyadic_integral_le hH0 (Real.rpow_nonneg hH0 _) hU).trans
    (hbound H hH)

end TaoTrudgianYang2025
