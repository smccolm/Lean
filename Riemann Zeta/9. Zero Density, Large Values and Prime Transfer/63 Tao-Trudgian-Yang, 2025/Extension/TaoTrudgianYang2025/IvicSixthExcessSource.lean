import TaoTrudgianYang2025.IvicSixthExcess
import TaoTrudgianYang2025.ZetaRealMomentAsymptotics

/-! The actual truncated sixth moment on the literal Perron source window. -/

noncomputable section
open Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem ivicSixthExcess_source_le_three (U : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ u in T/2..3*T, ivicSixthExcess U u^6) ≤
      (∫ u in T/2..T, ivicSixthExcess U u^6)+
      (∫ u in T..2*T, ivicSixthExcess U u^6)+
      (∫ u in 2*T..4*T, ivicSixthExcess U u^6) := by
  have hc := (continuous_ivicSixthExcess U).pow 6
  have hlast : (∫ u in 2*T..3*T, ivicSixthExcess U u^6) ≤
      ∫ u in 2*T..4*T, ivicSixthExcess U u^6 := by
    apply intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
    · exact Filter.Eventually.of_forall (fun u => pow_nonneg (ivicSixthExcess_nonneg U u) 6)
    · exact hc.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (T/2) T)
    (hc.intervalIntegrable T (3*T)),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable T (2*T))
      (hc.intervalIntegrable (2*T) (3*T))]
  linarith

theorem exists_ivicSixthExcess_source_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      (∫ u in T/2..3*T, ivicSixthExcess ((4*T)^(11/72+ε)) u^6) ≤ C*T^(1+ε) := by
  obtain ⟨A,hA,hbound⟩ := exists_ivicSixthExcess_dyadic_bound hε
  let C : ℝ := (2:ℝ)^(-(1+ε))+1+(2:ℝ)^(1+ε)
  refine ⟨C,by dsimp [C]; positivity,2*A,by linarith,?_⟩
  intro T hT
  have hT0 : 0 < T := by linarith
  let U := (4*T)^(11/72+ε)
  have hb (H : ℝ) (hAH : A ≤ H) (hH : 0 < H) (hHT : H ≤ 4*T) :
      (∫ u in H..2*H, ivicSixthExcess U u^6) ≤ H^(1+ε) :=
    hbound H U hAH (Real.rpow_le_rpow hH.le hHT (by linarith))
  have hh := hb (T/2) (by linarith) (by positivity) (by linarith)
  have hm := hb T (by linarith) hT0 (by linarith)
  have hl := hb (2*T) (by linarith) (by positivity) (by linarith)
  have hhalf : (T/2)^(1+ε) = (2:ℝ)^(-(1+ε))*T^(1+ε) := by
    rw [Real.div_rpow hT0.le (by norm_num),Real.rpow_neg (by norm_num)]
    ring
  have hd : (2*T)^(1+ε) = (2:ℝ)^(1+ε)*T^(1+ε) :=
    Real.mul_rpow (by norm_num) hT0.le
  rw [show 2*(T/2)=T by ring,hhalf] at hh
  rw [show 2*(2*T)=4*T by ring,hd] at hl
  have hs := ivicSixthExcess_source_le_three U hT0
  change (∫ u in T/2..3*T, ivicSixthExcess U u^6) ≤ C*T^(1+ε)
  dsimp [C]
  nlinarith

theorem eventually_ivicSixthExcess_source_log_moment {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      zetaMomentLogLoss T^6*
        (∫ u in T/2..3*T, ivicSixthExcess ((4*T)^(11/72+ε)) u^6) ≤ T^(1+3*ε) := by
  obtain ⟨C,hC,A,hA,hmoment⟩ := exists_ivicSixthExcess_source_moment hε
  have hlog : ∀ᶠ T : ℝ in atTop, zetaMomentLogLoss T^6 ≤ T^ε := by
    simpa only [Real.rpow_ofNat] using
      eventually_zetaMomentLogLoss_rpow_le_rpow (by norm_num : (0:ℝ) ≤ 6) hε
  have hconst := (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop C)
  filter_upwards [hlog,hconst,eventually_ge_atTop A] with T hl hc hT
  have hT0 : 0 < T := by linarith
  calc
    _ ≤ zetaMomentLogLoss T^6*(C*T^(1+ε)) :=
      mul_le_mul_of_nonneg_left (hmoment T hT) (by positivity)
    _ ≤ T^ε*(T^ε*T^(1+ε)) :=
      mul_le_mul hl (mul_le_mul_of_nonneg_right hc (by positivity))
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hT0,← Real.rpow_add hT0]; congr 1; ring

end TaoTrudgianYang2025
