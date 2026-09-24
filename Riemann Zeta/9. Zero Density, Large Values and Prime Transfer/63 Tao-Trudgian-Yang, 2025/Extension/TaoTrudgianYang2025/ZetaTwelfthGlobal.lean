import TaoTrudgianYang2025.ZetaTwelfthMoment
import TaoTrudgianYang2025.BourgainFourthMoment

/-! The genuine twelfth moment from zero, including the compact initial interval. -/

noncomputable section
open Filter MeasureTheory
namespace TaoTrudgianYang2025

theorem zeta_twelfth_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      (∫ t in 0..T, zetaMomentCriticalNorm t^12) ≤ C*T^(2+ε) := by
  obtain ⟨D,H₀,hD,hd⟩ := zeta_twelfth_dyadic ε hε
  let B := max H₀ 1
  have hB : 1 ≤ B := le_max_right _ _
  obtain ⟨K,hK,hglobal⟩ := integral_zero_le_of_dyadic
    (fun t => zetaMomentCriticalNorm t^12) (continuous_zetaMomentCriticalNorm.pow 12)
    (fun _ => by positivity) (by linarith : 1 ≤ 2+ε) hB hD
    (fun H hH => hd H ((le_max_left _ _).trans hH) (by linarith))
  exact ⟨K,B,hK,hB,hglobal⟩

theorem exists_zeta_global_twelfth_log_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      zetaMomentLogLoss (2*T)^12*(∫ t in 0..3*T, zetaMomentCriticalNorm t^12) ≤
        C*T^(2+ε) := by
  obtain ⟨D,B,hD,hB,hmoment⟩ := zeta_twelfth_zero (by linarith : 0 < ε/2)
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    (eventually_zetaMomentLogLoss_pow_le_rpow 12 (by linarith : 0 < ε/2))
  let C := D*(2 : ℝ)^(ε/2)*(3 : ℝ)^(2+ε/2)
  refine ⟨C,max 1 (max B L),by dsimp [C]; positivity,le_max_left _ _,?_⟩
  intro T hTC
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hTC
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hBT : B ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hTC)
  have hLT : L ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hTC)
  have hm := hmoment (3*T) (by linarith)
  have hl := hL (2*T) (by linarith)
  have hm0 : 0 ≤ ∫ t in 0..3*T, zetaMomentCriticalNorm t^12 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  calc
    _ ≤ (2*T)^(ε/2)*(D*(3*T)^(2+ε/2)) :=
      mul_le_mul hl hm hm0 (Real.rpow_nonneg (by linarith) _)
    _ = (D*(2 : ℝ)^(ε/2)*(3 : ℝ)^(2+ε/2))*
        (T^(ε/2)*T^(2+ε/2)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hT.le,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hT.le]
      ring
    _ = C*T^(2+ε) := by
      rw [← Real.rpow_add hT]
      congr 1
      congr 1
      ring

end TaoTrudgianYang2025

