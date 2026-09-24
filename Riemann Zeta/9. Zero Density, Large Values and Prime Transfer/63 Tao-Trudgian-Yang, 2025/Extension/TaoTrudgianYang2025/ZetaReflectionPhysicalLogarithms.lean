import TaoTrudgianYang2025.ZetaReflectionBandLogarithms
import TaoTrudgianYang2025.ZetaMomentAsymptotics

/-! The actual common interval and reflection floor satisfy a uniform quadratic height cap. -/

noncomputable section
open Complex Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem zetaReflection_band_ratio_height_cap (P : ZetaLargeValuePattern)
    (hT : 4 ≤ P.T) (hExp : Real.exp 1 ≤ P.T) (hV : 1 ≤ P.V)
    (hscale : 1 ≤ P.T/(4*Real.pi*P.N)) :
    ((zetaReflectionCommonInterval P.T P.N).card : ℝ)/zetaReflectionValueFloor P ≤
      (336*zetaReflectionConvolutionConstant)*P.T^2 := by
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hK := zetaReflectionConvolutionConstant_pos
  have hL := zetaMomentLogLoss_pos P.T
  have hcard := zetaReflectionCommonInterval_card_bound P.T_pos.le hN hscale
  have hc : ((zetaReflectionCommonInterval P.T P.N).card : ℝ)*(4*Real.pi*P.N) ≤ 6*P.T :=
    (le_div_iff₀ (by positivity : 0 < 4*Real.pi*P.N)).mp
      (by simpa only [mul_div_assoc] using hcard)
  have hden : P.N ≤ 4*Real.pi*P.N := by nlinarith [Real.pi_gt_three]
  have hcardN : ((zetaReflectionCommonInterval P.T P.N).card : ℝ)*P.N ≤ 6*P.T :=
    (mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _)).trans hc
  have hsqrt : 1 ≤ Real.sqrt P.T := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ P.T by linarith)
  have hden1 : 1 ≤ P.V*Real.sqrt P.T := by nlinarith
  have hlog : zetaMomentLogLoss P.T ≤ 7*P.T := by
    have hl := Real.log_le_sub_one_of_pos P.T_pos
    have hb := zetaMomentLogLoss_le_seven_log hT hExp
    linarith
  calc
    _ = 8*zetaReflectionConvolutionConstant*
        (((zetaReflectionCommonInterval P.T P.N).card : ℝ)*P.N)*
        zetaMomentLogLoss P.T/(P.V*Real.sqrt P.T) := by
      unfold zetaReflectionValueFloor
      rw [div_div_eq_mul_div]
      ring
    _ ≤ 8*zetaReflectionConvolutionConstant*
        (((zetaReflectionCommonInterval P.T P.N).card : ℝ)*P.N)*zetaMomentLogLoss P.T :=
      div_le_self (by positivity) hden1
    _ ≤ 8*zetaReflectionConvolutionConstant*(6*P.T)*(7*P.T) := by
      gcongr
    _ = _ := by ring

end TaoTrudgianYang2025
