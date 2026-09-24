import TaoTrudgianYang2025.ZetaReflectionPhysicalLogarithms
import TaoTrudgianYang2025.ZetaSourceLogScales

/-! The complete explicit reflection loss is subpower, uniformly in actual patterns. -/

noncomputable section
open Complex Filter MeasureTheory Set
namespace TaoTrudgianYang2025

def zetaReflectionBandLogConstant : ℝ :=
  2+(Real.log (336*zetaReflectionConvolutionConstant+1)+2)/Real.log 2

theorem zetaReflectionBandLogConstant_pos : 0 < zetaReflectionBandLogConstant := by
  have hK := zetaReflectionConvolutionConstant_pos
  have hlog : 0 ≤ Real.log (336*zetaReflectionConvolutionConstant+1) :=
    Real.log_nonneg (by linarith)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold zetaReflectionBandLogConstant
  positivity

theorem zetaReflectionBandCount_le_log (P : ZetaLargeValuePattern)
    (hT : 4 ≤ P.T) (hExp : Real.exp 1 ≤ P.T) (hV : 1 ≤ P.V)
    (hscale : 1 ≤ P.T/(4*Real.pi*P.N)) :
    (reflectionBandCount (zetaReflectionCommonInterval P.T P.N)
      (zetaReflectionValueFloor P) : ℝ) ≤ zetaReflectionBandLogConstant*Real.log P.T := by
  have hK := zetaReflectionConvolutionConstant_pos
  have hlog : 1 ≤ Real.log P.T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hExp
  apply reflectionBandCount_le_const_log _ (zetaReflectionValueFloor_pos P)
    (by positivity) (by linarith) hlog (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [Real.rpow_two] using zetaReflection_band_ratio_height_cap P hT hExp hV hscale

theorem exists_zetaReflection_height_loss_subpower {η : ℝ} (hη : 0 < η) :
    ∃ T₀ : ℝ, 4 ≤ T₀ ∧
      ∀ P : ZetaLargeValuePattern, T₀ ≤ P.T → 1 ≤ P.V →
        1 ≤ P.T/(4*Real.pi*P.N) →
          216*zetaReflectionConvolutionConstant*zetaMomentLogLoss P.T*
            (reflectionBandCount (zetaReflectionCommonInterval P.T P.N)
              (zetaReflectionValueFloor P) : ℝ) ≤ P.T^η := by
  let C := 216*zetaReflectionConvolutionConstant*7*zetaReflectionBandLogConstant
  have hC : 0 ≤ C := by
    have := zetaReflectionConvolutionConstant_pos
    have := zetaReflectionBandLogConstant_pos
    dsimp [C]
    positivity
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp (eventually_const_log_pow_le_rpow C hC 2 hη)
  refine ⟨max 4 (max (Real.exp 1) T₀),le_max_left _ _,?_⟩
  intro P hT hV hscale
  have hT4 : 4 ≤ P.T := (le_max_left _ _).trans hT
  have hExp : Real.exp 1 ≤ P.T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hsmall := hT₀ P.T ((le_max_right _ _).trans ((le_max_right _ _).trans hT))
  have hL := zetaMomentLogLoss_le_seven_log hT4 hExp
  have hJ := zetaReflectionBandCount_le_log P hT4 hExp hV hscale
  have hK := zetaReflectionConvolutionConstant_pos
  have hCpos := zetaReflectionBandLogConstant_pos
  have hlog : 0 ≤ Real.log P.T := Real.log_nonneg (by linarith)
  calc
    _ ≤ 216*zetaReflectionConvolutionConstant*(7*Real.log P.T)*
        (zetaReflectionBandLogConstant*Real.log P.T) := by
      gcongr
    _ = C*(Real.log P.T)^2 := by dsimp [C]; ring
    _ ≤ _ := hsmall

end TaoTrudgianYang2025
