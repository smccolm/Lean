import TaoTrudgianYang2025.SargosQuarticMorseWindow
import TaoTrudgianYang2025.SargosPositiveQuadraticLocal

/-! Width-independent positive stationary errors on the actual cutoff plateau. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

def sargosQuarticLocalRemainderConstant : ℝ :=
  4*sargosQuarticMorseInverseDerivativeBound 1/Real.pi+
    (4*sargosQuarticMorseInverseDerivativeBound 3+2*sargosQuarticMorseInverseDerivativeBound 4)/(2*Real.pi)

theorem sargosQuarticLocalRemainderConstant_nonneg :
    0 ≤ sargosQuarticLocalRemainderConstant := by
  unfold sargosQuarticLocalRemainderConstant
  positivity [sargosQuarticMorseInverseDerivativeBound_nonneg 1,
    sargosQuarticMorseInverseDerivativeBound_nonneg 3,
    sargosQuarticMorseInverseDerivativeBound_nonneg 4]

theorem sargosQuarticBufferedWeight_local_window_remainder {ε r l b η d H T : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hd : 0 < d)
    (hleft : l+2*η+d ≤ r) (hright : r+d ≤ b-2*η)
    (hH : 0 < H) (hsmall : H < d/2) (hT : 0 < T) :
    ‖(∫ z in (-H)..H,
        (sargosQuarticMorseWeight (modelPhaseBufferedCutoff l b η) ε r z : ℂ)*
          (𝐞 ((T/2)*z^2) : ℂ))-
      ((deriv (sargosQuarticMorseInverse ε r) 0 : ℝ) : ℂ)*
        ((𝐞 ((1:ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
      quadraticRemainderConstant H (sargosQuarticMorseInverseDerivativeBound 1)
        (sargosQuarticMorseInverseDerivativeBound 3) (sargosQuarticMorseInverseDerivativeBound 4)/T := by
  have hs₁₂ := modelPhaseBufferedCutoff_tsupport_model hη hl hb
  have hs : tsupport (modelPhaseBufferedCutoff l b η) ⊆ Ioo (0 : ℝ) 3 := by
    intro u hu
    have h := hs₁₂ hu
    constructor <;> linarith [h.1,h.2]
  have hro : r ∈ Ioo (0 : ℝ) 3 := by constructor <;> linarith
  have hzero : sargosQuarticMorseWeight (modelPhaseBufferedCutoff l b η) ε r 0 =
      deriv (sargosQuarticMorseInverse ε r) 0 := by
    rw [sargosQuarticMorseWeight_eq (sargosQuarticMorseRange_zero hro),
      sargosQuarticMorseAmplitude,sargosQuarticMorseInverse_zero hε hr,
      modelPhaseBufferedCutoff_one hη (by linarith) (by linarith),one_mul]
  have hjet (n : ℕ) : ∀ z ∈ Icc (-H) H,
      |iteratedDeriv n (sargosQuarticMorseWeight (modelPhaseBufferedCutoff l b η) ε r) z| ≤
        sargosQuarticMorseInverseDerivativeBound (n+1) :=
    fun z hz => sargosQuarticBufferedWeight_local_jet_bound hε hr hη hl hb hd hleft hright hsmall hz n
  have h₀ := hjet 0 0 (show (0:ℝ) ∈ Icc (-H) H by constructor <;> linarith)
  have h := sargos_positive_quadratic_window_remainder
    (sargosQuarticMorseWeight_contDiff (modelPhaseBufferedCutoff_contDiff l b η) hs hε hr)
    hT hH h₀ (hjet 2) (hjet 3)
  simpa only [hzero] using h

theorem sargosQuarticBufferedWeight_local_window_remainder_inverse {ε r l b η d H T : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hd : 0 < d)
    (hleft : l+2*η+d ≤ r) (hright : r+d ≤ b-2*η)
    (hH : 0 < H) (hH₁ : H ≤ 1) (hsmall : H < d/2) (hT : 0 < T) :
    ‖(∫ z in (-H)..H,
        (sargosQuarticMorseWeight (modelPhaseBufferedCutoff l b η) ε r z : ℂ)*
          (𝐞 ((T/2)*z^2) : ℂ))-
      ((deriv (sargosQuarticMorseInverse ε r) 0 : ℝ) : ℂ)*
        ((𝐞 ((1:ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
      sargosQuarticLocalRemainderConstant/(T*H) := by
  have h := sargosQuarticBufferedWeight_local_window_remainder hε hr hη hl hb hd
    hleft hright hH hsmall hT
  have hc := quadraticRemainderConstant_le_inverse_window
    (M₀ := sargosQuarticMorseInverseDerivativeBound 1) hH hH₁
    (sargosQuarticMorseInverseDerivativeBound_nonneg 3)
    (sargosQuarticMorseInverseDerivativeBound_nonneg 4)
  apply h.trans
  convert div_le_div_of_nonneg_right hc hT.le using 1
  unfold sargosQuarticLocalRemainderConstant
  ring

end TaoTrudgianYang2025
