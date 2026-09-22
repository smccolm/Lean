import TaoTrudgianYang2025.BetaBufferedWindowTails
import TaoTrudgianYang2025.BetaMorseRemainder

/-!
# Sharp interior stationary error for the original cutoff

The constant depends only on sigma. A critical point d inside both
cutoff plateau edges has error O(1/(T*d)) in normalized coordinates,
using a finite original-model order and no inverse cutoff-width loss.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

def bufferedInteriorStationaryConstant (σ : ℝ) : ℝ :=
  8*Real.sqrt (σ+1)/(modelPhaseCurvatureLower σ*Real.pi)+
    (4*morseInverseDerivativeBound σ 1/Real.pi+
      (4*morseInverseDerivativeBound σ 3+2*morseInverseDerivativeBound σ 4)/(2*Real.pi))

theorem bufferedNormalizedMode_interior_window_remainder
    {F : ℝ → ℝ} {σ δ v l r η d H T : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hd : 0 < d)
    (hleft : l+2*η+d ≤ modelPhaseInverseSlope F v)
    (hright : modelPhaseInverseSlope F v+d ≤ r-2*η)
    (hH : 0 < H) (hH₁ : H ≤ 1)
    (hsmall : H < Real.sqrt (modelPhaseCurvatureLower σ)*d) (hT : 0 < T) :
    ‖modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T (T*v)-
      (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ)*
        ((modelPhaseStationaryAmplitude F v : ℂ)*
          ((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)))‖ ≤
      bufferedInteriorStationaryConstant σ/(T*H) := by
  have hF₁ := approximateModelPhase_mono hF bufferedLocalStationaryOrder_pos le_rfl
  have hgeom (z : ℝ) (hz : z ∈ Icc (-H) H) :=
    modelPhaseMorseWindow_mem_and_inverse hσ hδ hF₁ hv hd
      (show 1 < modelPhaseInverseSlope F v-d by linarith)
      (show modelPhaseInverseSlope F v+d < 2 by linarith) hsmall hz
  have hs : Icc (-H) H ⊆ modelPhaseMorseRange F v := fun z hz => (hgeom z hz).1
  have hminus : -H ∈ Icc (-H) H := ⟨le_rfl,by linarith⟩
  have hplus : H ∈ Icc (-H) H := ⟨by linarith,le_rfl⟩
  have hm := abs_lt.mp (hgeom (-H) hminus).2
  have hp := abs_lt.mp (hgeom H hplus).2
  have htail := norm_bufferedNormalizedMode_sub_window_le hσ hδ hF₁ hv hT hη hl hr hH
    (hs hminus) (hs hplus) (show l+η ≤ modelPhaseMorseInverse F v (-H) by linarith [hm.1])
    (show modelPhaseMorseInverse F v H ≤ r-η by linarith [hp.2])
  have hcentral := bufferedMorseWeight_local_window_remainder_inverse hσ hδ hF hv hη hl hr hd
    hleft hright hH hH₁ hsmall hT
  let mid := ∫ u in modelPhaseMorseInverse F v (-H)..modelPhaseMorseInverse F v H,
    (modelPhaseBufferedCutoff l r η u : ℂ)*(𝐞 (T*F u-(T*v)*u) : ℂ)
  let main := (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ)*
    ((modelPhaseStationaryAmplitude F v : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)))
  have hmid : ‖mid-main‖ ≤
      (4*morseInverseDerivativeBound σ 1/Real.pi+
        (4*morseInverseDerivativeBound σ 3+2*morseInverseDerivativeBound σ 4)/(2*Real.pi))/(T*H) := by
    dsimp only [mid,main]
    rw [modelPhaseMorse_window_integral (modelPhaseBufferedCutoff_contDiff l r η).continuous
      hσ hδ hF₁ hv hH.le hs T,← mul_sub,norm_mul,Circle.norm_coe,one_mul]
    exact hcentral
  have hn := norm_add_le
    (modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T (T*v)-mid) (mid-main)
  rw [sub_add_sub_cancel] at hn
  apply (hn.trans (add_le_add htail hmid)).trans_eq
  unfold bufferedInteriorStationaryConstant
  ring

theorem modelPhaseBufferedMorseRemainder_interior_uniform
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η d : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → 0 < d →
      ∀ (F : ℝ → ℝ) (δ v T : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        v ∈ modelPhaseSlopeRange F → 0 < T →
        l+2*η+d ≤ modelPhaseInverseSlope F v →
        modelPhaseInverseSlope F v+d ≤ r-2*η →
        ‖modelPhaseMorseRemainder (modelPhaseBufferedCutoff l r η) F T v‖ ≤ C/(T*d) := by
  let γ := min 1 (Real.sqrt (modelPhaseCurvatureLower σ)/2)
  have hsqrt := Real.sqrt_pos.mpr (modelPhaseCurvatureLower_pos hσ)
  have hγ : 0 < γ := lt_min (by norm_num) (by positivity)
  have hγ₁ : γ ≤ 1 := min_le_left _ _
  have hγs : γ < Real.sqrt (modelPhaseCurvatureLower σ) :=
    (min_le_right _ _).trans_lt (by linarith)
  refine ⟨max (bufferedInteriorStationaryConstant σ/γ) 1,le_max_right _ _,?_⟩
  intro l r η d hl hr hη hd F δ v T hδ hF hv hT hleft hright
  have hF₁ := approximateModelPhase_mono hF bufferedLocalStationaryOrder_pos le_rfl
  have hd₁ : d ≤ 1 := by linarith
  have hH : 0 < γ*d := mul_pos hγ hd
  have hH₁ : γ*d ≤ 1 := (mul_le_mul hγ₁ hd₁ hd.le (by norm_num)).trans_eq (one_mul 1)
  have hsmall := mul_lt_mul_of_pos_right hγs hd
  have hb := bufferedNormalizedMode_interior_window_remainder hσ hδ hF hv hη hl hr hd
    hleft hright hH hH₁ hsmall hT
  have hχ : modelPhaseBufferedCutoff l r η (modelPhaseInverseSlope F v) = 1 :=
    modelPhaseBufferedCutoff_one hη (by linarith) (by linarith)
  have he :
      modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T (T*v)-
        (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ)*
          ((modelPhaseStationaryAmplitude F v : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))) =
      (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ)*
        modelPhaseMorseRemainder (modelPhaseBufferedCutoff l r η) F T v := by
    rw [modelPhaseNormalizedMode_morse (modelPhaseBufferedCutoff_tsupport_model hη hl hr)
      hσ hδ hF₁ hv T]
    unfold modelPhaseMorseRemainder
    rw [modelPhaseMorseAmplitude_zero hσ hδ hF₁ hv,hχ,one_mul]
    ring
  rw [he,norm_mul,Circle.norm_coe,one_mul] at hb
  apply hb.trans
  calc
    bufferedInteriorStationaryConstant σ/(T*(γ*d)) =
        (bufferedInteriorStationaryConstant σ/γ)/(T*d) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) (mul_pos hT hd).le

theorem modelPhaseBufferedFourierMode_interior_uniform
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η d : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → 0 < d →
      ∀ (F : ℝ → ℝ) (δ T N q : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        0 < T → 0 < N → q*N/T ∈ modelPhaseSlopeRange F →
        l+2*η+d ≤ modelPhaseInverseSlope F (q*N/T) →
        modelPhaseInverseSlope F (q*N/T)+d ≤ r-2*η →
        ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
          modelPhaseStationaryMainTerm F T N q‖ ≤ C*N/(T*d) := by
  obtain ⟨C,hC,hR⟩ := modelPhaseBufferedMorseRemainder_interior_uniform hσ
  refine ⟨C,hC,?_⟩
  intro l r η d hl hr hη hd F δ T N q hδ hF hT hN hv hleft hright
  have hχ : modelPhaseBufferedCutoff l r η (modelPhaseInverseSlope F (q*N/T)) = 1 :=
    modelPhaseBufferedCutoff_one hη (by linarith) (by linarith)
  have he := norm_modelPhaseFourierMode_sub_main
    (modelPhaseBufferedCutoff_tsupport_model hη hl hr) hσ hδ
    (approximateModelPhase_mono hF bufferedLocalStationaryOrder_pos le_rfl) hT hN hv
  rw [hχ,Complex.ofReal_one,one_mul] at he
  rw [he]
  exact (mul_le_mul_of_nonneg_left
    (hR l r η d hl hr hη hd F δ (q*N/T) T hδ hF hv hT hleft hright) hN.le).trans_eq (by ring)

end TaoTrudgianYang2025
