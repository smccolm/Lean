import TaoTrudgianYang2025.BetaMorseWeightJets
import TaoTrudgianYang2025.BetaBufferedCutoff
import TaoTrudgianYang2025.BetaQuadraticLocalRemainder

/-!
# Central Morse windows inside the original cutoff plateau

The window and local derivative budgets are derived from the original
critical point's distance to the cutoff edges. No global cutoff jet
bound, and hence no negative power of its transition width, is used.
-/

noncomputable section

open Set Expdb Filter MeasureTheory
open scoped ContDiff Topology FourierTransform

namespace TaoTrudgianYang2025

theorem modelPhaseMorseWindow_mem_and_inverse
    {F : ℝ → ℝ} {σ δ v d H z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hd : 0 < d)
    (hl : 1 < modelPhaseInverseSlope F v-d)
    (hr : modelPhaseInverseSlope F v+d < 2)
    (hH : H < Real.sqrt (modelPhaseCurvatureLower σ)*d)
    (hz : z ∈ Icc (-H) H) :
    z ∈ modelPhaseMorseRange F v ∧
      |modelPhaseMorseInverse F v z-modelPhaseInverseSlope F v| < d := by
  let u₀ := modelPhaseInverseSlope F v
  have hu₀ : u₀ ∈ Ioo (1 : ℝ) 2 := modelPhaseInverseSlope_mem hv
  have ha : u₀-d ∈ Ioo (1 : ℝ) 2 := ⟨hl,by dsimp [u₀]; linarith⟩
  have hb : u₀+d ∈ Ioo (1 : ℝ) 2 := ⟨by dsimp [u₀]; linarith,hr⟩
  have hs : Icc (u₀-d) (u₀+d) ⊆ Ioo (1 : ℝ) 2 := by
    intro u hu
    exact ⟨ha.1.trans_le hu.1,hu.2.trans_lt hb.2⟩
  have hm := modelPhaseMorseCoordinate_strictMonoOn hσ hδ hF hv
  have hwa : modelPhaseMorseCoordinate F v (u₀-d) < 0 := by
    simpa only [u₀,modelPhaseMorseCoordinate_at_inverse] using
      hm ha hu₀ (show u₀-d < u₀ by linarith)
  have hwb : 0 < modelPhaseMorseCoordinate F v (u₀+d) := by
    simpa only [u₀,modelPhaseMorseCoordinate_at_inverse] using
      hm hu₀ hb (show u₀ < u₀+d by linarith)
  have hba := (modelPhaseMorseCoordinate_bounds hσ hδ hF hv ha).1
  have hbb := (modelPhaseMorseCoordinate_bounds hσ hδ hF hv hb).1
  change Real.sqrt (modelPhaseCurvatureLower σ)*|u₀-d-u₀| ≤ _ at hba
  change Real.sqrt (modelPhaseCurvatureLower σ)*|u₀+d-u₀| ≤ _ at hbb
  rw [show u₀-d-u₀ = -d by ring,abs_neg,abs_of_pos hd,abs_of_neg hwa] at hba
  rw [show u₀+d-u₀ = d by ring,abs_of_pos hd,abs_of_pos hwb] at hbb
  have hc : ContinuousOn (modelPhaseMorseCoordinate F v) (Icc (u₀-d) (u₀+d)) :=
    fun u hu => (modelPhaseMorseCoordinate_contDiffAt hσ hδ hF hv (hs hu)).continuousAt.continuousWithinAt
  have hz' : z ∈ modelPhaseMorseRange F v := by
    obtain ⟨u,hu,he⟩ := intermediate_value_Icc (show u₀-d ≤ u₀+d by linarith) hc
      (show z ∈ Icc (modelPhaseMorseCoordinate F v (u₀-d))
        (modelPhaseMorseCoordinate F v (u₀+d)) by constructor <;> linarith [hz.1,hz.2])
    exact ⟨u,hs hu,he⟩
  refine ⟨hz',?_⟩
  have hb' := (modelPhaseMorseCoordinate_bounds hσ hδ hF hv
    (modelPhaseMorseInverse_mem hz')).1
  rw [modelPhaseMorseCoordinate_inverse hz'] at hb'
  have hcpos := Real.sqrt_pos.mpr (modelPhaseCurvatureLower_pos hσ)
  have habs : |z| ≤ H := abs_le.mpr hz
  nlinarith

theorem iteratedDeriv_bufferedMorseWeight_of_flat
    {F : ℝ → ℝ} {σ δ v z l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (hη : 0 < η)
    (hl : l+2*η < modelPhaseMorseInverse F v z)
    (hr : modelPhaseMorseInverse F v z < r-2*η) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseWeight (modelPhaseBufferedCutoff l r η) F v) z =
      iteratedDeriv (n+1) (modelPhaseMorseInverse F v) z := by
  rw [iteratedDeriv_modelPhaseMorseWeight_eq hσ hδ hF hv hz,iteratedDeriv_succ']
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hi := (modelPhaseMorseInverse_contDiffAt hσ hδ hF hv hz).continuousAt
  have hn : ∀ᶠ x in 𝓝 z, modelPhaseMorseInverse F v x ∈ Ioo (l+2*η) (r-2*η) :=
    hi (isOpen_Ioo.mem_nhds ⟨hl,hr⟩)
  filter_upwards [hn] with x hx
  simp only [modelPhaseMorseAmplitude,modelPhaseBufferedCutoff_one hη hx.1.le hx.2.le,one_mul]

theorem bufferedMorseWeight_local_jet_bound
    {F : ℝ → ℝ} {σ δ v l r η d H z : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hd : 0 < d)
    (hleft : l+2*η+d ≤ modelPhaseInverseSlope F v)
    (hright : modelPhaseInverseSlope F v+d ≤ r-2*η)
    (hH : H < Real.sqrt (modelPhaseCurvatureLower σ)*d)
    (hz : z ∈ Icc (-H) H) (n : ℕ)
    (hP : morseInverseDerivativeOrder (n+1) ≤ P) :
    |iteratedDeriv n (modelPhaseMorseWeight (modelPhaseBufferedCutoff l r η) F v) z| ≤
      morseInverseDerivativeBound σ (n+1) := by
  have hF₁ := approximateModelPhase_mono hF ((morseInverseDerivativeOrder_pos (n+1)).trans hP) le_rfl
  obtain ⟨hz',hi⟩ := modelPhaseMorseWindow_mem_and_inverse hσ hδ hF₁ hv hd
    (show 1 < modelPhaseInverseSlope F v-d by linarith)
    (show modelPhaseInverseSlope F v+d < 2 by linarith) hH hz
  have hi' := abs_lt.mp hi
  rw [iteratedDeriv_bufferedMorseWeight_of_flat hσ hδ hF₁ hv hz' hη
    (show l+2*η < modelPhaseMorseInverse F v z by linarith [hi'.1])
    (show modelPhaseMorseInverse F v z < r-2*η by linarith [hi'.2]) n]
  exact modelPhaseMorseInverse_iteratedDeriv_bound hσ hδ hF hv hz' (n+1) hP

def bufferedLocalStationaryOrder : ℕ :=
  morseInverseDerivativeOrder 1+morseInverseDerivativeOrder 3+morseInverseDerivativeOrder 4

theorem bufferedLocalStationaryOrder_pos : 1 ≤ bufferedLocalStationaryOrder := by
  have h := morseInverseDerivativeOrder_pos 1
  unfold bufferedLocalStationaryOrder
  omega

theorem bufferedMorseWeight_local_window_remainder
    {F : ℝ → ℝ} {σ δ v l r η d H T : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hd : 0 < d)
    (hleft : l+2*η+d ≤ modelPhaseInverseSlope F v)
    (hright : modelPhaseInverseSlope F v+d ≤ r-2*η)
    (hH : 0 < H) (hsmall : H < Real.sqrt (modelPhaseCurvatureLower σ)*d)
    (hT : 0 < T) :
    ‖(∫ z in (-H)..H,
      (modelPhaseMorseWeight (modelPhaseBufferedCutoff l r η) F v z : ℂ)*
        betaQuadraticKernel T z)-
      (modelPhaseStationaryAmplitude F v : ℂ)*
        ((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
      quadraticRemainderConstant H (morseInverseDerivativeBound σ 1)
        (morseInverseDerivativeBound σ 3) (morseInverseDerivativeBound σ 4)/T := by
  have hF₁ := approximateModelPhase_mono hF bufferedLocalStationaryOrder_pos le_rfl
  have hs := modelPhaseBufferedCutoff_tsupport_model hη hl hr
  have hW := modelPhaseMorseWeight_contDiff (modelPhaseBufferedCutoff_contDiff l r η)
    hs hσ hδ hF₁ hv
  have hzero : modelPhaseMorseWeight (modelPhaseBufferedCutoff l r η) F v 0 =
      modelPhaseStationaryAmplitude F v := by
    rw [modelPhaseMorseWeight_eq (zero_mem_modelPhaseMorseRange hv),
      modelPhaseMorseAmplitude_zero hσ hδ hF₁ hv,
      modelPhaseBufferedCutoff_one hη (by linarith) (by linarith),one_mul]
  have hb (n : ℕ) (hn : morseInverseDerivativeOrder (n+1) ≤ bufferedLocalStationaryOrder) :
      ∀ z ∈ Icc (-H) H,
        |iteratedDeriv n (modelPhaseMorseWeight (modelPhaseBufferedCutoff l r η) F v) z| ≤
          morseInverseDerivativeBound σ (n+1) :=
    fun z hz => bufferedMorseWeight_local_jet_bound hσ hδ hF hv hη hl hr hd
      hleft hright hsmall hz n hn
  have h₀ := hb 0 (by simp only [Nat.reduceAdd,bufferedLocalStationaryOrder]; omega) 0
    (show (0 : ℝ) ∈ Icc (-H) H by constructor <;> linarith)
  have h₂ := hb 2 (by simp only [Nat.reduceAdd,bufferedLocalStationaryOrder]; omega)
  have h₃ := hb 3 (by simp only [Nat.reduceAdd,bufferedLocalStationaryOrder]; omega)
  have h := norm_quadratic_window_remainder_le_local hW hT hH h₀ h₂ h₃
  simpa only [hzero] using h

theorem bufferedMorseWeight_local_window_remainder_inverse
    {F : ℝ → ℝ} {σ δ v l r η d H T : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hd : 0 < d)
    (hleft : l+2*η+d ≤ modelPhaseInverseSlope F v)
    (hright : modelPhaseInverseSlope F v+d ≤ r-2*η)
    (hH : 0 < H) (hH₁ : H ≤ 1)
    (hsmall : H < Real.sqrt (modelPhaseCurvatureLower σ)*d)
    (hT : 0 < T) :
    ‖(∫ z in (-H)..H,
      (modelPhaseMorseWeight (modelPhaseBufferedCutoff l r η) F v z : ℂ)*
        betaQuadraticKernel T z)-
      (modelPhaseStationaryAmplitude F v : ℂ)*
        ((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
      (4*morseInverseDerivativeBound σ 1/Real.pi+
        (4*morseInverseDerivativeBound σ 3+2*morseInverseDerivativeBound σ 4)/(2*Real.pi))/(T*H) := by
  have h := bufferedMorseWeight_local_window_remainder hσ hδ hF hv hη hl hr hd
    hleft hright hH hsmall hT
  have hc := quadraticRemainderConstant_le_inverse_window (M₀ := morseInverseDerivativeBound σ 1) hH hH₁
    (morseInverseDerivativeBound_nonneg hσ 3) (morseInverseDerivativeBound_nonneg hσ 4)
  apply h.trans
  convert div_le_div_of_nonneg_right hc hT.le using 1
  ring

end TaoTrudgianYang2025
