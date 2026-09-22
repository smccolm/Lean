import TaoTrudgianYang2025.BetaBufferedFrequencyGap
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic sums of the actual nonstationary Fourier modes

Integer blocks outside the proved physical slope envelope have harmonic
rather than linear cost. The original cutoff width does not enter.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sum_norm_bufferedModes_right_le_harmonic
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2)
    (Q : ℤ) (hQ : (T/N)*(1+δ) ≤ (Q : ℝ)) (L : ℕ) :
    (∑ n ∈ Finset.range L,
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((Q : ℝ)+((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range L, (4/Real.pi)*(((n+1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := norm_modelPhaseBufferedFourierMode_of_frequency_gap hσ hδ hF
        hT hN hη hl hr (by positivity : 0 < ((n+1 : ℕ) : ℝ))
        (Or.inr (add_le_add hQ le_rfl))
      convert h using 1
      ring
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]

theorem sum_norm_bufferedModes_left_le_harmonic
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2)
    (Q : ℤ) (hQ : (Q : ℝ) ≤ (T/N)*((2 : ℝ)^(-σ)-δ)) (L : ℕ) :
    (∑ n ∈ Finset.range L,
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((Q : ℝ)-((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range L, (4/Real.pi)*(((n+1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := norm_modelPhaseBufferedFourierMode_of_frequency_gap hσ hδ hF
        hT hN hη hl hr (by positivity : 0 < ((n+1 : ℕ) : ℝ))
        (Or.inl (sub_le_sub_right hQ _))
      convert h using 1
      ring
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]

theorem norm_bufferedModes_exterior_blocks_le_log
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2)
    (Lminus Lplus : ℕ) :
    ‖(∑ n ∈ Finset.range Lminus,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((⌊(T/N)*((2 : ℝ)^(-σ)-δ)⌋ : ℤ)-((n+1 : ℕ) : ℝ)))+
      (∑ n ∈ Finset.range Lplus,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((⌈(T/N)*(1+δ)⌉ : ℤ)+((n+1 : ℕ) : ℝ)))‖ ≤
      (4/Real.pi)*(2+Real.log (Lminus : ℝ)+Real.log (Lplus : ℝ)) := by
  have hm := sum_norm_bufferedModes_left_le_harmonic hσ hδ hF hT hN hη hl hr
    ⌊(T/N)*((2 : ℝ)^(-σ)-δ)⌋ (Int.floor_le _) Lminus
  have hp := sum_norm_bufferedModes_right_le_harmonic hσ hδ hF hT hN hη hl hr
    ⌈(T/N)*(1+δ)⌉ (Int.le_ceil _) Lplus
  calc
    _ ≤ (4/Real.pi)*(harmonic Lminus : ℝ)+(4/Real.pi)*(harmonic Lplus : ℝ) :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_sum_le _ _).trans hm) ((norm_sum_le _ _).trans hp))
    _ ≤ (4/Real.pi)*(1+Real.log (Lminus : ℝ))+
        (4/Real.pi)*(1+Real.log (Lplus : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log Lminus) (by positivity))
        (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log Lplus) (by positivity))
    _ = _ := by ring

end TaoTrudgianYang2025
