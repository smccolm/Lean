import TaoTrudgianYang2025.BetaClosedSlope
import TaoTrudgianYang2025.BetaBufferedNonstationary
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Nonstationary blocks relative to the actual endpoint slopes

Unlike the approximate model envelope, these cutoffs exactly delimit the
stationary image. All outer modes except the nearest integer on each side
have the original width-independent reciprocal-distance bound.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem norm_modelPhaseBufferedFourierMode_of_endpoint_gap
    {F : ℝ → ℝ} {σ δ T N q l r η d : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hd : 0 < d)
    (hgap : q ≤ (T/N)*modelPhaseClosedSlope F 2-d ∨
      (T/N)*modelPhaseClosedSlope F 1+d ≤ q) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4/(d*Real.pi) := by
  have hg : (∀ u ∈ Ioo (1 : ℝ) 2, N*d ≤ T*deriv F u-q*N) ∨
      (∀ u ∈ Ioo (1 : ℝ) 2, T*deriv F u-q*N ≤ -(N*d)) := by
    have he (c : ℝ) : (T/N)*c*N = T*c := by field_simp
    rcases hgap with hp | hn
    · left
      intro u hu
      have hb := mul_le_mul_of_nonneg_left
        (modelPhaseClosedSlope_deriv_bounds hσ hδ hF hu).1 hT.le
      have h := mul_le_mul_of_nonneg_right hp hN.le
      rw [sub_mul,he] at h
      nlinarith
    · right
      intro u hu
      have hb := mul_le_mul_of_nonneg_left
        (modelPhaseClosedSlope_deriv_bounds hσ hδ hF hu).2 hT.le
      have h := mul_le_mul_of_nonneg_right hn hN.le
      rw [add_mul,he] at h
      nlinarith
  have h := norm_modelPhaseBufferedFourierMode_nonstationary hσ hδ hF hT hN hη hl hr
    (mul_pos hN hd) hg
  apply h.trans_eq
  field_simp

theorem sum_norm_bufferedModes_endpoint_right_le_harmonic
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2)
    (Q : ℤ) (hQ : (T/N)*modelPhaseClosedSlope F 1 ≤ (Q : ℝ)) (L : ℕ) :
    (∑ n ∈ Finset.range L,
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((Q : ℝ)+((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range L, (4/Real.pi)*(((n+1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := norm_modelPhaseBufferedFourierMode_of_endpoint_gap hσ hδ hF
        hT hN hη hl hr (by positivity : 0 < ((n+1 : ℕ) : ℝ))
        (Or.inr (add_le_add hQ le_rfl))
      convert h using 1
      ring
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]

theorem sum_norm_bufferedModes_endpoint_left_le_harmonic
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2)
    (Q : ℤ) (hQ : (Q : ℝ) ≤ (T/N)*modelPhaseClosedSlope F 2) (L : ℕ) :
    (∑ n ∈ Finset.range L,
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((Q : ℝ)-((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range L, (4/Real.pi)*(((n+1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := norm_modelPhaseBufferedFourierMode_of_endpoint_gap hσ hδ hF
        hT hN hη hl hr (by positivity : 0 < ((n+1 : ℕ) : ℝ))
        (Or.inl (sub_le_sub_right hQ _))
      convert h using 1
      ring
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]

theorem norm_bufferedModes_endpoint_blocks_le_log
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2)
    (Lminus Lplus : ℕ) :
    ‖(∑ n ∈ Finset.range Lminus,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((⌊(T/N)*modelPhaseClosedSlope F 2⌋ : ℤ)-((n+1 : ℕ) : ℝ)))+
      (∑ n ∈ Finset.range Lplus,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((⌈(T/N)*modelPhaseClosedSlope F 1⌉ : ℤ)+((n+1 : ℕ) : ℝ)))‖ ≤
      (4/Real.pi)*(2+Real.log (Lminus : ℝ)+Real.log (Lplus : ℝ)) := by
  have hm := sum_norm_bufferedModes_endpoint_left_le_harmonic hσ hδ hF hT hN hη hl hr
    ⌊(T/N)*modelPhaseClosedSlope F 2⌋ (Int.floor_le _) Lminus
  have hp := sum_norm_bufferedModes_endpoint_right_le_harmonic hσ hδ hF hT hN hη hl hr
    ⌈(T/N)*modelPhaseClosedSlope F 1⌉ (Int.le_ceil _) Lplus
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

