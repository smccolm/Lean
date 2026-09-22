import TaoTrudgianYang2025.BetaBufferedLocalNonstationary
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Nonstationary bounds outside the actual cutoff-support slopes

Only the support interval [l+eta,r-eta] is used. Stationary points
elsewhere in the original model interval do not obstruct these estimates.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform BigOperators

namespace TaoTrudgianYang2025

theorem modelPhaseBufferedNormalizedMode_eq_interval
    {l r η : ℝ} (hη : 0 < η) (F : ℝ → ℝ) (T q : ℝ) :
    modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T q =
      ∫ u in (l+η)..(r-η), (modelPhaseBufferedCutoff l r η u : ℂ)*(𝐞 (T*F u-q*u) : ℂ) := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro u hu
  have hχ : modelPhaseBufferedCutoff l r η u ≠ 0 := by
    intro hz
    exact hu (by simp only [hz,Complex.ofReal_zero,zero_mul])
  have hh := modelPhaseBufferedCutoff_support_open hη hχ
  exact ⟨hh.1,hh.2.le⟩

theorem norm_modelPhaseBufferedFourierMode_of_support_gap
    {F : ℝ → ℝ} {σ δ T N q l r η d : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hsep : l+2*η ≤ r) (hd : 0 < d)
    (hgap : q ≤ (T/N)*deriv F (r-η)-d ∨
      (T/N)*deriv F (l+η)+d ≤ q) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4/(d*Real.pi) := by
  have hab : l+η ≤ r-η := by linarith
  have ha : l+η ∈ Ioo (1 : ℝ) 2 := ⟨by linarith,by linarith⟩
  have hb : r-η ∈ Ioo (1 : ℝ) 2 := ⟨by linarith,by linarith⟩
  have hm := (approximateModelPhase_deriv_strictAntiOn hσ hδ hF).antitoneOn
  have hg : (∀ u ∈ Icc (l+η) (r-η), N*d ≤ T*deriv F u-q*N) ∨
      (∀ u ∈ Icc (l+η) (r-η), T*deriv F u-q*N ≤ -(N*d)) := by
    have he (c : ℝ) : (T/N)*c*N = T*c := by field_simp
    rcases hgap with hp | hn
    · left
      intro u hu
      have hu' : u ∈ Ioo (1 : ℝ) 2 := ⟨ha.1.trans_le hu.1,hu.2.trans_lt hb.2⟩
      have hs := mul_le_mul_of_nonneg_left (hm hu' hb hu.2) hT.le
      have h := mul_le_mul_of_nonneg_right hp hN.le
      rw [sub_mul,he] at h
      nlinarith
    · right
      intro u hu
      have hu' : u ∈ Ioo (1 : ℝ) 2 := ⟨ha.1.trans_le hu.1,hu.2.trans_lt hb.2⟩
      have hs := mul_le_mul_of_nonneg_left (hm ha hu' hu.1) hT.le
      have h := mul_le_mul_of_nonneg_right hn hN.le
      rw [add_mul,he] at h
      nlinarith
  have h := norm_buffered_subinterval_nonstationary (l := l) (r := r)
    hσ hδ hF hT hη hab ha.1 hb.2 (mul_pos hN hd) hg
  rw [modelPhaseFourierMode_eq_normalized _ _ _ _ hN,norm_smul,
    Real.norm_eq_abs,abs_of_pos hN,modelPhaseBufferedNormalizedMode_eq_interval hη]
  apply (mul_le_mul_of_nonneg_left h hN.le).trans_eq
  field_simp

theorem sum_norm_bufferedModes_support_right_le_harmonic
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hsep : l+2*η ≤ r)
    (Q : ℤ) (hQ : (T/N)*deriv F (l+η) ≤ (Q : ℝ)) (L : ℕ) :
    (∑ n ∈ Finset.range L,
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((Q : ℝ)+((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range L, (4/Real.pi)*(((n+1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := norm_modelPhaseBufferedFourierMode_of_support_gap hσ hδ hF
        hT hN hη hl hr hsep (by positivity : 0 < ((n+1 : ℕ) : ℝ))
        (Or.inr (add_le_add hQ le_rfl))
      convert h using 1
      ring
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]

theorem sum_norm_bufferedModes_support_left_le_harmonic
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hsep : l+2*η ≤ r)
    (Q : ℤ) (hQ : (Q : ℝ) ≤ (T/N)*deriv F (r-η)) (L : ℕ) :
    (∑ n ∈ Finset.range L,
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((Q : ℝ)-((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range L, (4/Real.pi)*(((n+1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := norm_modelPhaseBufferedFourierMode_of_support_gap hσ hδ hF
        hT hN hη hl hr hsep (by positivity : 0 < ((n+1 : ℕ) : ℝ))
        (Or.inl (sub_le_sub_right hQ _))
      convert h using 1
      ring
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]

theorem norm_bufferedModes_support_blocks_le_log
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hsep : l+2*η ≤ r)
    (Lminus Lplus : ℕ) :
    ‖(∑ n ∈ Finset.range Lminus,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((⌊(T/N)*deriv F (r-η)⌋ : ℤ)-((n+1 : ℕ) : ℝ)))+
      (∑ n ∈ Finset.range Lplus,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((⌈(T/N)*deriv F (l+η)⌉ : ℤ)+((n+1 : ℕ) : ℝ)))‖ ≤
      (4/Real.pi)*(2+Real.log (Lminus : ℝ)+Real.log (Lplus : ℝ)) := by
  have hm := sum_norm_bufferedModes_support_left_le_harmonic hσ hδ hF hT hN hη hl hr hsep
    ⌊(T/N)*deriv F (r-η)⌋ (Int.floor_le _) Lminus
  have hp := sum_norm_bufferedModes_support_right_le_harmonic hσ hδ hF hT hN hη hl hr hsep
    ⌈(T/N)*deriv F (l+η)⌉ (Int.le_ceil _) Lplus
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
