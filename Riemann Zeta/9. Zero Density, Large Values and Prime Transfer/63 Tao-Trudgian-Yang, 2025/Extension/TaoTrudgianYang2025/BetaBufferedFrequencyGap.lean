import TaoTrudgianYang2025.BetaBufferedNonstationary
import TaoTrudgianYang2025.BetaInverseStability

/-!
# Derived model-slope envelopes and physical frequency gaps

The original approximate-model hypothesis supplies both frequency cutoffs.
The final inverse-distance bound is independent of N, eta and the endpoints;
moving boundary strips and summation of the infinite tail remain separate.
-/

noncomputable section

open Set Expdb

namespace TaoTrudgianYang2025

theorem approximateModelPhase_firstDeriv_bounds
    {F : ℝ → ℝ} {σ δ : ℝ} {P : ℕ} (hσ : 0 < σ)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    (2 : ℝ)^(-σ)-δ ≤ deriv F u ∧ deriv F u ≤ 1+δ := by
  have he := (abs_le.mp (approximateModelPhase_firstDeriv_error hF hu))
  have hlow : (2 : ℝ)^(-σ) ≤ u^(-σ) :=
    Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hu.1) hu.2.le (by linarith)
  have hhigh : u^(-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu.1.le (by linarith)
  constructor <;> linarith [he.1,he.2]

theorem norm_modelPhaseBufferedFourierMode_of_envelope_gap
    {F : ℝ → ℝ} {σ δ T N q l r η lam : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hlam : 0 < lam)
    (hgap : q*N ≤ T*((2 : ℝ)^(-σ)-δ)-lam ∨ T*(1+δ)+lam ≤ q*N) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4*N/(lam*Real.pi) := by
  apply norm_modelPhaseBufferedFourierMode_nonstationary hσ hδ hF hT hN hη hl hr hlam
  rcases hgap with hp | hn
  · left
    intro u hu
    have hb := (approximateModelPhase_firstDeriv_bounds hσ hF hu).1
    nlinarith
  · right
    intro u hu
    have hb := (approximateModelPhase_firstDeriv_bounds hσ hF hu).2
    nlinarith

theorem norm_modelPhaseBufferedFourierMode_of_frequency_gap
    {F : ℝ → ℝ} {σ δ T N q l r η d : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hd : 0 < d)
    (hgap : q ≤ (T/N)*((2 : ℝ)^(-σ)-δ)-d ∨ (T/N)*(1+δ)+d ≤ q) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4/(d*Real.pi) := by
  have hg : q*N ≤ T*((2 : ℝ)^(-σ)-δ)-N*d ∨ T*(1+δ)+N*d ≤ q*N := by
    have he (c : ℝ) : (T/N)*c*N = T*c := by field_simp
    rcases hgap with hp | hn
    · left
      have h := mul_le_mul_of_nonneg_right hp hN.le
      rw [sub_mul,he] at h
      nlinarith
    · right
      have h := mul_le_mul_of_nonneg_right hn hN.le
      rw [add_mul,he] at h
      nlinarith
  have h := norm_modelPhaseBufferedFourierMode_of_envelope_gap hσ hδ hF hT hN hη hl hr
    (mul_pos hN hd) hg
  apply h.trans_eq
  field_simp

end TaoTrudgianYang2025
