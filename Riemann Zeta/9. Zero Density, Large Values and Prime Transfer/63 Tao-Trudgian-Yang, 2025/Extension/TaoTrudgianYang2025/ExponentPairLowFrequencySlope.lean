import TaoTrudgianYang2025.BetaClosedSlope
import TaoTrudgianYang2025.BetaDiscreteCurvature

/-!
# Source-derived slope gaps for the small-parameter A-process branch

Positive first derivatives and physical increment bounds are derived
from the actual closed-interval model. No exterior phase values enter.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem modelPhaseClosedSlope_positive_bounds {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ phaseInterval) :
    (2 : ℝ)^(-σ)/2 ≤ modelPhaseClosedSlope F u ∧ modelPhaseClosedSlope F u ≤ 2 := by
  have he := modelPhaseClosedSlope_model_error hF hu
  rw [abs_le] at he
  have hlo := Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hu.1) hu.2
    (neg_nonpos.mpr hσ.le)
  have hhi := Real.rpow_le_one_of_one_le_of_nonpos hu.1 (neg_nonpos.mpr hσ.le)
  have hd₀ := hδ.trans (min_le_left _ _)
  have hd₁ := hδ.trans (min_le_right _ _)
  constructor <;> linarith

theorem betaModelSample_firstDifference_bounds
    {σ δ T N A : ℝ} {F : ℝ → ℝ} {P L : ℕ}
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N)
    (hδ : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hstart : N < A) (hend : A+(L : ℝ)+1 < 2*N)
    (n : ℕ) (hn : n ≤ L) :
    -4*Real.pi*T/N ≤ betaModelSample F T N A (n+1)-betaModelSample F T N A n ∧
      betaModelSample F T N A (n+1)-betaModelSample F T N A n ≤
        -Real.pi*(2 : ℝ)^(-σ)*T/N := by
  have hinside (x : ℝ) (hx : x ∈ Icc (n : ℝ) (n+1)) :
      (A+x)/N ∈ Ioo (1 : ℝ) 2 := by
    have hn' : (n : ℝ) ≤ L := by exact_mod_cast hn
    constructor
    · apply (lt_div_iff₀ hN).mpr
      linarith [hx.1,(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · apply (div_lt_iff₀ hN).mpr
      linarith [hx.2]
  obtain ⟨x,hx,he⟩ := exists_hasDerivAt_eq_slope
    (betaModelSample F T N A)
    (fun y => (-2*Real.pi*T/N)*deriv F ((A+y)/N))
    (show (n : ℝ) < n+1 by linarith)
    (fun y hy => (betaModelSample_hasDerivAt hF.1 (hinside y hy)).continuousAt.continuousWithinAt)
    (fun y hy => betaModelSample_hasDerivAt hF.1 (hinside y ⟨hy.1.le,hy.2.le⟩))
  rw [show (n : ℝ)+1-n = 1 by ring,div_one] at he
  have hxI := hinside x ⟨hx.1.le,hx.2.le⟩
  have hb := modelPhaseClosedSlope_positive_bounds hσ hδ hF ⟨hxI.1.le,hxI.2.le⟩
  rw [modelPhaseClosedSlope_eq_deriv hxI] at hb
  have hf : 0 ≤ 2*Real.pi*T/N := by positivity
  have hlo := mul_le_mul_of_nonneg_left hb.1 hf
  have hhi := mul_le_mul_of_nonneg_left hb.2 hf
  ring_nf at he hlo hhi ⊢
  constructor <;> linarith

end TaoTrudgianYang2025
