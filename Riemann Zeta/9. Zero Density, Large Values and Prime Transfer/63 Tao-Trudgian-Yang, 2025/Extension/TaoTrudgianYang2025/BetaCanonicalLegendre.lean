import TaoTrudgianYang2025.BetaPhaseNormalization

/-!
# Canonical model extensions of retained Legendre windows

For every positive source exponent, a retained compact window of ratio
less than two is placed strictly inside a multiplicative copy of [1,2].
The same fixed cutoff works at every requested order and tolerance.
The source's closed-interval model condition and exact retained values
(up to the permitted additive constant) are both proved.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def canonicalLegendrePhase (χ F : ℝ → ℝ) (σ A w u : ℝ) : ℝ :=
  referenceModelPrimitive σ⁻¹ u +
    rescaledPhaseCorrection (legendreCutoffCorrection χ F σ w) σ⁻¹ A u

theorem canonicalLegendrePhase_agrees {χ F : ℝ → ℝ} {σ A w v : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hv : 0 < v) (hχ : χ v = 1) :
    canonicalLegendrePhase χ F σ A w (v/A) =
      A^(σ⁻¹-1)*(modelPhaseLegendreDual F v-modelPhaseLegendreDual F w) +
        referenceModelPrimitive σ⁻¹ (w/A) := by
  have he := referenceModelPrimitive_scaling_difference σ⁻¹ hA
    (div_pos hv hA) (div_pos hw hA)
  rw [mul_div_cancel₀ _ hA.ne',mul_div_cancel₀ _ hA.ne'] at he
  unfold canonicalLegendrePhase rescaledPhaseCorrection
  rw [mul_div_cancel₀ _ hA.ne',legendreCutoffCorrection_agrees hχ]
  unfold anchoredLegendreError
  nlinarith only [he]

theorem canonicalLegendrePhase_uniformity
    {σ c d w : ℝ} (hσ : 0 < σ)
    (hc : (2 : ℝ)^(-σ) < c) (hcd : c ≤ d) (hd : d < 1)
    (hw : w ∈ Icc c d) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Icc c d)
    (A : ℝ) (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      ∀ F : ℝ → ℝ,
        IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder (Q+1)) δ →
      Icc c d ⊆ modelPhaseSlopeRange F ∧
        IsApproximateModelPhaseFunction (canonicalLegendrePhase χ F σ A w)
          σ⁻¹ Q ε := by
  let C := phaseRescalingBudget σ⁻¹ A (Q+1)
  have hC : 0 < C := phaseRescalingBudget_pos _ _ _
  have hη : 0 < ε/C := div_pos hε hC
  obtain ⟨δ,hδ,hsmall,hall⟩ := legendreCutoffCorrection_uniformity
    hσ hc hcd hd hw hχ hs (Q+1) hη
  refine ⟨δ,hδ,hsmall,?_⟩
  intro F hF
  obtain ⟨hJ,hH,he⟩ := hall F hF
  refine ⟨hJ,referencePlusCorrection_approximate
    (rescaledPhaseCorrection_contDiff hH σ⁻¹ A) σ⁻¹ Q ?_⟩
  intro u _ n hn
  have h := rescaledPhaseCorrection_uniform_bound hH σ⁻¹ A hη.le he u
    (Nat.succ_le_succ hn)
  simpa only [C,mul_div_cancel₀ _ hC.ne'] using h

theorem modelPhaseLegendreDual_canonical_extension
    {σ a b : ℝ} (hσ : 0 < σ)
    (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1)
    (hr : b < 2*a) :
    ∃ A : ℝ, 0 < A ∧ A < a ∧ b < 2*A ∧
      ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        (∀ v ∈ Icc a b, χ v = 1) ∧
        ∀ (Q : ℕ) (ε : ℝ), 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
          ∀ F : ℝ → ℝ,
            IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder (Q+1)) δ →
          Icc a b ⊆ modelPhaseSlopeRange F ∧
          IsApproximateModelPhaseFunction (canonicalLegendrePhase χ F σ A a) σ⁻¹ Q ε ∧
          ∀ v ∈ Icc a b, v/A ∈ Ioo (1 : ℝ) 2 ∧
            canonicalLegendrePhase χ F σ A a (v/A) =
              A^(σ⁻¹-1)*(modelPhaseLegendreDual F v-modelPhaseLegendreDual F a) +
                referenceModelPrimitive σ⁻¹ (a/A) := by
  have ha₀ : 0 < a :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-σ)).trans ha
  let A := (b/2+a)/2
  have hA : 0 < A := by dsimp [A]; linarith
  have hAa : A < a := by dsimp [A]; linarith
  have hbA : b < 2*A := by dsimp [A]; linarith
  let c := ((2 : ℝ)^(-σ)+a)/2
  let d := (b+1)/2
  have hc : (2 : ℝ)^(-σ) < c := by dsimp [c]; linarith
  have hca : c < a := by dsimp [c]; linarith
  have hbd : b < d := by dsimp [d]; linarith
  have hd : d < 1 := by dsimp [d]; linarith
  have hcd : c ≤ d := by linarith
  obtain ⟨χ,hχ,hplateau,hs,hcompact,_⟩ :=
    exists_smooth_interval_cutoff hca hab hbd
  have hs' : tsupport χ ⊆ Icc c d := fun _ hx => ⟨(hs hx).1.le,(hs hx).2.le⟩
  have haI : a ∈ Icc c d := ⟨hca.le,hab.trans hbd.le⟩
  refine ⟨A,hA,hAa,hbA,χ,hχ,hcompact,hplateau,?_⟩
  intro Q ε hε
  obtain ⟨δ,hδ,hsmall,hall⟩ :=
    canonicalLegendrePhase_uniformity hσ hc hcd hd haI hχ hs' A Q hε
  refine ⟨δ,hδ,hsmall,?_⟩
  intro F hF
  obtain ⟨hJ,hmodel⟩ := hall F hF
  have hsub : Icc a b ⊆ Icc c d := fun _ hx => ⟨hca.le.trans hx.1,hx.2.trans hbd.le⟩
  refine ⟨fun _ hv => hJ (hsub hv),hmodel,?_⟩
  intro v hv
  refine ⟨⟨(one_lt_div hA).mpr (hAa.trans_le hv.1),
    (div_lt_iff₀ hA).mpr (hv.2.trans_lt hbA)⟩,?_⟩
  exact canonicalLegendrePhase_agrees hA ha₀ (ha₀.trans_le hv.1) (hplateau v hv)

end TaoTrudgianYang2025
