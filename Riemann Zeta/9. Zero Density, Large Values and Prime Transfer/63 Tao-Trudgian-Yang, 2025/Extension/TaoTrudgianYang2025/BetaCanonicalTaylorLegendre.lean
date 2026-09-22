import TaoTrudgianYang2025.BetaLegendreTaylorExtension
import TaoTrudgianYang2025.BetaPhaseNormalization

/-!
# Canonical model phases from the genuine moving Taylor extension

The tolerance is chosen before the source phase, anchor and shrinking
buffer width. Exact dual values hold on the actual retained slope
plateau; no fixed strict-interior reference-image condition is imposed.
-/

noncomputable section

open Set Expdb
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

def canonicalTaylorLegendrePhase (F : ℝ → ℝ) (σ A : ℝ) (Q : ℕ) (w h u : ℝ) : ℝ :=
  referenceModelPrimitive σ⁻¹ u+
    rescaledPhaseCorrection (modelPhaseTaylorExtension F σ (Q+1) w h) σ⁻¹ A u

theorem canonicalTaylorLegendrePhase_agrees
    {F : ℝ → ℝ} {σ A w v h : ℝ} (Q : ℕ)
    (hA : 0 < A) (hw : 0 < w) (hv : 0 < v) (hh : 0 < h)
    (hplateau : v ∈ Icc (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    canonicalTaylorLegendrePhase F σ A Q w h (v/A) =
      A^(σ⁻¹-1)*(modelPhaseLegendreDual F v-modelPhaseLegendreDual F w)+
        referenceModelPrimitive σ⁻¹ (w/A) := by
  have he := referenceModelPrimitive_scaling_difference σ⁻¹ hA
    (div_pos hv hA) (div_pos hw hA)
  rw [mul_div_cancel₀ _ hA.ne',mul_div_cancel₀ _ hA.ne'] at he
  unfold canonicalTaylorLegendrePhase rescaledPhaseCorrection
  rw [mul_div_cancel₀ _ hA.ne']
  change referenceModelPrimitive σ⁻¹ (v/A)+A^(σ⁻¹-1)*
    taylorPastedExtension (anchoredLegendreError F σ w) (Q+1) _ _ h v = _
  rw [taylorPastedExtension_agrees _ (Q+1) hh hplateau]
  unfold anchoredLegendreError
  nlinarith only [he]

theorem canonicalTaylorLegendrePhase_uniformity
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2)
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 ∧
      ∀ F : ℝ → ℝ,
        IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder (Q+2)) δ →
        ∀ w ∈ modelPhaseSlopeRange F, ∀ h : ℝ,
          0 < h → h ≤ 1 →
          modelPhaseClosedSlope F 2+4*h < modelPhaseClosedSlope F 1 →
          IsApproximateModelPhaseFunction (canonicalTaylorLegendrePhase F σ A Q w h)
            σ⁻¹ Q ε := by
  obtain ⟨C,hC,hext⟩ := modelPhaseTaylorExtension_uniformity hσ (Q+1)
  let B := phaseRescalingBudget σ⁻¹ A (Q+1)
  have hB : 0 < B := phaseRescalingBudget_pos _ _ _
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  let δ := min (min (modelPhaseCurvatureLower σ) 1)
    (min (min ((2 : ℝ)^(-σ)/2) 1) (ε/(B*C)))
  have hd : 0 < δ := lt_min
    (lt_min (modelPhaseCurvatureLower_pos hσ) zero_lt_one)
    (lt_min (lt_min (by positivity) zero_lt_one) (div_pos hε (mul_pos hB hCpos)))
  have hsmall : δ ≤ min (modelPhaseCurvatureLower σ) 1 := min_le_left _ _
  have hpos : δ ≤ min ((2 : ℝ)^(-σ)/2) 1 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hbudget : δ ≤ ε/(B*C) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hd,hsmall,hpos,?_⟩
  intro F hF w hw h hh hh₁ hgap
  obtain ⟨hsmooth,_,hjets⟩ := hext F δ hsmall hpos hF w hw h hh hh₁ hgap
  apply referencePlusCorrection_approximate
    (rescaledPhaseCorrection_contDiff hsmooth σ⁻¹ A) σ⁻¹ Q
  intro u hu n hn
  have hv : A*u ∈ Icc (0 : ℝ) 4 := by
    constructor
    · exact mul_nonneg hA.le (zero_le_one.trans hu.1)
    · nlinarith [hu.1,hu.2]
  have hn' : n+1 ≤ Q+1 := Nat.succ_le_succ hn
  have hcoeff : |A^(σ⁻¹-1)| * |A|^(n+1) ≤ B := by
    have hsum := Finset.single_le_sum (s := Finset.range (Q+1+1))
      (fun j _ => mul_nonneg (abs_nonneg (A^(σ⁻¹-1))) (pow_nonneg (abs_nonneg A) j))
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn'))
    dsimp [B,phaseRescalingBudget]
    linarith
  rw [rescaledPhaseCorrection_iteratedDeriv hsmooth,abs_mul,abs_mul,abs_pow]
  have hbound := mul_le_mul hcoeff (hjets (A*u) hv (n+1) hn')
    (abs_nonneg _) hB.le
  have hbudget' : B*C*δ ≤ ε := by
    have hmul := (le_div_iff₀ (mul_pos hB hCpos)).mp hbudget
    nlinarith
  exact hbound.trans (by nlinarith)

end TaoTrudgianYang2025
