import TaoTrudgianYang2025.PhaseWeightedCurvature
import TaoTrudgianYang2025.BetaBufferedNonstationary
import TaoTrudgianYang2025.BetaStationaryPoint

/-!
# Width-independent curvature bounds for the original buffered modes

All real frequencies are covered, including moving stationary endpoints.
The cutoff has total variation at most two, independent of its width.
The original model supplies curvature before any physical parameters are chosen.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem norm_modelPhaseBufferedNormalizedMode_curvature
    {F : ℝ → ℝ} {σ δ T q l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) :
    ‖modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T q‖ ≤
      4*(2/Real.pi+2)/Real.sqrt (T*modelPhaseCurvatureLower σ) := by
  by_cases hab : l+η ≤ r-η
  · let φ : ℝ → ℝ := modelPhaseFrequencyPhase F T 1 q
    have hφ : ∀ u ∈ Ioo (1 : ℝ) 2, ContDiffAt ℝ 2 φ u := by
      intro u hu
      have hc := (approximateModelPhase_contDiffAt hF hu).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      have he : φ = fun u => T*F u-q*u := by
        funext v
        simp only [φ,modelPhaseFrequencyPhase,div_one]
      rw [he]
      exact (contDiffAt_const.mul hc).sub (contDiffAt_const.mul contDiffAt_id)
    have hcurv : ∀ u ∈ Ioo (1 : ℝ) 2,
        deriv (deriv φ) u ≤ -(T*modelPhaseCurvatureLower σ) := by
      intro u hu
      have hd := modelPhaseFrequencyPhase_secondDeriv (T := T) (N := 1) (r := q)
        hF (by simpa only [div_one] using hu)
      change deriv (deriv (modelPhaseFrequencyPhase F T 1 q)) u ≤ _
      rw [hd]
      norm_num only [one_pow,div_one]
      have h := mul_le_mul_of_nonneg_left
        (approximateModelPhase_curvature_deriv_bounds hσ hδ hF hu).1 hT.le
      linarith
    have hsub : Icc (l+η) (r-η) ⊆ Ioo (1 : ℝ) 2 := by
      intro u hu
      constructor <;> linarith [hu.1,hu.2]
    have h := (intervalC1Bound_modelPhaseBufferedCutoff (l := l) (r := r) hη hab).fourierChar_of_negative_curvature hab
        (mul_pos hT (modelPhaseCurvatureLower_pos hσ)) isOpen_Ioo hsub hφ hcurv
    have hs : Function.support (fun u => (modelPhaseBufferedCutoff l r η u : ℂ)*
        (𝐞 (T*F u-q*u) : ℂ)) ⊆ Ioc (l+η) (r-η) := by
      intro u hu
      have hχ : modelPhaseBufferedCutoff l r η u ≠ 0 := by
        intro hz
        exact hu (by simp only [hz,Complex.ofReal_zero,zero_mul])
      have hh := modelPhaseBufferedCutoff_support_open hη hχ
      exact ⟨hh.1,hh.2.le⟩
    unfold modelPhaseNormalizedMode
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
    simpa only [φ,modelPhaseFrequencyPhase,div_one,show (2 : ℝ)*2 = 4 by norm_num] using h
  · have hz := modelPhaseBufferedCutoff_eq_zero_of_overlap hη (le_of_not_ge hab)
    simp only [modelPhaseNormalizedMode,hz,Complex.ofReal_zero,zero_mul,integral_zero,norm_zero]
    positivity

theorem norm_modelPhaseBufferedFourierMode_curvature
    {F : ℝ → ℝ} {σ δ T N q l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4*(2/Real.pi+2)*N/Real.sqrt (T*modelPhaseCurvatureLower σ) := by
  rw [modelPhaseFourierMode_eq_normalized _ _ _ _ hN,norm_smul,
    Real.norm_eq_abs,abs_of_pos hN]
  exact (mul_le_mul_of_nonneg_left
    (norm_modelPhaseBufferedNormalizedMode_curvature hσ hδ hF hT hη hl hr)
    hN.le).trans_eq (by ring)

theorem modelPhaseBufferedFourierMode_uniform_curvature {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l r η : ℝ),
      1 ≤ l → r ≤ 2 → 0 < η →
      ∀ (F : ℝ → ℝ) (δ T N q : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ 1 δ →
        0 < T → 0 < N →
        ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
          C*N/Real.sqrt T := by
  let C := 4*(2/Real.pi+2)/Real.sqrt (modelPhaseCurvatureLower σ)
  have hc := modelPhaseCurvatureLower_pos hσ
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro l r η hl hr hη F δ T N q hδ hF hT hN
  have h := norm_modelPhaseBufferedFourierMode_curvature
    (q := q) hσ hδ hF hT hN hη hl hr
  rw [Real.sqrt_mul hT.le] at h
  exact h.trans_eq (by dsimp [C]; ring)

end TaoTrudgianYang2025
