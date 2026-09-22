import TaoTrudgianYang2025.BetaBufferedKernelJets
import GuthMaynard.DFIParametricMellin

/-!
# Quantitative second-order decay of the actual buffered Fourier modes

The explicit constant is uniform before endpoints, width, phase, height,
physical scale and frequency. The original factor N is retained.
-/

noncomputable section

open Complex Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem modelPhaseNormalizedMode_eq_fourier (χ F : ℝ → ℝ) (T ξ : ℝ) :
    modelPhaseNormalizedMode χ F T ξ =
      𝓕 (modelPhaseWeightedKernel χ F T 1) ξ := by
  rw [Real.fourier_eq]
  unfold modelPhaseNormalizedMode
  apply integral_congr_ae
  filter_upwards [] with u
  change (χ u : ℂ)*(𝐞 (T*F u-ξ*u) : ℂ) =
    𝐞 (-(ξ*u)) • modelPhaseWeightedKernel χ F T 1 u
  simp only [Circle.smul_def,smul_eq_mul,modelPhaseWeightedKernel,div_one]
  rw [show T*F u-ξ*u = -(ξ*u)+T*F u by ring,
    AddChar.map_add_eq_mul,Circle.coe_mul]
  ring

theorem modelPhaseBufferedFourierMode_uniform_decay
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T N q : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < N →
        (1+|q*N|)^2 *
          ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
          C*N*(η⁻¹)^2*(1+|T|)^2 := by
  obtain ⟨C,hC,hjets⟩ := modelPhaseBufferedKernel_uniform_second_derivative hσ
  refine ⟨8*C,by linarith,?_⟩
  intro l r η hl hr hη hη₁ F δ T N q hδ hF hN
  let χ := modelPhaseBufferedCutoff l r η
  let f := modelPhaseWeightedKernel χ F T 1
  have hs := modelPhaseBufferedCutoff_tsupport_model hη hl hr
  have hf := modelPhaseWeightedKernel_contDiff
    (modelPhaseBufferedCutoff_contDiff l r η) hs hF T 1
  have hsupport : Function.support f ⊆ Icc (1 : ℝ) 2 := by
    intro u hu
    by_contra hn
    exact hu (by
      exact modelPhaseWeightedKernel_zero_of_not_mem hs (by norm_num)
        (by simpa only [mul_one] using hn) T)
  have hb₀ : ∀ u, ‖iteratedDeriv 0 f u‖ ≤ 1 := by
    intro u
    exact norm_modelPhaseBufferedKernel_le_one l r η T 1 u F
  have hb₂ := hjets l r η hl hr hη hη₁ F δ T hδ hF
  have h := RiemannZeta.GuthMaynard.one_add_abs_fourier_decay_of_support_of_bounds_order 2
    hf (by norm_num : (1 : ℝ) ≤ 2) hsupport (by norm_num)
    (by positivity : 0 ≤ C*(η⁻¹)^2*(1+|T|)^2) hb₀ hb₂ (q*N)
  have hA : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη₁
  have hA₂ : 1 ≤ (η⁻¹)^2 := one_le_pow₀ hA
  have hU₂ : 1 ≤ (1+|T|)^2 := one_le_pow₀ (by linarith [abs_nonneg T])
  have hbig : 1 ≤ C*(η⁻¹)^2*(1+|T|)^2 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hA₂) hU₂
  have hfbound : (1+|q*N|)^2 * ‖𝓕 f (q*N)‖ ≤
      8*C*(η⁻¹)^2*(1+|T|)^2 := by
    norm_num only [Nat.reducePow,sub_self,sub_zero,show (2:ℝ)-1 = 1 by norm_num,mul_one] at h
    nlinarith
  rw [modelPhaseFourierMode_eq_normalized χ F T q hN,
    modelPhaseNormalizedMode_eq_fourier,norm_smul,Real.norm_of_nonneg hN.le]
  have hh := mul_le_mul_of_nonneg_left hfbound hN.le
  dsimp [f,χ] at hh ⊢
  nlinarith

theorem modelPhaseBufferedFourierMode_inverse_square_bound
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T N q : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < N → q ≠ 0 →
        ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
          C*(η⁻¹)^2*(1+|T|)^2/(N*q^2) := by
  obtain ⟨C,hC,hdecay⟩ := modelPhaseBufferedFourierMode_uniform_decay hσ
  refine ⟨C,hC,?_⟩
  intro l r η hl hr hη hη₁ F δ T N q hδ hF hN hq
  have h := hdecay l r η hl hr hη hη₁ F δ T N q hδ hF hN
  have hsmall : |q*N|^2 ≤ (1+|q*N|)^2 := by nlinarith [abs_nonneg (q*N)]
  have hb := (mul_le_mul_of_nonneg_right hsmall
    (norm_nonneg (modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q))).trans h
  rw [sq_abs,mul_pow] at hb
  apply (le_div_iff₀ (mul_pos hN (sq_pos_of_ne_zero hq))).mpr
  apply (mul_le_mul_iff_left₀ hN).mp
  nlinarith

end TaoTrudgianYang2025
