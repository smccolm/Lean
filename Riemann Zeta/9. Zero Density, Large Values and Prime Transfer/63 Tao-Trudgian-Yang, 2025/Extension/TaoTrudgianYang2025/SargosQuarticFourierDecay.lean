import TaoTrudgianYang2025.SargosQuarticKernelJets
import GuthMaynard.DFIParametricMellin

/-! Exact original-mode Fourier normalization and uniform quantitative decay. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem sargosQuarticFourierMode_eq_scaled_fourier (χ : ℝ → ℝ) {N α : ℝ}
    (hN : 0 < N) (hα : 0 < α) (γ y : ℝ) :
    sargosQuarticFourierMode χ N α γ y =
      (N : ℂ)*𝓕 (sargosQuarticWeightedKernel χ 1 (α*N^2) ((α*N^2)*(γ*N^2/α))) (y*N) := by
  rw [sargosQuarticFourierMode_eq_normalized χ hN α γ y]
  congr 1
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with u
  change (χ u : ℂ)*(𝐞 (sargosQuarticPhase α γ (N*u)-y*(N*u)) : ℂ) =
    𝐞 (-((y*N)*u)) • sargosQuarticWeightedKernel χ 1 (α*N^2) ((α*N^2)*(γ*N^2/α)) u
  have hp := sargosQuarticPhase_normalize hN.ne' hα.ne' γ (N*u)
  rw [mul_div_cancel_left₀ _ hN.ne'] at hp
  rw [sargosQuarticWeightedKernel_normalized]
  simp only [Circle.smul_def,smul_eq_mul]
  rw [← hp,show α*N^2*sargosQuarticPhase 1 (γ*N^2/α) u-y*(N*u) =
    -((y*N)*u)+α*N^2*sargosQuarticPhase 1 (γ*N^2/α) u by ring,
    AddChar.map_add_eq_mul,Circle.coe_mul]
  ring

theorem sargosQuarticBufferedFourierMode_uniform_decay :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l b η : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (N α γ y : ℝ), 0 < N → 0 < α → |γ| ≤ α/(96*N^2) →
      (1+|y*N|)^2*‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y‖ ≤
        C*N*(η⁻¹)^2*(1+α*N^2)^2 := by
  obtain ⟨C,hC,hjets⟩ := sargosQuarticBufferedKernel_uniform_second_derivative
  refine ⟨8*C,by linarith,?_⟩
  intro l b η hl hb hη hη₁ N α γ y hN hα hγ
  let χ := modelPhaseBufferedCutoff l b η
  let T := α*N^2
  let ε := γ*N^2/α
  let f := sargosQuarticWeightedKernel χ 1 T (T*ε)
  have hT : 0 < T := by dsimp [T]; positivity
  have hε : |ε| ≤ 1/96 := sargosQuartic_normalized_coefficient_bound hN hα hγ
  have hs := modelPhaseBufferedCutoff_tsupport_model hη hl hb
  have hf := sargosQuarticWeightedKernel_contDiff (modelPhaseBufferedCutoff_contDiff l b η) 1 T (T*ε)
  have hsupport : Function.support f ⊆ Icc (1:ℝ) 2 := by
    intro u hu
    by_contra hn
    exact hu (sargosQuarticWeightedKernel_zero_of_not_mem hs (by norm_num)
      (by simpa only [mul_one] using hn) T (T*ε))
  have hb₀ : ∀ u, ‖iteratedDeriv 0 f u‖ ≤ 1 :=
    fun u => sargosQuarticBufferedKernel_norm_le_one l b η 1 T (T*ε) u
  have hb₂ := hjets l b η hl hb hη hη₁ ε T hε
  have h := RiemannZeta.GuthMaynard.one_add_abs_fourier_decay_of_support_of_bounds_order 2
    hf (by norm_num : (1:ℝ) ≤ 2) hsupport (by norm_num)
    (by positivity : 0 ≤ C*(η⁻¹)^2*(1+|T|)^2) hb₀ hb₂ (y*N)
  have hA : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη₁
  have hA₂ : 1 ≤ (η⁻¹)^2 := one_le_pow₀ hA
  have hU₂ : 1 ≤ (1+|T|)^2 := one_le_pow₀ (by linarith [abs_nonneg T])
  have hbig : 1 ≤ C*(η⁻¹)^2*(1+|T|)^2 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hA₂) hU₂
  have hfbound : (1+|y*N|)^2*‖𝓕 f (y*N)‖ ≤ 8*C*(η⁻¹)^2*(1+|T|)^2 := by
    norm_num only [Nat.reducePow,sub_self,sub_zero,show (2:ℝ)-1 = 1 by norm_num,mul_one] at h
    nlinarith
  rw [abs_of_pos hT] at hfbound
  rw [sargosQuarticFourierMode_eq_scaled_fourier _ hN hα,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN]
  have hh := mul_le_mul_of_nonneg_left hfbound hN.le
  dsimp [f,χ,T,ε] at hh ⊢
  nlinarith

theorem sargosQuarticBufferedFourierMode_inverse_square_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l b η : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (N α γ y : ℝ), 0 < N → 0 < α → |γ| ≤ α/(96*N^2) → y ≠ 0 →
      ‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y‖ ≤
        C*(η⁻¹)^2*(1+α*N^2)^2/(N*y^2) := by
  obtain ⟨C,hC,hdecay⟩ := sargosQuarticBufferedFourierMode_uniform_decay
  refine ⟨C,hC,?_⟩
  intro l b η hl hb hη hη₁ N α γ y hN hα hγ hy
  have h := hdecay l b η hl hb hη hη₁ N α γ y hN hα hγ
  have hsmall : |y*N|^2 ≤ (1+|y*N|)^2 := by nlinarith [abs_nonneg (y*N)]
  have hb' := (mul_le_mul_of_nonneg_right hsmall
    (norm_nonneg (sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y))).trans h
  rw [sq_abs,mul_pow] at hb'
  apply (le_div_iff₀ (mul_pos hN (sq_pos_of_ne_zero hy))).mpr
  apply (mul_le_mul_iff_left₀ hN).mp
  nlinarith

end TaoTrudgianYang2025

