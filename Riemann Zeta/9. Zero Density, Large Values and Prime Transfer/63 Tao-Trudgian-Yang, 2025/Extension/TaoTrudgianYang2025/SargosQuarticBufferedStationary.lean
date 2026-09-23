import TaoTrudgianYang2025.SargosQuarticStationaryEstimate
import TaoTrudgianYang2025.SargosQuarticBufferedJets

/-! Quantitative stationary bounds uniform in the actual buffered cutoff family.
The eta^(-3) loss is explicit; this is not the sharp summed B-transform. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem sargosQuarticBufferedRemainder_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l b η : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (ε r T : ℝ), |ε| ≤ 1/96 → r ∈ Icc 0 3 → 0 < T →
      ‖sargosQuarticMorseRemainder (modelPhaseBufferedCutoff l b η) ε r T‖ ≤
        C*(η⁻¹)^3/T := by
  obtain ⟨C₀,hC₀,h₀⟩ := sargosQuarticBufferedWeight_uniform_derivative 0
  obtain ⟨C₂,hC₂,h₂⟩ := sargosQuarticBufferedWeight_uniform_derivative 2
  obtain ⟨C₃,hC₃,h₃⟩ := sargosQuarticBufferedWeight_uniform_derivative 3
  refine ⟨max (quadraticRemainderConstant 7 C₀ C₂ C₃) 1,le_max_right _ _,?_⟩
  intro l b η hl hb hη hη₁ ε r T hε hr hT
  have hA : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη₁
  have hs₁₂ := modelPhaseBufferedCutoff_tsupport_model hη hl hb
  have hs : tsupport (modelPhaseBufferedCutoff l b η) ⊆ Ioo (0 : ℝ) 3 := by
    intro u hu
    have h := hs₁₂ hu
    constructor <;> linarith [h.1,h.2]
  have h₀' (z : ℝ) :
      |iteratedDeriv 0 (sargosQuarticMorseWeight (modelPhaseBufferedCutoff l b η) ε r) z| ≤
        C₀*(η⁻¹)^3 :=
    (h₀ l b η hl hb hη hη₁ ε r hε hr z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (by omega : 0 ≤ 3)) (zero_le_one.trans hC₀))
  have h₂' (z : ℝ) :
      |iteratedDeriv 2 (sargosQuarticMorseWeight (modelPhaseBufferedCutoff l b η) ε r) z| ≤
        C₂*(η⁻¹)^3 :=
    (h₂ l b η hl hb hη hη₁ ε r hε hr z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (by omega : 2 ≤ 3)) (zero_le_one.trans hC₂))
  have h₃' := h₃ l b η hl hb hη hη₁ ε r hε hr
  have hsupport : Function.support (sargosQuarticMorseWeight (modelPhaseBufferedCutoff l b η) ε r) ⊆
      Ioc (-7 : ℝ) 7 := by
    intro z hz
    have h := sargosQuarticMorseWeight_tsupport_uniform hs hε hr (subset_tsupport _ hz)
    constructor <;> linarith [h.1,h.2]
  have h := sargos_positive_quadratic_global_remainder
    (sargosQuarticMorseWeight_contDiff (modelPhaseBufferedCutoff_contDiff l b η) hs hε hr)
    hT (by norm_num) hsupport (by simpa only [iteratedDeriv_zero] using h₀' 0) h₂' h₃'
  have hscale : quadraticRemainderConstant 7 (C₀*(η⁻¹)^3) (C₂*(η⁻¹)^3) (C₃*(η⁻¹)^3) =
      quadraticRemainderConstant 7 C₀ C₂ C₃*(η⁻¹)^3 := by
    unfold quadraticRemainderConstant
    ring
  rw [hscale] at h
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hT.le)

theorem sargosQuarticBufferedFourierMode_stationary_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l b η : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (N α γ y : ℝ), 0 < N → 0 < α → |γ| ≤ α/(96*N^2) →
      y ∈ sargosQuarticSlopeRange N α γ →
      ‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y-
        (modelPhaseBufferedCutoff l b η (sargosQuarticInverseSlope N α γ y/N) : ℂ)*
          sargosQuarticStationaryMainTerm N α γ y‖ ≤ C*(η⁻¹)^3/(α*N) := by
  obtain ⟨C,hC,hR⟩ := sargosQuarticBufferedRemainder_uniform
  refine ⟨C,hC,?_⟩
  intro l b η hl hb hη hη₁ N α γ y hN hα hγ hy
  have hr := sargosQuartic_normalized_inverse_mem hN hα hγ hy
  have hrc : sargosQuarticInverseSlope N α γ y/N ∈ Icc 0 3 := by
    constructor <;> linarith [hr.1,hr.2]
  have h := hR l b η hl hb hη hη₁ (γ*N^2/α) (sargosQuarticInverseSlope N α γ y/N) (α*N^2)
    (sargosQuartic_normalized_coefficient_bound hN hα hγ) hrc (by positivity)
  rw [sargosQuarticFourierMode_sub_main_norm
    (modelPhaseBufferedCutoff_tsupport_model hη hl hb) hN hα hγ hy]
  apply (mul_le_mul_of_nonneg_left h hN.le).trans_eq
  field_simp

end TaoTrudgianYang2025

