import TaoTrudgianYang2025.SargosQuarticMorseRemainder

/-! Uniform physical stationary errors with an explicit original-cutoff jet budget. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosQuarticStationaryCutoffOrder : ℕ :=
  sargosQuarticMorseWeightCutoffOrder 0+sargosQuarticMorseWeightCutoffOrder 2+
    sargosQuarticMorseWeightCutoffOrder 3

def sargosQuarticStationaryRemainderConstant (M : ℝ) : ℝ :=
  quadraticRemainderConstant 7 (sargosQuarticMorseWeightDerivativeBound M 0)
    (sargosQuarticMorseWeightDerivativeBound M 2) (sargosQuarticMorseWeightDerivativeBound M 3)

theorem sargosQuarticStationaryRemainderConstant_nonneg {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ sargosQuarticStationaryRemainderConstant M :=
  quadraticRemainderConstant_nonneg (by norm_num)
    (sargosQuarticMorseWeightDerivativeBound_nonneg hM 0)
    (sargosQuarticMorseWeightDerivativeBound_nonneg hM 2)
    (sargosQuarticMorseWeightDerivativeBound_nonneg hM 3)

theorem sargosQuarticMorseRemainder_bound {χ : ℝ → ℝ} {ε r T M : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hT : 0 < T) (hM : 0 ≤ M)
    (hb : ∀ u ∈ Ioo (0 : ℝ) 3, ∀ k ≤ sargosQuarticStationaryCutoffOrder,
      |iteratedDeriv k χ u| ≤ M) :
    ‖sargosQuarticMorseRemainder χ ε r T‖ ≤ sargosQuarticStationaryRemainderConstant M/T := by
  have h₀ := sargosQuarticMorseWeight_iteratedDeriv_bound hχ hs hε hr hM 0
    (fun u hu k hk => hb u hu k (by unfold sargosQuarticStationaryCutoffOrder; omega))
  have h₂ := sargosQuarticMorseWeight_iteratedDeriv_bound hχ hs hε hr hM 2
    (fun u hu k hk => hb u hu k (by unfold sargosQuarticStationaryCutoffOrder; omega))
  have h₃ := sargosQuarticMorseWeight_iteratedDeriv_bound hχ hs hε hr hM 3
    (fun u hu k hk => hb u hu k (by unfold sargosQuarticStationaryCutoffOrder; omega))
  have hsupport : Function.support (sargosQuarticMorseWeight χ ε r) ⊆ Ioc (-7 : ℝ) 7 := by
    intro z hz
    have h := sargosQuarticMorseWeight_tsupport_uniform hs hε hr (subset_tsupport _ hz)
    constructor <;> linarith [h.1,h.2]
  exact sargos_positive_quadratic_global_remainder
    (sargosQuarticMorseWeight_contDiff hχ hs hε hr) hT (by norm_num) hsupport
    (by simpa only [iteratedDeriv_zero] using h₀ 0) h₂ h₃

theorem sargosQuarticFourierMode_stationary_bound {χ : ℝ → ℝ} {N α γ y M : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) (hM : 0 ≤ M)
    (hb : ∀ u ∈ Ioo (0 : ℝ) 3, ∀ k ≤ sargosQuarticStationaryCutoffOrder,
      |iteratedDeriv k χ u| ≤ M) :
    ‖sargosQuarticFourierMode χ N α γ y-
      (χ (sargosQuarticInverseSlope N α γ y/N) : ℂ)*sargosQuarticStationaryMainTerm N α γ y‖ ≤
        sargosQuarticStationaryRemainderConstant M/(α*N) := by
  have hs' : tsupport χ ⊆ Ioo (0 : ℝ) 3 := by
    intro u hu
    have h := hs hu
    constructor <;> linarith [h.1,h.2]
  have hr := sargosQuartic_normalized_inverse_mem hN hα hγ hy
  have hrc : sargosQuarticInverseSlope N α γ y/N ∈ Icc 0 3 := by
    constructor <;> linarith [hr.1,hr.2]
  have hR := sargosQuarticMorseRemainder_bound hχ hs'
    (sargosQuartic_normalized_coefficient_bound hN hα hγ) hrc
    (by positivity : 0 < α*N^2) hM hb
  rw [sargosQuarticFourierMode_sub_main_norm hs hN hα hγ hy]
  apply (mul_le_mul_of_nonneg_left hR hN.le).trans_eq
  field_simp

end TaoTrudgianYang2025

