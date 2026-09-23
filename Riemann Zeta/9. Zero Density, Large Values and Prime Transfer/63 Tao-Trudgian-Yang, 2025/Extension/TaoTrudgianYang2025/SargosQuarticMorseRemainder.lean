import TaoTrudgianYang2025.SargosQuarticMorseFourier
import TaoTrudgianYang2025.SargosPositiveQuadraticRemainder

/-! Exact physical stationary main term and the original cutoff-weighted remainder. -/

noncomputable section

open Set MeasureTheory
open scoped FourierTransform

namespace TaoTrudgianYang2025

def sargosQuarticStationaryMainTerm (N α γ y : ℝ) : ℂ :=
  (𝐞 (sargosQuarticLegendre N α γ y+(1:ℝ)/8) : ℂ)/
    (Real.sqrt (2*α+12*γ*(sargosQuarticInverseSlope N α γ y)^2) : ℂ)

def sargosQuarticMorseRemainder (χ : ℝ → ℝ) (ε r T : ℝ) : ℂ :=
  (∫ z : ℝ, (sargosQuarticMorseWeight χ ε r z : ℂ)*(𝐞 ((T/2)*z^2) : ℂ))-
    (sargosQuarticMorseWeight χ ε r 0 : ℂ)*
      ((𝐞 ((1:ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))

theorem sargosQuarticMorseLeadingTerm_scale {χ : ℝ → ℝ} {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    (N : ℂ)*(𝐞 (sargosQuarticLegendre N α γ y) : ℂ)*
        ((sargosQuarticMorseWeight χ (γ*N^2/α)
          (sargosQuarticInverseSlope N α γ y/N) 0 : ℂ)*
          ((𝐞 ((1:ℝ)/8) : ℂ)/(Real.sqrt (α*N^2) : ℂ))) =
      (χ (sargosQuarticInverseSlope N α γ y/N) : ℂ)*sargosQuarticStationaryMainTerm N α γ y := by
  have he := sargosQuartic_normalized_coefficient_bound hN hα hγ
  have hr := sargosQuartic_normalized_inverse_mem hN hα hγ hy
  have hro : sargosQuarticInverseSlope N α γ y/N ∈ Ioo 0 3 := by
    constructor <;> linarith [hr.1,hr.2]
  have hrc : sargosQuarticInverseSlope N α γ y/N ∈ Icc 0 3 := ⟨hro.1.le,hro.2.le⟩
  have hreal :
      N/Real.sqrt (α*N^2)*sargosQuarticMorseWeight χ (γ*N^2/α)
        (sargosQuarticInverseSlope N α γ y/N) 0 =
      χ (sargosQuarticInverseSlope N α γ y/N)/
        Real.sqrt (2*α+12*γ*(sargosQuarticInverseSlope N α γ y)^2) := by
    rw [sargosQuarticMorseWeight_eq (sargosQuarticMorseRange_zero hro),
      sargosQuarticMorseAmplitude,sargosQuarticMorseInverse_zero he hrc]
    calc
      _ = χ (sargosQuarticInverseSlope N α γ y/N)*
          (N/Real.sqrt (α*N^2)*
            deriv (sargosQuarticMorseInverse (γ*N^2/α)
              (sargosQuarticInverseSlope N α γ y/N)) 0) := by ring
      _ = _ := by rw [sargosQuartic_physical_stationary_amplitude hN hα hγ hy]; ring
  have hc := congrArg (fun t : ℝ => (t : ℂ)) hreal
  simp only [Complex.ofReal_mul,Complex.ofReal_div] at hc
  unfold sargosQuarticStationaryMainTerm
  rw [AddChar.map_add_eq_mul,Circle.coe_mul]
  calc
    _ = ((N : ℂ)/(Real.sqrt (α*N^2) : ℂ)*
          (sargosQuarticMorseWeight χ (γ*N^2/α)
            (sargosQuarticInverseSlope N α γ y/N) 0 : ℂ))*
          ((𝐞 (sargosQuarticLegendre N α γ y) : ℂ)*(𝐞 ((1:ℝ)/8) : ℂ)) := by ring
    _ = _ := by rw [hc]; ring

theorem sargosQuarticFourierMode_sub_main_eq_morseRemainder {χ : ℝ → ℝ} {N α γ y : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    sargosQuarticFourierMode χ N α γ y-
        (χ (sargosQuarticInverseSlope N α γ y/N) : ℂ)*sargosQuarticStationaryMainTerm N α γ y =
      (N : ℂ)*(𝐞 (sargosQuarticLegendre N α γ y) : ℂ)*
        sargosQuarticMorseRemainder χ (γ*N^2/α) (sargosQuarticInverseSlope N α γ y/N) (α*N^2) := by
  rw [sargosQuarticFourierMode_eq_global_morse hs hN hα hγ hy,
    ← sargosQuarticMorseLeadingTerm_scale hN hα hγ hy]
  unfold sargosQuarticMorseRemainder
  ring

theorem sargosQuarticFourierMode_sub_main_norm {χ : ℝ → ℝ} {N α γ y : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    ‖sargosQuarticFourierMode χ N α γ y-
        (χ (sargosQuarticInverseSlope N α γ y/N) : ℂ)*sargosQuarticStationaryMainTerm N α γ y‖ =
      N*‖sargosQuarticMorseRemainder χ (γ*N^2/α)
        (sargosQuarticInverseSlope N α γ y/N) (α*N^2)‖ := by
  rw [sargosQuarticFourierMode_sub_main_eq_morseRemainder hs hN hα hγ hy,
    norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN,Circle.norm_coe,mul_one]

end TaoTrudgianYang2025

