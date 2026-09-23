import TaoTrudgianYang2025.SargosQuarticUniformSource

/-! Closed stationary-frequency conventions for the actual quartic phase.
The integer endpoint terms are retained, including exact resonances. -/

noncomputable section

open Set
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosQuarticStationaryFrequencies (N α γ : ℝ) : Finset ℤ :=
  Finset.Icc ⌈sargosQuarticSlope α γ N⌉ ⌊sargosQuarticSlope α γ (2*N)⌋

theorem mem_sargosQuarticStationaryFrequencies {N α γ : ℝ} {y : ℤ} :
    y ∈ sargosQuarticStationaryFrequencies N α γ ↔
      (y : ℝ) ∈ Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N)) := by
  simp only [sargosQuarticStationaryFrequencies,Finset.mem_Icc,mem_Icc,
    Int.ceil_le,Int.le_floor]

theorem sargosQuarticInverseSlope_mem_closed {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N))) :
    sargosQuarticInverseSlope N α γ y ∈ Icc N (2*N) := by
  obtain ⟨x,hx,rfl⟩ := intermediate_value_Icc (show N ≤ 2*N by linarith)
    (contDiff_sargosQuarticSlope α γ).continuous.continuousOn hy
  rw [sargosQuarticInverseSlope_slope hN hα hγ hx]
  exact hx

theorem sargosQuarticStationaryMainTerm_norm_bound_closed {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N))) :
    ‖sargosQuarticStationaryMainTerm N α γ y‖ ≤ 1/Real.sqrt α := by
  have hw := sargosQuarticInverseSlope_mem_closed hN hα hγ hy
  have hc := (sargosQuarticPhase_curvature hN hα hγ hw).1
  have ha : α ≤ 2*α+12*γ*(sargosQuarticInverseSlope N α γ y)^2 := by linarith
  simp only [sargosQuarticStationaryMainTerm,norm_div,Circle.norm_coe,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hα) (Real.sqrt_le_sqrt ha)

theorem sargosQuarticPlateau_subset_stationaryFrequencies {N α γ l b η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hflat : l+4*η < b) :
    Finset.Ioo (sargosQuarticPlateauLower N α γ l η)
      (sargosQuarticPlateauUpper N α γ b η) ⊆ sargosQuarticStationaryFrequencies N α γ := by
  intro y hy
  have hm := (sargosQuarticSlope_strictMonoOn hN hα hγ).monotoneOn
  have ha : N*(l+2*η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have hb' : N*(b-2*η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have hL := hm (show N ∈ Icc N (2*N) by constructor <;> linarith) ha ha.1
  have hR := hm hb' (show 2*N ∈ Icc N (2*N) by constructor <;> linarith) hb'.2
  have hy' := Finset.mem_Ioo.mp hy
  have hyl : (sargosQuarticPlateauLower N α γ l η : ℝ) < y := by exact_mod_cast hy'.1
  have hyr : (y : ℝ) < sargosQuarticPlateauUpper N α γ b η := by exact_mod_cast hy'.2
  have hc := Int.le_ceil (sargosQuarticSlope α γ (N*(l+2*η)))
  have hf := Int.floor_le (sargosQuarticSlope α γ (N*(b-2*η)))
  apply mem_sargosQuarticStationaryFrequencies.mpr
  change _ ≤ _ ∧ _ ≤ _
  change (⌈sargosQuarticSlope α γ (N*(l+2*η))⌉ : ℝ) < y at hyl
  change (y : ℝ) < ⌊sargosQuarticSlope α γ (N*(b-2*η))⌋ at hyr
  constructor <;> linarith

end TaoTrudgianYang2025

