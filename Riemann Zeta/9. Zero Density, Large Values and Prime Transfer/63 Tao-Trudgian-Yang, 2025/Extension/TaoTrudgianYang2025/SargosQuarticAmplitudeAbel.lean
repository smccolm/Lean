import TaoTrudgianYang2025.SargosQuarticAmplitudeVariation
import TaoTrudgianYang2025.SargosIntegerPrefix
import TaoTrudgianYang2025.SargosQuarticPowerError

/-! Abel removal of the actual curvature amplitude from the complete stationary source sum. -/

noncomputable section

open Set
open scoped BigOperators FourierTransform

namespace TaoTrudgianYang2025

def sargosQuarticStationaryPrefixMaximum (N α γ : ℝ) : ℝ :=
  sargosIntegerPrefixMaximum ⌈sargosQuarticSlope α γ N⌉
    (⌊sargosQuarticSlope α γ (2*N)⌋+1-⌈sargosQuarticSlope α γ N⌉).toNat
    (fun y => (𝐞 (sargosQuarticLegendre N α γ y) : ℂ))

theorem sargosQuarticStationaryMainTerm_eq_amplitude_character (N α γ y : ℝ) :
    sargosQuarticStationaryMainTerm N α γ y =
      (𝐞 ((1:ℝ)/8) : ℂ)*((sargosQuarticStationaryAmplitude N α γ y : ℂ)*
        (𝐞 (sargosQuarticLegendre N α γ y) : ℂ)) := by
  simp only [sargosQuarticStationaryMainTerm,sargosQuarticStationaryAmplitude,
    AddChar.map_add_eq_mul,Circle.coe_mul,Complex.ofReal_div,Complex.ofReal_one]
  ring

theorem sargosQuarticStationarySum_le_prefixMaximum {N α γ : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) :
    ‖∑ y ∈ sargosQuarticStationaryFrequencies N α γ,
      sargosQuarticStationaryMainTerm N α γ y‖ ≤
        (2/Real.sqrt α)*sargosQuarticStationaryPrefixMaximum N α γ := by
  let a : ℤ := ⌈sargosQuarticSlope α γ N⌉
  let b : ℤ := ⌊sargosQuarticSlope α γ (2*N)⌋
  let H := (b+1-a).toNat
  let f : ℤ → ℂ := fun y => (𝐞 (sargosQuarticLegendre N α γ y) : ℂ)
  have hB := sargosIntegerPrefixMaximum_nonneg a H f
  change ‖∑ y ∈ Finset.Icc a b, sargosQuarticStationaryMainTerm N α γ y‖ ≤
    (2/Real.sqrt α)*sargosIntegerPrefixMaximum a H f
  by_cases hab : a ≤ b
  · let L := (b-a).toNat
    have hlen : H = L+1 := by dsimp [H,L]; omega
    have hr : ∀ i : ℕ, i ≤ L → (a : ℝ)+i ∈
        Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N)) := by
      intro i hi
      have hz := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
      have hiz : (i : ℤ) ≤ b-a := by dsimp [L] at hi; omega
      have hir : (i : ℝ) ≤ (b : ℝ)-(a : ℝ) := by exact_mod_cast hiz
      have hleft : sargosQuarticSlope α γ N ≤ (a : ℝ) := Int.le_ceil _
      have hright : (b : ℝ) ≤ sargosQuarticSlope α γ (2*N) := Int.floor_le _
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i]
    let z : ℕ → ℂ := fun i => (𝐞 (sargosQuarticLegendre N α γ ((a : ℝ)+i)) : ℂ)
    have hp : ∀ j ≤ L+1, ‖∑ i ∈ Finset.range j, z i‖ ≤ sargosIntegerPrefixMaximum a H f := by
      intro j hj
      have hh := norm_sargosIntegerPrefix_le_maximum a H j f (by omega)
      simpa only [sargosIntegerPrefix,f,z,Int.cast_add,Int.cast_natCast] using hh
    have hb := sargosQuarticStationaryAmplitude_sum_le_prefix_bound hN hα hγ (a : ℝ) L hr z hB hp
    rw [sargos_sum_Icc_eq_range,show (b+1-a).toNat = L+1 from hlen]
    have he :
        (∑ i ∈ Finset.range (L+1), sargosQuarticStationaryMainTerm N α γ ((a+(i:ℤ) : ℤ) : ℝ)) =
        (𝐞 ((1:ℝ)/8) : ℂ)*(∑ i ∈ Finset.range (L+1),
          (sargosQuarticStationaryAmplitude N α γ ((a : ℝ)+i) : ℂ)*z i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [sargosQuarticStationaryMainTerm_eq_amplitude_character]
      simp only [Int.cast_add,Int.cast_natCast,z]
    rw [he,norm_mul,Circle.norm_coe,one_mul]
    exact hb
  · have hz : Finset.Icc a b = ∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hab)
    rw [hz,Finset.sum_empty,norm_zero]
    exact mul_nonneg (by positivity) hB

theorem sargosQuartic_source_le_stationaryPrefixMaximum :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (α γ : ℝ),
      9216 ≤ N → 1/Real.sqrt (N : ℝ) ≤ α → α ≤ 1 → |γ| ≤ 1/(N : ℝ)^3 →
      ‖sargosQuarticSum N (fun _ => 1) α γ‖ ≤
        (2/Real.sqrt α)*sargosQuarticStationaryPrefixMaximum N α γ+
          C*(N : ℝ)^((1:ℝ)/4) := by
  obtain ⟨C,hC,hsource⟩ := sargosQuartic_source_le_stationary_quarterPower
  refine ⟨C,hC,?_⟩
  intro N α γ hN hα hα₁ hγ
  have hNr : (9216:ℝ) ≤ N := by exact_mod_cast hN
  have hs := hsource N α γ hN hα hα₁ hγ
  have ha := sargosQuarticStationarySum_le_prefixMaximum (by linarith : (0:ℝ) < N)
    (sargosQuartic_source_scale hNr hα).1 (sargosQuartic_source_smallness hNr hα hγ)
  exact hs.trans (add_le_add ha le_rfl)

end TaoTrudgianYang2025
