import TaoTrudgianYang2025.SargosQuarticResidualBoundary

/-! Removal of the actual Legendre residual, preserving the full closed integer range. -/

noncomputable section

open Set
open scoped BigOperators FourierTransform

namespace TaoTrudgianYang2025

def sargosQuarticDualPolynomial (α γ y : ℝ) : ℝ :=
  -y^2/(4*α)+γ*y^4/(16*α^4)-γ^2*y^6/(16*α^7)

def sargosQuarticPolynomialPrefixMaximum (N α γ : ℝ) : ℝ :=
  sargosIntegerPrefixMaximum ⌈sargosQuarticSlope α γ N⌉
    (⌊sargosQuarticSlope α γ (2*N)⌋+1-⌈sargosQuarticSlope α γ N⌉).toNat
    (fun y => (𝐞 (sargosQuarticDualPolynomial α γ y) : ℂ))

theorem sargosQuarticLegendre_character_eq (N α γ y : ℝ) :
    (𝐞 (sargosQuarticLegendre N α γ y) : ℂ) =
      (𝐞 (sargosQuarticLegendreRemainder N α γ y) : ℂ)*
        (𝐞 (sargosQuarticDualPolynomial α γ y) : ℂ) := by
  rw [sargosQuarticLegendre_expansion,AddChar.map_add_eq_mul,Circle.coe_mul]
  exact mul_comm _ _

theorem sargosQuarticLegendrePrefix_le_polynomialMaximum
    {N α γ : ℝ} (hN : 9216 ≤ N) (hα : 1/Real.sqrt N ≤ α) (hγ : |γ| ≤ 1/N^3)
    (a : ℤ) (H L : ℕ) (hL : L ≤ H)
    (hr : ∀ i : ℕ, i < H → (a : ℝ)+i ∈
      Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N))) :
    ‖sargosIntegerPrefix a L (fun y => (𝐞 (sargosQuarticLegendre N α γ y) : ℂ))‖ ≤
      (2*(5+81920*Real.pi))*sargosIntegerPrefixMaximum a H
        (fun y => (𝐞 (sargosQuarticDualPolynomial α γ y) : ℂ)) := by
  have hB := sargosIntegerPrefixMaximum_nonneg a H
    (fun y => (𝐞 (sargosQuarticDualPolynomial α γ y) : ℂ))
  cases L with
  | zero =>
    simp only [sargosIntegerPrefix,Finset.sum_range_zero,norm_zero]
    exact mul_nonneg (by positivity) hB
  | succ L =>
    have hv := finiteVariationBound_sargosQuarticLegendreRemainder_closed hN hα hγ (a : ℝ) L
      (fun i hi => hr i (by omega))
    let z : ℕ → ℂ := fun i => (𝐞 (sargosQuarticDualPolynomial α γ ((a : ℝ)+i)) : ℂ)
    have hz : ∀ j ≤ L+1, ‖∑ i ∈ Finset.range j, z i‖ ≤
        sargosIntegerPrefixMaximum a H (fun y => (𝐞 (sargosQuarticDualPolynomial α γ y) : ℂ)) := by
      intro j hj
      have hh := norm_sargosIntegerPrefix_le_maximum a H j
        (fun y => (𝐞 (sargosQuarticDualPolynomial α γ y) : ℂ)) (by omega)
      simpa only [sargosIntegerPrefix,z,Int.cast_add,Int.cast_natCast] using hh
    have hh := norm_sum_range_succ_mul_le_of_finiteVariation hv hB hz
    simpa only [sargosIntegerPrefix,sargosQuarticLegendre_character_eq,
      Int.cast_add,Int.cast_natCast,z] using hh

theorem sargosQuarticStationaryPrefixMaximum_le_polynomial {N α γ : ℝ}
    (hN : 9216 ≤ N) (hα : 1/Real.sqrt N ≤ α) (hγ : |γ| ≤ 1/N^3) :
    sargosQuarticStationaryPrefixMaximum N α γ ≤
      (2*(5+81920*Real.pi))*sargosQuarticPolynomialPrefixMaximum N α γ := by
  let a : ℤ := ⌈sargosQuarticSlope α γ N⌉
  let b : ℤ := ⌊sargosQuarticSlope α γ (2*N)⌋
  let H := (b+1-a).toNat
  have hr : ∀ i : ℕ, i < H → (a : ℝ)+i ∈
      Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N)) := by
    intro i hi
    have hiz : a+(i:ℤ) ∈ Finset.Icc a b := by
      simp only [Finset.mem_Icc]
      dsimp [H] at hi
      constructor <;> omega
    have hh := mem_sargosQuarticStationaryFrequencies.mp hiz
    simpa only [Int.cast_add,Int.cast_natCast] using hh
  obtain ⟨L,hL,he⟩ := sargosIntegerPrefixMaximum_attained a H
    (fun y => (𝐞 (sargosQuarticLegendre N α γ y) : ℂ))
  change sargosIntegerPrefixMaximum a H (fun y => (𝐞 (sargosQuarticLegendre N α γ y) : ℂ)) ≤ _
  rw [he]
  exact sargosQuarticLegendrePrefix_le_polynomialMaximum hN hα hγ a H L hL hr

theorem sargosQuartic_source_le_polynomialPrefixMaximum :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (α γ : ℝ),
      9216 ≤ N → 1/Real.sqrt (N : ℝ) ≤ α → α ≤ 1 → |γ| ≤ 1/(N : ℝ)^3 →
      ‖sargosQuarticSum N (fun _ => 1) α γ‖ ≤
        C*((1/Real.sqrt α)*sargosQuarticPolynomialPrefixMaximum N α γ+
          (N : ℝ)^((1:ℝ)/4)) := by
  obtain ⟨C₀,hC₀,hsource⟩ := sargosQuartic_source_le_stationaryPrefixMaximum
  let M := 5+81920*Real.pi
  let C := max C₀ (4*M)
  have hC : C₀ ≤ C := le_max_left _ _
  have hCM : 4*M ≤ C := le_max_right _ _
  refine ⟨C,hC₀.trans hC,?_⟩
  intro N α γ hN hα hα₁ hγ
  have hNr : (9216:ℝ) ≤ N := by exact_mod_cast hN
  have hαp := (sargosQuartic_source_scale hNr hα).1
  have hs := hsource N α γ hN hα hα₁ hγ
  have hg := sargosQuarticStationaryPrefixMaximum_le_polynomial hNr hα hγ
  have hP : 0 ≤ sargosQuarticPolynomialPrefixMaximum N α γ :=
    sargosIntegerPrefixMaximum_nonneg _ _ _
  have hi : 0 ≤ 1/Real.sqrt α := by positivity
  have hp : 0 ≤ (N : ℝ)^((1:ℝ)/4) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hm := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2/Real.sqrt α by positivity)
  calc
    _ ≤ (2/Real.sqrt α)*((2*M)*sargosQuarticPolynomialPrefixMaximum N α γ)+
        C₀*(N : ℝ)^((1:ℝ)/4) := hs.trans (add_le_add hm le_rfl)
    _ = (4*M)*(1/Real.sqrt α)*sargosQuarticPolynomialPrefixMaximum N α γ+
        C₀*(N : ℝ)^((1:ℝ)/4) := by ring
    _ ≤ C*(1/Real.sqrt α)*sargosQuarticPolynomialPrefixMaximum N α γ+
        C*(N : ℝ)^((1:ℝ)/4) :=
      add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCM hi) hP)
        (mul_le_mul_of_nonneg_right hC hp)
    _ = _ := by ring

end TaoTrudgianYang2025

