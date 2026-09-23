import TaoTrudgianYang2025.SargosQuarticClosedRange

/-! Counts for the actual missing stationary endpoint bands, including resonant endpoints. -/

noncomputable section

open Set
open scoped BigOperators

namespace TaoTrudgianYang2025

private theorem card_Icc_ceil_ceil_le {x y : ℝ} (hxy : x ≤ y) :
    ((Finset.Icc ⌈x⌉ ⌈y⌉).card : ℝ) ≤ y-x+2 := by
  have hc : ((Finset.Icc ⌈x⌉ ⌈y⌉).card : ℝ) = (⌈y⌉ : ℝ)+1-(⌈x⌉ : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le ⌈x⌉ ⌈y⌉ (by have hh := Int.ceil_mono hxy; omega)
  rw [hc]
  linarith [Int.le_ceil x,Int.ceil_lt_add_one y]

private theorem card_Icc_floor_floor_le {x y : ℝ} (hxy : x ≤ y) :
    ((Finset.Icc ⌊x⌋ ⌊y⌋).card : ℝ) ≤ y-x+2 := by
  have hc : ((Finset.Icc ⌊x⌋ ⌊y⌋).card : ℝ) = (⌊y⌋ : ℝ)+1-(⌊x⌋ : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le ⌊x⌋ ⌊y⌋ (by have hh := Int.floor_mono hxy; omega)
  rw [hc]
  linarith [Int.lt_floor_add_one x,Int.floor_le y]

theorem sargosQuarticEndpointBands_card {N α γ η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hflat : (N+1)/N+4*η < 2) :
    ((Finset.Icc ⌈sargosQuarticSlope α γ N⌉
      (sargosQuarticPlateauLower N α γ ((N+1)/N) η)).card : ℝ) ≤
        5*α/2+5*α*N*η+2 ∧
    ((Finset.Icc (sargosQuarticPlateauUpper N α γ 2 η)
      ⌊sargosQuarticSlope α γ (2*N)⌋).card : ℝ) ≤ 5*α*N*η+2 := by
  let l := (N+1)/N
  have hl : 1 ≤ l := (one_le_div hN).mpr (by linarith)
  have hn : N*l = N+1 := by dsimp [l]; field_simp
  have ha : N*(l+2*η) ∈ Icc N (2*N) := by constructor <;> dsimp [l] at * <;> nlinarith
  have hb : N*(2-2*η) ∈ Icc N (2*N) := by constructor <;> dsimp [l] at * <;> nlinarith
  have hNmem : N ∈ Icc N (2*N) := by constructor <;> linarith
  have h2Nmem : 2*N ∈ Icc N (2*N) := by constructor <;> linarith
  have hm := (sargosQuarticSlope_strictMonoOn hN hα hγ).monotoneOn
  have hgL := sargosQuarticSlope_gap_upper hN hα hγ hNmem ha ha.1
  have hgR := sargosQuarticSlope_gap_upper hN hα hγ hb h2Nmem hb.2
  have hcL := card_Icc_ceil_ceil_le (hm hNmem ha ha.1)
  have hcR := card_Icc_floor_floor_le (hm hb h2Nmem hb.2)
  change ((Finset.Icc ⌈sargosQuarticSlope α γ N⌉
    ⌈sargosQuarticSlope α γ (N*(l+2*η))⌉).card : ℝ) ≤ _ ∧
    ((Finset.Icc ⌊sargosQuarticSlope α γ (N*(2-2*η))⌋
      ⌊sargosQuarticSlope α γ (2*N)⌋).card : ℝ) ≤ _
  constructor
  · have he : N*(l+2*η)-N = 1+2*N*η := by nlinarith only [hn]
    rw [he] at hgL
    nlinarith only [hcL,hgL]
  · nlinarith only [hcR,hgR]

theorem sargosQuarticOmittedStationary_card {N α γ η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hflat : (N+1)/N+4*η < 2) :
    let A := sargosQuarticPlateauLower N α γ ((N+1)/N) η
    let B := sargosQuarticPlateauUpper N α γ 2 η
    (((sargosQuarticStationaryFrequencies N α γ) \ (Finset.Ioo A B)).card : ℝ) ≤
      5*α/2+10*α*N*η+4 := by
  classical
  intro A B
  let L := ⌈sargosQuarticSlope α γ N⌉
  let U := ⌊sargosQuarticSlope α γ (2*N)⌋
  let S := sargosQuarticStationaryFrequencies N α γ \ Finset.Ioo A B
  have hs : S ⊆ Finset.Icc L A ∪ Finset.Icc B U := by
    intro y hy
    simp only [S,sargosQuarticStationaryFrequencies,L,U,Finset.mem_sdiff,
      Finset.mem_Icc,Finset.mem_Ioo,Finset.mem_union] at *
    omega
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hc' : (S.card : ℝ) ≤ ((Finset.Icc L A).card : ℝ)+((Finset.Icc B U).card : ℝ) := by
    exact_mod_cast hc
  have hb := sargosQuarticEndpointBands_card hN hα hγ hη hflat
  change (S.card : ℝ) ≤ _
  linarith [hb.1,hb.2]

end TaoTrudgianYang2025

