import TaoTrudgianYang2025.SargosQuarticInteriorSum

/-! Rounded actual quartic support and plateau bands, including endpoint resonances. -/

noncomputable section

open Set
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosQuarticSupportLower (N α γ l η : ℝ) : ℤ :=
  ⌊sargosQuarticSlope α γ (N*(l+η))⌋

def sargosQuarticSupportUpper (N α γ b η : ℝ) : ℤ :=
  ⌈sargosQuarticSlope α γ (N*(b-η))⌉

def sargosQuarticPlateauLower (N α γ l η : ℝ) : ℤ :=
  ⌈sargosQuarticSlope α γ (N*(l+2*η))⌉

def sargosQuarticPlateauUpper (N α γ b η : ℝ) : ℤ :=
  ⌊sargosQuarticSlope α γ (N*(b-2*η))⌋

theorem sargosQuarticBand_endpoints {N α γ l b η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hflat : l+4*η < b) :
    sargosQuarticSupportLower N α γ l η ≤ sargosQuarticPlateauLower N α γ l η ∧
      sargosQuarticPlateauLower N α γ l η ≤ sargosQuarticSupportUpper N α γ b η ∧
      sargosQuarticSupportLower N α γ l η ≤ sargosQuarticPlateauUpper N α γ b η ∧
      sargosQuarticPlateauUpper N α γ b η ≤ sargosQuarticSupportUpper N α γ b η := by
  have ha₀ : N*(l+η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have ha : N*(l+2*η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have hb' : N*(b-2*η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have hb₀ : N*(b-η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have hm := (sargosQuarticSlope_strictMonoOn hN hα hγ).monotoneOn
  have h₁ := hm ha₀ ha (by nlinarith)
  have h₂ := hm ha hb₀ (by nlinarith)
  have h₃ := hm ha₀ hb' (by nlinarith)
  have h₄ := hm hb' hb₀ (by nlinarith)
  unfold sargosQuarticSupportLower sargosQuarticSupportUpper
    sargosQuarticPlateauLower sargosQuarticPlateauUpper
  exact ⟨(Int.floor_mono h₁).trans (Int.floor_le_ceil _),Int.ceil_mono h₂,
    Int.floor_mono h₃,(Int.floor_mono h₄).trans (Int.floor_le_ceil _)⟩

theorem sargosQuarticBand_card_bounds {N α γ l b η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hflat : l+4*η < b) :
    ((Finset.Icc (sargosQuarticSupportLower N α γ l η)
      (sargosQuarticPlateauLower N α γ l η)).card : ℝ) ≤ 5*α*N*η/2+3 ∧
    ((Finset.Icc (sargosQuarticPlateauUpper N α γ b η)
      (sargosQuarticSupportUpper N α γ b η)).card : ℝ) ≤ 5*α*N*η/2+3 := by
  have he := sargosQuarticBand_endpoints hN hα hγ hη hl hb hflat
  have ha₀ : N*(l+η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have ha : N*(l+2*η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have hb' : N*(b-2*η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have hb₀ : N*(b-η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have hL := sargosQuarticSlope_gap_upper hN hα hγ ha₀ ha (by nlinarith)
  have hR := sargosQuarticSlope_gap_upper hN hα hγ hb' hb₀ (by nlinarith)
  have hcardL : ((Finset.Icc (sargosQuarticSupportLower N α γ l η)
      (sargosQuarticPlateauLower N α γ l η)).card : ℝ) =
      (sargosQuarticPlateauLower N α γ l η : ℝ)+1-
        (sargosQuarticSupportLower N α γ l η : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le _ _ (show sargosQuarticSupportLower N α γ l η ≤
      sargosQuarticPlateauLower N α γ l η+1 by linarith [he.1])
  have hcardR : ((Finset.Icc (sargosQuarticPlateauUpper N α γ b η)
      (sargosQuarticSupportUpper N α γ b η)).card : ℝ) =
      (sargosQuarticSupportUpper N α γ b η : ℝ)+1-
        (sargosQuarticPlateauUpper N α γ b η : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le _ _ (show sargosQuarticPlateauUpper N α γ b η ≤
      sargosQuarticSupportUpper N α γ b η+1 by linarith [he.2.2.2])
  rw [hcardL,hcardR]
  unfold sargosQuarticSupportLower sargosQuarticSupportUpper
    sargosQuarticPlateauLower sargosQuarticPlateauUpper
  constructor
  · have hf := Int.lt_floor_add_one (sargosQuarticSlope α γ (N*(l+η)))
    have hc := Int.ceil_lt_add_one (sargosQuarticSlope α γ (N*(l+2*η)))
    nlinarith
  · have hf := Int.lt_floor_add_one (sargosQuarticSlope α γ (N*(b-2*η)))
    have hc := Int.ceil_lt_add_one (sargosQuarticSlope α γ (N*(b-η)))
    nlinarith

theorem sargosQuarticTransition_card_le {N α γ l b η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hflat : l+4*η < b) :
    (((Finset.Icc (sargosQuarticSupportLower N α γ l η)
        (sargosQuarticSupportUpper N α γ b η)) \
      (Finset.Ioo (sargosQuarticPlateauLower N α γ l η)
        (sargosQuarticPlateauUpper N α γ b η))).card : ℝ) ≤ 5*α*N*η+6 := by
  classical
  let S := (Finset.Icc (sargosQuarticSupportLower N α γ l η)
      (sargosQuarticSupportUpper N α γ b η)) \
    (Finset.Ioo (sargosQuarticPlateauLower N α γ l η)
      (sargosQuarticPlateauUpper N α γ b η))
  have hs : S ⊆
      Finset.Icc (sargosQuarticSupportLower N α γ l η)
        (sargosQuarticPlateauLower N α γ l η) ∪
      Finset.Icc (sargosQuarticPlateauUpper N α γ b η)
        (sargosQuarticSupportUpper N α γ b η) := by
    intro q hq
    simp only [S,Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_Ioo,Finset.mem_union] at *
    omega
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hc' : (S.card : ℝ) ≤
      ((Finset.Icc (sargosQuarticSupportLower N α γ l η)
        (sargosQuarticPlateauLower N α γ l η)).card : ℝ)+
      ((Finset.Icc (sargosQuarticPlateauUpper N α γ b η)
        (sargosQuarticSupportUpper N α γ b η)).card : ℝ) := by exact_mod_cast hc
  have hbound := sargosQuarticBand_card_bounds hN hα hγ hη hl hb hflat
  change (S.card : ℝ) ≤ _
  linarith [hbound.1,hbound.2]

end TaoTrudgianYang2025

