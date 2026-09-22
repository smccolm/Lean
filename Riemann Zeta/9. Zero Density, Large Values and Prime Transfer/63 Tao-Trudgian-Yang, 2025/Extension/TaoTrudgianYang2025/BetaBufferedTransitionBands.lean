import TaoTrudgianYang2025.BetaBufferedInteriorSum
import TaoTrudgianYang2025.BetaBufferedSupportGap
import TaoTrudgianYang2025.BetaBufferedCurvature

/-!
# The actual integer transition bands

Support and plateau endpoints are rounded in opposite directions.
The complement of the deep interior lies in two explicitly counted
bands, including all nearest and exactly resonant frequencies.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

def modelPhaseBufferedSupportLower (F : ℝ → ℝ) (r η T N : ℝ) : ℤ :=
  ⌊(T/N)*deriv F (r-η)⌋

def modelPhaseBufferedSupportUpper (F : ℝ → ℝ) (l η T N : ℝ) : ℤ :=
  ⌈(T/N)*deriv F (l+η)⌉

def modelPhaseBufferedPlateauLower (F : ℝ → ℝ) (r η T N : ℝ) : ℤ :=
  ⌈(T/N)*deriv F (r-2*η)⌉

def modelPhaseBufferedPlateauUpper (F : ℝ → ℝ) (l η T N : ℝ) : ℤ :=
  ⌊(T/N)*deriv F (l+2*η)⌋

theorem modelPhaseBufferedBand_endpoints
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hflat : l+4*η < r) :
    modelPhaseBufferedSupportLower F r η T N ≤ modelPhaseBufferedPlateauLower F r η T N ∧
      modelPhaseBufferedPlateauLower F r η T N ≤ modelPhaseBufferedSupportUpper F l η T N ∧
      modelPhaseBufferedSupportLower F r η T N ≤ modelPhaseBufferedPlateauUpper F l η T N ∧
      modelPhaseBufferedPlateauUpper F l η T N ≤ modelPhaseBufferedSupportUpper F l η T N := by
  have ha₀ : l+η ∈ Ioo (1 : ℝ) 2 := by constructor <;> linarith
  have ha : l+2*η ∈ Ioo (1 : ℝ) 2 := by constructor <;> linarith
  have hb : r-2*η ∈ Ioo (1 : ℝ) 2 := by constructor <;> linarith
  have hb₀ : r-η ∈ Ioo (1 : ℝ) 2 := by constructor <;> linarith
  have hm := (approximateModelPhase_deriv_strictAntiOn hσ hδ hF).antitoneOn
  have hscale : 0 ≤ T/N := (div_pos hT hN).le
  have h₁ := mul_le_mul_of_nonneg_left (hm hb hb₀ (by linarith)) hscale
  have h₂ := mul_le_mul_of_nonneg_left (hm ha₀ hb (by linarith)) hscale
  have h₃ := mul_le_mul_of_nonneg_left (hm ha hb₀ (by linarith)) hscale
  have h₄ := mul_le_mul_of_nonneg_left (hm ha₀ ha (by linarith)) hscale
  unfold modelPhaseBufferedSupportLower modelPhaseBufferedSupportUpper
    modelPhaseBufferedPlateauLower modelPhaseBufferedPlateauUpper
  exact ⟨(Int.floor_mono h₁).trans (Int.floor_le_ceil _),Int.ceil_mono h₂,
    Int.floor_mono h₃,(Int.floor_mono h₄).trans (Int.floor_le_ceil _)⟩

theorem modelPhaseBufferedBand_card_bounds
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hflat : l+4*η < r) :
    ((Finset.Icc (modelPhaseBufferedSupportLower F r η T N)
      (modelPhaseBufferedPlateauLower F r η T N)).card : ℝ) ≤ (T/N)*(σ+1)*η+3 ∧
    ((Finset.Icc (modelPhaseBufferedPlateauUpper F l η T N)
      (modelPhaseBufferedSupportUpper F l η T N)).card : ℝ) ≤ (T/N)*(σ+1)*η+3 := by
  have he := modelPhaseBufferedBand_endpoints hσ hδ hF hT hN hη hl hr hflat
  have ha₀ : l+η ∈ Ioo (1 : ℝ) 2 := by constructor <;> linarith
  have ha : l+2*η ∈ Ioo (1 : ℝ) 2 := by constructor <;> linarith
  have hb : r-2*η ∈ Ioo (1 : ℝ) 2 := by constructor <;> linarith
  have hb₀ : r-η ∈ Ioo (1 : ℝ) 2 := by constructor <;> linarith
  have hL := (le_abs_self (deriv F (r-2*η)-deriv F (r-η))).trans
    (approximateModelPhase_slope_gap_upper_abs hσ hδ hF hb hb₀)
  have hR := (le_abs_self (deriv F (l+η)-deriv F (l+2*η))).trans
    (approximateModelPhase_slope_gap_upper_abs hσ hδ hF ha₀ ha)
  rw [show r-2*η-(r-η) = -η by ring,abs_neg,abs_of_pos hη] at hL
  rw [show l+η-(l+2*η) = -η by ring,abs_neg,abs_of_pos hη] at hR
  have hL' := mul_le_mul_of_nonneg_left hL (div_pos hT hN).le
  have hR' := mul_le_mul_of_nonneg_left hR (div_pos hT hN).le
  have hcardL : ((Finset.Icc (modelPhaseBufferedSupportLower F r η T N)
      (modelPhaseBufferedPlateauLower F r η T N)).card : ℝ) =
      (modelPhaseBufferedPlateauLower F r η T N : ℝ)+1-
        (modelPhaseBufferedSupportLower F r η T N : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le _ _ (show modelPhaseBufferedSupportLower F r η T N ≤
      modelPhaseBufferedPlateauLower F r η T N+1 by linarith [he.1])
  have hcardR : ((Finset.Icc (modelPhaseBufferedPlateauUpper F l η T N)
      (modelPhaseBufferedSupportUpper F l η T N)).card : ℝ) =
      (modelPhaseBufferedSupportUpper F l η T N : ℝ)+1-
        (modelPhaseBufferedPlateauUpper F l η T N : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le _ _ (show modelPhaseBufferedPlateauUpper F l η T N ≤
      modelPhaseBufferedSupportUpper F l η T N+1 by linarith [he.2.2.2])
  rw [hcardL,hcardR]
  unfold modelPhaseBufferedPlateauLower modelPhaseBufferedSupportLower
    modelPhaseBufferedSupportUpper modelPhaseBufferedPlateauUpper
  constructor
  · have hfloor := Int.lt_floor_add_one ((T/N)*deriv F (r-η))
    have hceil := Int.ceil_lt_add_one ((T/N)*deriv F (r-2*η))
    nlinarith
  · have hfloor := Int.lt_floor_add_one ((T/N)*deriv F (l+2*η))
    have hceil := Int.ceil_lt_add_one ((T/N)*deriv F (l+η))
    nlinarith

theorem modelPhaseBufferedTransition_card_le
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hflat : l+4*η < r) :
    (((Finset.Icc (modelPhaseBufferedSupportLower F r η T N)
        (modelPhaseBufferedSupportUpper F l η T N)) \
      (Finset.Ioo (modelPhaseBufferedPlateauLower F r η T N)
        (modelPhaseBufferedPlateauUpper F l η T N))).card : ℝ) ≤
      2*(T/N)*(σ+1)*η+6 := by
  classical
  let S := (Finset.Icc (modelPhaseBufferedSupportLower F r η T N)
      (modelPhaseBufferedSupportUpper F l η T N)) \
    (Finset.Ioo (modelPhaseBufferedPlateauLower F r η T N)
      (modelPhaseBufferedPlateauUpper F l η T N))
  have hs : S ⊆
      Finset.Icc (modelPhaseBufferedSupportLower F r η T N)
        (modelPhaseBufferedPlateauLower F r η T N) ∪
      Finset.Icc (modelPhaseBufferedPlateauUpper F l η T N)
        (modelPhaseBufferedSupportUpper F l η T N) := by
    intro q hq
    simp only [S,Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_Ioo,Finset.mem_union] at *
    omega
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hc' : (S.card : ℝ) ≤
      ((Finset.Icc (modelPhaseBufferedSupportLower F r η T N)
        (modelPhaseBufferedPlateauLower F r η T N)).card : ℝ)+
      ((Finset.Icc (modelPhaseBufferedPlateauUpper F l η T N)
        (modelPhaseBufferedSupportUpper F l η T N)).card : ℝ) := by exact_mod_cast hc
  have hb := modelPhaseBufferedBand_card_bounds hσ hδ hF hT hN hη hl hr hflat
  change (S.card : ℝ) ≤ _
  linarith [hb.1,hb.2]

end TaoTrudgianYang2025
