import TaoTrudgianYang2025.BourgainPairDensityClosure
import TaoTrudgianYang2025.BourgainPiecewiseCertificates
import TaoTrudgianYang2025.SquareProductCount
import TaoTrudgianYang2025.HuxleyLinearForms

/-! Analytic consumers for the optimized rational table. Seven pair inputs
are discharged below from proved source estimates, including the first two
new published pairs. Only the third new published pair, needed by piece 8,
remains open; full table closure is not claimed. -/

noncomputable section
namespace TaoTrudgianYang2025

open Expdb

theorem ExponentPair.bourgain_piece_1 {σ : ℝ}
    (hpair : ExponentPair (11/85) (59/85))
    (hσ : 3/4 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceOne σ):EReal) := by
  rw [bourgainPieceOne_eq_candidateFormula]
  have h := hpair.bourgain_zero_density_closed_low_k (by norm_num)
    (by norm_num) (by norm_num) (by norm_num; linarith) hσ1
  convert h using 1
  norm_num [generatedBourgainPiece1]

theorem ExponentPair.bourgain_piece_2 {σ : ℝ}
    (hpair : ExponentPair (391/4595) (3461/4595))
    (hσ : 14/15 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceTwo σ):EReal) := by
  rw [bourgainPieceTwo_eq_candidateFormula]
  have h := hpair.bourgain_zero_density_closed_low_k (by norm_num)
    (by norm_num) (by norm_num) (by norm_num; linarith) hσ1
  convert h using 1
  norm_num [generatedBourgainPiece2]

theorem ExponentPair.bourgain_piece_3 {σ : ℝ}
    (hpair : ExponentPair (2779/38033) (58699/76066))
    (hσ : 2841/3016 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceThree σ):EReal) := by
  rw [bourgainPieceThree_eq_candidateFormula]
  have h := hpair.bourgain_zero_density_closed_low_k (by norm_num)
    (by norm_num) (by norm_num) (by norm_num; linarith) hσ1
  convert h using 1
  norm_num [generatedBourgainPiece3]

theorem ExponentPair.bourgain_piece_4 {σ : ℝ}
    (hpair : ExponentPair (89/1282) (997/1282))
    (hσ : 859/908 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceFour σ):EReal) := by
  rw [bourgainPieceFour_eq_candidateFormula]
  have h := hpair.bourgain_zero_density_closed_low_k (by norm_num)
    (by norm_num) (by norm_num) (by norm_num; linarith) hσ1
  convert h using 1
  norm_num [generatedBourgainPiece4]

theorem ExponentPair.bourgain_piece_5 {σ : ℝ}
    (hpair : ExponentPair (652397/9713986) (7599781/9713986))
    (hσ : 1625/1692 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceFive σ):EReal) := by
  rw [bourgainPieceFive_eq_candidateFormula]
  have h := hpair.bourgain_zero_density_closed_low_k (by norm_num)
    (by norm_num) (by norm_num) (by norm_num; linarith) hσ1
  convert h using 1
  norm_num [generatedBourgainPiece5]

theorem ExponentPair.bourgain_piece_6 {σ : ℝ}
    (hpair : ExponentPair (2371/43205) (280013/345640))
    (hσ : 3334585/3447984 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceSix σ):EReal) := by
  rw [bourgainPieceSix_eq_candidateFormula]
  have h := hpair.bourgain_zero_density_closed_low_k (by norm_num)
    (by norm_num) (by norm_num) (by norm_num; linarith) hσ1
  convert h using 1
  norm_num [generatedBourgainPiece6]

theorem ExponentPair.bourgain_piece_7 {σ : ℝ}
    (hpair : ExponentPair (9/217) (1461/1736))
    (hσ : 974605/1005296 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceSeven σ):EReal) := by
  rw [bourgainPieceSeven_eq_candidateFormula]
  have h := hpair.bourgain_zero_density_closed_low_k (by norm_num)
    (by norm_num) (by norm_num) (by norm_num; linarith) hσ1
  convert h using 1
  norm_num [generatedBourgainPiece7]

theorem ExponentPair.bourgain_piece_8 {σ : ℝ}
    (hpair : ExponentPair (10769/351096) (609317/702192))
    (hσ : 5857/6032 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceEight σ):EReal) := by
  rw [bourgainPieceEight_eq_candidateFormula]
  have h := hpair.bourgain_zero_density_closed_low_k (by norm_num)
    (by norm_num) (by norm_num) (by norm_num; linarith) hσ1
  convert h using 1
  norm_num [generatedBourgainPiece8]

/-- The literal eight-piece published function, with each internal endpoint
owned by its left-hand piece. Its analytic validity is a separate theorem. -/
def optimizedBourgainBound (σ : ℝ) : ℝ :=
  if σ ≤ 14/15 then bourgainPieceOne σ else
  if σ ≤ 2841/3016 then bourgainPieceTwo σ else
  if σ ≤ 859/908 then bourgainPieceThree σ else
  if σ ≤ 1625/1692 then bourgainPieceFour σ else
  if σ ≤ 3334585/3447984 then bourgainPieceFive σ else
  if σ ≤ 974605/1005296 then bourgainPieceSix σ else
  if σ ≤ 5857/6032 then bourgainPieceSeven σ else
  bourgainPieceEight σ

/-- Conditional assembly consumes actual analytic pairs. This is not an
unconditional proof of the published eight-piece theorem. -/
theorem optimizedBourgain_bound_of_pairs {σ : ℝ}
    (h1 : ExponentPair (11/85) (59/85))
    (h2 : ExponentPair (391/4595) (3461/4595))
    (h3 : ExponentPair (2779/38033) (58699/76066))
    (h4 : ExponentPair (89/1282) (997/1282))
    (h5 : ExponentPair (652397/9713986) (7599781/9713986))
    (h6 : ExponentPair (2371/43205) (280013/345640))
    (h7 : ExponentPair (9/217) (1461/1736))
    (h8 : ExponentPair (10769/351096) (609317/702192))
    (hσ : 3/4 < σ) (hσ1 : σ < 1) :
    zeroDensityExponent σ ≤ ((optimizedBourgainBound σ):EReal) := by
  unfold optimizedBourgainBound
  by_cases hs1 : σ ≤ 14/15
  · rw [if_pos hs1]
    exact h1.bourgain_piece_1 hσ hσ1.le
  rw [if_neg hs1]
  by_cases hs2 : σ ≤ 2841/3016
  · rw [if_pos hs2]
    exact h2.bourgain_piece_2 (lt_of_not_ge hs1) hσ1.le
  rw [if_neg hs2]
  by_cases hs3 : σ ≤ 859/908
  · rw [if_pos hs3]
    exact h3.bourgain_piece_3 (lt_of_not_ge hs2) hσ1.le
  rw [if_neg hs3]
  by_cases hs4 : σ ≤ 1625/1692
  · rw [if_pos hs4]
    exact h4.bourgain_piece_4 (lt_of_not_ge hs3) hσ1.le
  rw [if_neg hs4]
  by_cases hs5 : σ ≤ 3334585/3447984
  · rw [if_pos hs5]
    exact h5.bourgain_piece_5 (lt_of_not_ge hs4) hσ1.le
  rw [if_neg hs5]
  by_cases hs6 : σ ≤ 974605/1005296
  · rw [if_pos hs6]
    exact h6.bourgain_piece_6 (lt_of_not_ge hs5) hσ1.le
  rw [if_neg hs6]
  by_cases hs7 : σ ≤ 5857/6032
  · rw [if_pos hs7]
    exact h7.bourgain_piece_7 (lt_of_not_ge hs6) hσ1.le
  rw [if_neg hs7]
  exact h8.bourgain_piece_8 (lt_of_not_ge hs7) hσ1.le

theorem exponentPair_eleven_eightyFifths :
    ExponentPair (11/85) (59/85) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  by_cases hlo : (α:ℝ) ≤ 3/7
  · have h := CubicJointCount.exponentSumGrowthExponent_le_sargosD_bourgain
      (α:=α) (by linarith only [hhalf] : (α:ℝ) ≤ 1)
    unfold exponentPairLine at h ⊢
    linarith only [h,hlo]
  · have h := exponentSumGrowthExponent_le_exponentPairLine_closed
      exponentPair_bourgain α (by linarith only [hhalf] : (α:ℝ) ≤ 1)
    unfold exponentPairLine at h ⊢
    linarith only [h,lt_of_not_ge hlo]

theorem zeroDensityExponent_le_bourgain_piece_1 {σ : ℝ}
    (hσ : 3/4 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceOne σ):EReal) :=
  exponentPair_eleven_eightyFifths.bourgain_piece_1 hσ hσ1

theorem zeroDensityExponent_le_bourgain_piece_6 {σ : ℝ}
    (hσ : 3334585/3447984 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceSix σ):EReal) :=
  CubicJointCount.exponentPair_aTrudgianYang_first.bourgain_piece_6 hσ hσ1

theorem zeroDensityExponent_le_bourgain_piece_7 {σ : ℝ}
    (hσ : 974605/1005296 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceSeven σ):EReal) :=
  CubicJointCount.exponentPair_sargosAD_bourgain.bourgain_piece_7 hσ hσ1

/-- Legacy explicit-input assembly preserving its original signature. Four
of these five pair inputs are now proved below; only the piece-8 input
remains open. This conditional interface does not assert full table closure. -/
theorem optimizedBourgain_bound_of_remaining_pairs {σ : ℝ}
    (h2 : ExponentPair (391/4595) (3461/4595))
    (h3 : ExponentPair (2779/38033) (58699/76066))
    (h4 : ExponentPair (89/1282) (997/1282))
    (h5 : ExponentPair (652397/9713986) (7599781/9713986))
    (h8 : ExponentPair (10769/351096) (609317/702192))
    (hσ : 3/4 < σ) (hσ1 : σ < 1) :
    zeroDensityExponent σ ≤ ((optimizedBourgainBound σ):EReal) :=
  optimizedBourgain_bound_of_pairs exponentPair_eleven_eightyFifths h2 h3 h4 h5
    CubicJointCount.exponentPair_aTrudgianYang_first
    CubicJointCount.exponentPair_sargosAD_bourgain h8 hσ hσ1

/-- The first new pair in the published theorem, with every beta input discharged. -/
theorem exponentPair_taoTrudgianYang_firstNew : ExponentPair (89/1282) (997/1282) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := CubicJointCount.exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_seventhRow (α:=α) (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eighthRow (α:=α) (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_ninthRow (α:=α) (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_tenthRow (α:=α) (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eleventhRow (α:=α) (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := CubicJointCount.exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

/-- The second new pair in the published theorem, with every beta input discharged. -/
theorem exponentPair_taoTrudgianYang_secondNew : ExponentPair (652397/9713986) (7599781/9713986) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := CubicJointCount.exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_seventhRow (α:=α) (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eighthRow (α:=α) (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_ninthRow (α:=α) (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_tenthRow (α:=α) (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eleventhRow (α:=α) (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := CubicJointCount.exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

theorem exponentPair_bourgain_piece_two_input : ExponentPair (391/4595) (3461/4595) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := CubicJointCount.exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_seventhRow (α:=α) (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eighthRow (α:=α) (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_ninthRow (α:=α) (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_tenthRow (α:=α) (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eleventhRow (α:=α) (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := CubicJointCount.exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

theorem exponentPair_bourgain_piece_three_input : ExponentPair (2779/38033) (58699/76066) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := CubicJointCount.exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_seventhRow (α:=α) (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eighthRow (α:=α) (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_ninthRow (α:=α) (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_tenthRow (α:=α) (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eleventhRow (α:=α) (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := CubicJointCount.exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

theorem zeroDensityExponent_le_bourgain_piece_2 {σ : ℝ}
    (hσ : 14/15 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceTwo σ):EReal) := by
  exact exponentPair_bourgain_piece_two_input.bourgain_piece_2 hσ hσ1

theorem zeroDensityExponent_le_bourgain_piece_3 {σ : ℝ}
    (hσ : 2841/3016 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceThree σ):EReal) := by
  exact exponentPair_bourgain_piece_three_input.bourgain_piece_3 hσ hσ1

theorem zeroDensityExponent_le_bourgain_piece_4 {σ : ℝ}
    (hσ : 859/908 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceFour σ):EReal) := by
  exact exponentPair_taoTrudgianYang_firstNew.bourgain_piece_4 hσ hσ1

theorem zeroDensityExponent_le_bourgain_piece_5 {σ : ℝ}
    (hσ : 1625/1692 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceFive σ):EReal) := by
  exact exponentPair_taoTrudgianYang_secondNew.bourgain_piece_5 hσ hσ1

end TaoTrudgianYang2025
