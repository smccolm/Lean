import TaoTrudgianYang2025.SquareProductCount
import TaoTrudgianYang2025.BourgainOptimizedTransfer

noncomputable section
open Expdb
open scoped NNReal
namespace TaoTrudgianYang2025

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

/-- The three proved pair inputs are discharged here. Only the five still
missing analytic pairs remain explicit; this is not full table closure. -/
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

example : ExponentPair (11/85) (59/85) := exponentPair_eleven_eightyFifths

example {σ : ℝ} (hσ : 3/4 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceOne σ):EReal) :=
  zeroDensityExponent_le_bourgain_piece_1 hσ hσ1

example {σ : ℝ} (hσ : 3334585/3447984 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceSix σ):EReal) :=
  zeroDensityExponent_le_bourgain_piece_6 hσ hσ1

example {σ : ℝ} (hσ : 974605/1005296 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceSeven σ):EReal) :=
  zeroDensityExponent_le_bourgain_piece_7 hσ hσ1

example {σ : ℝ}
    (h2 : ExponentPair (391/4595) (3461/4595))
    (h3 : ExponentPair (2779/38033) (58699/76066))
    (h4 : ExponentPair (89/1282) (997/1282))
    (h5 : ExponentPair (652397/9713986) (7599781/9713986))
    (h8 : ExponentPair (10769/351096) (609317/702192))
    (hσ : 3/4 < σ) (hσ1 : σ < 1) :
    zeroDensityExponent σ ≤ ((optimizedBourgainBound σ):EReal) :=
  optimizedBourgain_bound_of_remaining_pairs h2 h3 h4 h5 h8 hσ hσ1

example : zeroDensityExponent (14/15) ≤ ((bourgainPieceOne (14/15)):EReal) :=
  zeroDensityExponent_le_bourgain_piece_1 (by norm_num) (by norm_num)

example : zeroDensityExponent (974605/1005296) ≤
    ((bourgainPieceSix (974605/1005296)):EReal) :=
  zeroDensityExponent_le_bourgain_piece_6 (by norm_num) (by norm_num)

example : zeroDensityExponent (5857/6032) ≤
    ((bourgainPieceSeven (5857/6032)):EReal) :=
  zeroDensityExponent_le_bourgain_piece_7 (by norm_num) (by norm_num)

#print axioms exponentPair_eleven_eightyFifths
#print axioms zeroDensityExponent_le_bourgain_piece_1
#print axioms zeroDensityExponent_le_bourgain_piece_6
#print axioms zeroDensityExponent_le_bourgain_piece_7
#print axioms optimizedBourgain_bound_of_remaining_pairs
end TaoTrudgianYang2025
