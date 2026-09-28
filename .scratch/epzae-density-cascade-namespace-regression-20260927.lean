import TaoTrudgianYang2025
open Expdb GafniTao TaoTrudgianYang2025
example : ExponentPair (11/85) (59/85) := exponentPair_eleven_eightyFifths

example {σ : ℝ} (hσ : 3/4 < σ) (hσ1 : σ ≤ 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((bourgainPieceOne σ):EReal) :=
  zeroDensityExponent_le_bourgain_piece_1 hσ hσ1

example {σ : ℝ} (hσ : 3334585/3447984 < σ) (hσ1 : σ ≤ 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((bourgainPieceSix σ):EReal) :=
  zeroDensityExponent_le_bourgain_piece_6 hσ hσ1

example {σ : ℝ} (hσ : 974605/1005296 < σ) (hσ1 : σ ≤ 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((bourgainPieceSeven σ):EReal) :=
  zeroDensityExponent_le_bourgain_piece_7 hσ hσ1

example {σ : ℝ}
    (h2 : ExponentPair (391/4595) (3461/4595))
    (h3 : ExponentPair (2779/38033) (58699/76066))
    (h4 : ExponentPair (89/1282) (997/1282))
    (h5 : ExponentPair (652397/9713986) (7599781/9713986))
    (h8 : ExponentPair (10769/351096) (609317/702192))
    (hσ : 3/4 < σ) (hσ1 : σ < 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((optimizedBourgainBound σ):EReal) :=
  optimizedBourgain_bound_of_remaining_pairs h2 h3 h4 h5 h8 hσ hσ1

example : TaoTrudgianYang2025.zeroDensityExponent (14/15) ≤ ((bourgainPieceOne (14/15)):EReal) :=
  zeroDensityExponent_le_bourgain_piece_1 (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (974605/1005296) ≤
    ((bourgainPieceSix (974605/1005296)):EReal) :=
  zeroDensityExponent_le_bourgain_piece_6 (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (5857/6032) ≤
    ((bourgainPieceSeven (5857/6032)):EReal) :=
  zeroDensityExponent_le_bourgain_piece_7 (by norm_num) (by norm_num)

