import TaoTrudgianYang2025

open scoped NNReal

example
    {α : ℝ≥0} (hα : (423:ℝ)/1295≤(α:ℝ)) (hα₁ : (α:ℝ)≤(227:ℝ)/601) :
    Expdb.exponentSumGrowthExponent α≤(89+908*(α:ℝ))/1282 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_ninthRow (α:=α) hα hα₁

example
    {α : ℝ≥0} (hα : (227:ℝ)/601≤(α:ℝ)) (hα₁ : (α:ℝ)≤(12:ℝ)/31) :
    Expdb.exponentSumGrowthExponent α≤(29+173*(α:ℝ))/280 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_tenthRow (α:=α) hα hα₁

example
    {α : ℝ≥0} (hα : (12:ℝ)/31≤(α:ℝ)) (hα₁ : (α:ℝ)≤(1508:ℝ)/3825) :
    Expdb.exponentSumGrowthExponent α≤(4+103*(α:ℝ))/128 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eleventhRow (α:=α) hα hα₁

example : TaoTrudgianYang2025.ExponentPair (89/1282) (997/1282) :=
  TaoTrudgianYang2025.exponentPair_taoTrudgianYang_firstNew

example : TaoTrudgianYang2025.ExponentPair (652397/9713986) (7599781/9713986) :=
  TaoTrudgianYang2025.exponentPair_taoTrudgianYang_secondNew

example : TaoTrudgianYang2025.ExponentPair (391/4595) (3461/4595) :=
  TaoTrudgianYang2025.exponentPair_bourgain_piece_two_input

example : TaoTrudgianYang2025.ExponentPair (2779/38033) (58699/76066) :=
  TaoTrudgianYang2025.exponentPair_bourgain_piece_three_input

example {σ : ℝ}
    (hσ : 14/15 < σ) (hσ1 : σ ≤ 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((TaoTrudgianYang2025.bourgainPieceTwo σ):EReal) :=
  TaoTrudgianYang2025.zeroDensityExponent_le_bourgain_piece_2 (σ:=σ) hσ hσ1

example {σ : ℝ}
    (hσ : 2841/3016 < σ) (hσ1 : σ ≤ 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((TaoTrudgianYang2025.bourgainPieceThree σ):EReal) :=
  TaoTrudgianYang2025.zeroDensityExponent_le_bourgain_piece_3 (σ:=σ) hσ hσ1

example {σ : ℝ}
    (hσ : 859/908 < σ) (hσ1 : σ ≤ 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((TaoTrudgianYang2025.bourgainPieceFour σ):EReal) :=
  TaoTrudgianYang2025.zeroDensityExponent_le_bourgain_piece_4 (σ:=σ) hσ hσ1

example {σ : ℝ}
    (hσ : 1625/1692 < σ) (hσ1 : σ ≤ 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((TaoTrudgianYang2025.bourgainPieceFive σ):EReal) :=
  TaoTrudgianYang2025.zeroDensityExponent_le_bourgain_piece_5 (σ:=σ) hσ hσ1

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_ninthRow
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_tenthRow
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eleventhRow
#print axioms TaoTrudgianYang2025.exponentPair_taoTrudgianYang_firstNew
#print axioms TaoTrudgianYang2025.exponentPair_taoTrudgianYang_secondNew
#print axioms TaoTrudgianYang2025.exponentPair_bourgain_piece_two_input
#print axioms TaoTrudgianYang2025.exponentPair_bourgain_piece_three_input
#print axioms TaoTrudgianYang2025.zeroDensityExponent_le_bourgain_piece_2
#print axioms TaoTrudgianYang2025.zeroDensityExponent_le_bourgain_piece_3
#print axioms TaoTrudgianYang2025.zeroDensityExponent_le_bourgain_piece_4
#print axioms TaoTrudgianYang2025.zeroDensityExponent_le_bourgain_piece_5
