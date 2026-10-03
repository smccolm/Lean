import TaoTrudgianYang2025.LiteratureDensity
import TaoTrudgianYang2025.CDVMixedDensity
import TaoTrudgianYang2025.RobertSargosExponentPair
import TaoTrudgianYang2025.BourgainImprovedDensity
import TaoTrudgianYang2025.HeathBrownExponentPairs

/-!
The unchanged finite part of the printed best-known density table.
The analytic theorem explicitly excludes the two unresolved Pintz lower
endpoints; this is NOT a source-contract repair or a complete table proof.
The integer tail is a separate existing interior theorem.
-/

noncomputable section
namespace LiteratureTableScratch
open TaoTrudgianYang2025

def printedFiniteDensityTable (σ : ℝ) : ℝ :=
  if σ ≤ 7/10 then 3/(2-σ) else
  if σ < 19/25 then 15/(3+5*σ) else
  if σ < 127/167 then 9/(8*σ-2) else
  if σ < 13/17 then 15/(13*σ-3) else
  if σ < 17/22 then 6/(5*σ-1) else
  if σ < 41/53 then 2/(9*σ-6) else
  if σ < 7/9 then 9/(7*σ-1) else
  if σ < 1867/2347 then 9/(8*(2*σ-1)) else
  if σ < 4/5 then 3/(2*σ) else
  if σ < 7/8 then 3/(2*σ) else
  if σ < 279/314 then 3/(10*σ-7) else
  if σ < 155/174 then 24/(30*σ-11) else
  if σ ≤ 9/10 then 24/(30*σ-11) else
  if σ ≤ 31/34 then 3/(10*σ-7) else
  if σ < 14/15 then 11/(48*σ-36) else
  if σ < 2841/3016 then 391/(2493*σ-2014) else
  if σ < 859/908 then 22232/(163248*σ-134765) else
  if σ < 23/24 then 356/(2742*σ-2279) else
  if σ < 2211487/2274732 then 3/(24*σ-20) else
  if σ < 39/40 then 86152/(1447460*σ-1311509) else
  if σ < 41/42 then 2/(15*σ-12) else
  3/(40*σ-35)

theorem zeroDensityExponent_le_printedFinite_regular {σ : ℝ}
    (hσ : 1/2 ≤ σ) (hσhi : σ < 59/60)
    (h39 : σ ≠ 39/40) (h41 : σ ≠ 41/42) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((printedFiniteDensityTable σ):EReal) := by
  have hσ1 : σ < 1 := by linarith only [hσhi]
  unfold printedFiniteDensityTable
  by_cases h1 : σ ≤ 7/10
  · rw [if_pos h1]
    exact zeroDensityExponent_le_ingham_closed hσ hσ1.le
  rw [if_neg h1]
  by_cases h2 : σ < 19/25
  · rw [if_pos h2]
    exact zeroDensityExponent_le_guthMaynard (by linarith only [h1]) hσ1.le
  rw [if_neg h2]
  by_cases h3 : σ < 127/167
  · rw [if_pos h3]
    exact zeroDensityExponent_le_ivic_six (by linarith only [h2]) hσ1
  rw [if_neg h3]
  by_cases h4 : σ < 13/17
  · rw [if_pos h4]
    exact zeroDensityExponent_le_ivic_five (le_of_not_gt h3) hσ1
  rw [if_neg h4]
  by_cases h5 : σ < 17/22
  · rw [if_pos h5]
    exact zeroDensityExponent_le_ivic_four (le_of_not_gt h4) hσ1
  rw [if_neg h5]
  by_cases h6 : σ < 41/53
  · rw [if_pos h6]
    exact zeroDensityExponent_le_bourgain_improved_lower (le_of_not_gt h5)
      (by linarith only [h6])
  rw [if_neg h6]
  by_cases h7 : σ < 7/9
  · rw [if_pos h7]
    exact zeroDensityExponent_le_ivic_three (le_of_not_gt h6) hσ1
  rw [if_neg h7]
  by_cases h8 : σ < 1867/2347
  · rw [if_pos h8]
    exact zeroDensityExponent_le_bourgain_improved_upper
      (by linarith only [h7]) (by linarith only [h8])
  rw [if_neg h8]
  by_cases h9 : σ < 4/5
  · rw [if_pos h9]
    exact zeroDensityExponent_le_bourgain_literature (le_of_not_gt h8) hσ1
  rw [if_neg h9]
  by_cases h10 : σ < 7/8
  · rw [if_pos h10]
    exact zeroDensityExponent_le_ivic_two (le_of_not_gt h9) hσ1
  rw [if_neg h10]
  by_cases h11 : σ < 279/314
  · rw [if_pos h11]
    exact improved_heathBrown_zeroDensity (by linarith only [h10]) hσ1.le
  rw [if_neg h11]
  by_cases h12 : σ < 155/174
  · rw [if_pos h12]
    exact zeroDensityExponent_le_cdv_ivic (le_of_not_gt h11) (by linarith only [h12])
  rw [if_neg h12]
  by_cases h13 : σ ≤ 9/10
  · rw [if_pos h13]
    exact zeroDensityExponent_le_ivic_nineteenth (le_of_not_gt h12) (by linarith only [h13])
  rw [if_neg h13]
  by_cases h14 : σ ≤ 31/34
  · rw [if_pos h14]
    exact improved_heathBrown_zeroDensity (by linarith only [h13]) hσ1.le
  rw [if_neg h14]
  by_cases h15 : σ < 14/15
  · rw [if_pos h15]
    have hh := exponentPair_eleven_eightyFifths.bourgain_piece_1
      (by linarith only [h14]) hσ1.le
    simpa [bourgainPieceOne,generatedBourgainPiece1,RationalAffineFraction.eval] using hh
  rw [if_neg h15]
  by_cases h16 : σ < 2841/3016
  · rw [if_pos h16]
    by_cases he : σ = 14/15
    · subst σ
      have hh := exponentPair_eleven_eightyFifths.bourgain_piece_1
        (σ:=14/15) (by norm_num) (by norm_num)
      norm_num [bourgainPieceOne,generatedBourgainPiece1,RationalAffineFraction.eval] at hh ⊢
      exact hh
    · have hh := zeroDensityExponent_le_bourgain_piece_2
        (lt_of_le_of_ne (le_of_not_gt h15) (Ne.symm he)) hσ1.le
      simpa [bourgainPieceTwo,generatedBourgainPiece2,RationalAffineFraction.eval] using hh
  rw [if_neg h16]
  by_cases h17 : σ < 859/908
  · rw [if_pos h17]
    by_cases he : σ = 2841/3016
    · subst σ
      have hh := zeroDensityExponent_le_bourgain_piece_2
        (σ:=2841/3016) (by norm_num) (by norm_num)
      norm_num [bourgainPieceTwo,generatedBourgainPiece2,RationalAffineFraction.eval] at hh ⊢
      exact hh
    · have hh := zeroDensityExponent_le_bourgain_piece_3
        (lt_of_le_of_ne (le_of_not_gt h16) (Ne.symm he)) hσ1.le
      simpa [bourgainPieceThree,generatedBourgainPiece3,RationalAffineFraction.eval] using hh
  rw [if_neg h17]
  by_cases h18 : σ < 23/24
  · rw [if_pos h18]
    by_cases he : σ = 859/908
    · subst σ
      have hh := zeroDensityExponent_le_bourgain_piece_3
        (σ:=859/908) (by norm_num) (by norm_num)
      norm_num [bourgainPieceThree,generatedBourgainPiece3,RationalAffineFraction.eval] at hh ⊢
      exact hh
    · have hh := zeroDensityExponent_le_bourgain_piece_4
        (lt_of_le_of_ne (le_of_not_gt h17) (Ne.symm he)) hσ1.le
      simpa [bourgainPieceFour,generatedBourgainPiece4,RationalAffineFraction.eval] using hh
  rw [if_neg h18]
  by_cases h19 : σ < 2211487/2274732
  · rw [if_pos h19]
    exact zeroDensityExponent_le_pintz_first (le_of_not_gt h18) hσ1
  rw [if_neg h19]
  by_cases h20 : σ < 39/40
  · rw [if_pos h20]
    have hh := zeroDensityExponent_le_bourgain_piece_8
      (by linarith only [h19]) hσ1.le
    simpa [bourgainPieceEight,generatedBourgainPiece8,RationalAffineFraction.eval] using hh
  rw [if_neg h20]
  by_cases h21 : σ < 41/42
  · rw [if_pos h21]
    exact zeroDensityExponent_le_pintz_second_interior
      (lt_of_le_of_ne (le_of_not_gt h20) (Ne.symm h39)) hσ1
  rw [if_neg h21]
  exact zeroDensityExponent_le_pintz_third_interior
    (lt_of_le_of_ne (le_of_not_gt h21) (Ne.symm h41)) hσ1

example (σ : ℝ) : printedFiniteDensityTable σ =
    if σ ≤ 7/10 then 3/(2-σ) else
    if σ < 19/25 then 15/(3+5*σ) else
    if σ < 127/167 then 9/(8*σ-2) else
    if σ < 13/17 then 15/(13*σ-3) else
    if σ < 17/22 then 6/(5*σ-1) else
    if σ < 41/53 then 2/(9*σ-6) else
    if σ < 7/9 then 9/(7*σ-1) else
    if σ < 1867/2347 then 9/(8*(2*σ-1)) else
    if σ < 4/5 then 3/(2*σ) else
    if σ < 7/8 then 3/(2*σ) else
    if σ < 279/314 then 3/(10*σ-7) else
    if σ < 155/174 then 24/(30*σ-11) else
    if σ ≤ 9/10 then 24/(30*σ-11) else
    if σ ≤ 31/34 then 3/(10*σ-7) else
    if σ < 14/15 then 11/(48*σ-36) else
    if σ < 2841/3016 then 391/(2493*σ-2014) else
    if σ < 859/908 then 22232/(163248*σ-134765) else
    if σ < 23/24 then 356/(2742*σ-2279) else
    if σ < 2211487/2274732 then 3/(24*σ-20) else
    if σ < 39/40 then 86152/(1447460*σ-1311509) else
    if σ < 41/42 then 2/(15*σ-12) else
    3/(40*σ-35) := rfl

example {σ : ℝ} (hσ : 1/2 ≤ σ) (hσhi : σ < 59/60)
    (h39 : σ ≠ 39/40) (h41 : σ ≠ 41/42) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((printedFiniteDensityTable σ):EReal) :=
  zeroDensityExponent_le_printedFinite_regular hσ hσhi h39 h41

example : TaoTrudgianYang2025.zeroDensityExponent (1/2) ≤
    ((printedFiniteDensityTable (1/2)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (7/10) ≤
    ((printedFiniteDensityTable (7/10)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (19/25) ≤
    ((printedFiniteDensityTable (19/25)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (127/167) ≤
    ((printedFiniteDensityTable (127/167)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (13/17) ≤
    ((printedFiniteDensityTable (13/17)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (17/22) ≤
    ((printedFiniteDensityTable (17/22)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (41/53) ≤
    ((printedFiniteDensityTable (41/53)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (7/9) ≤
    ((printedFiniteDensityTable (7/9)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (1867/2347) ≤
    ((printedFiniteDensityTable (1867/2347)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (4/5) ≤
    ((printedFiniteDensityTable (4/5)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (7/8) ≤
    ((printedFiniteDensityTable (7/8)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (279/314) ≤
    ((printedFiniteDensityTable (279/314)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (155/174) ≤
    ((printedFiniteDensityTable (155/174)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (9/10) ≤
    ((printedFiniteDensityTable (9/10)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (31/34) ≤
    ((printedFiniteDensityTable (31/34)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (14/15) ≤
    ((printedFiniteDensityTable (14/15)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (2841/3016) ≤
    ((printedFiniteDensityTable (2841/3016)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (859/908) ≤
    ((printedFiniteDensityTable (859/908)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (23/24) ≤
    ((printedFiniteDensityTable (23/24)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (2211487/2274732) ≤
    ((printedFiniteDensityTable (2211487/2274732)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (1951/2000) ≤
    ((printedFiniteDensityTable (1951/2000)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (49/50) ≤
    ((printedFiniteDensityTable (49/50)):EReal) :=
  zeroDensityExponent_le_printedFinite_regular (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

-- These are frozen-table VALUES only, not density theorems at the open obligations.
example : printedFiniteDensityTable (39/40) = 2/(15*(39/40)-12) := by
  norm_num [printedFiniteDensityTable]

example : printedFiniteDensityTable (41/42) = 3/(40*(41/42)-35) := by
  norm_num [printedFiniteDensityTable]

#print axioms printedFiniteDensityTable
#print axioms zeroDensityExponent_le_printedFinite_regular


/-- Every raw integer derivative majorant meets the Pintz plateau in this
height range. This is a limitation of these majorants, not a lower bound
for the true exponential sum or a counterexample to a density theorem. -/
theorem raw_derivative_plateau_all_orders {n r : ℕ}
    (hn : 4 ≤ n) (hr : 3 ≤ r) {τ : ℝ}
    (hτlo : (n:ℝ)-2+2/(n:ℝ) ≤ τ) :
    1-1/((n:ℝ)*((n:ℝ)-1)) ≤ τ*heathBrownBetaBound r (1/τ) := by
  have hnr : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hrr : (3:ℝ) ≤ r := by exact_mod_cast hr
  have hnp : (0:ℝ) < n := by linarith only [hnr]
  have hDn : 0 < (n:ℝ)*((n:ℝ)-1) := mul_pos hnp (by linarith only [hnr])
  have hDr : 0 < (r:ℝ)*((r:ℝ)-1) := mul_pos
    (by linarith only [hrr]) (by linarith only [hrr])
  have hτ : 0 < τ := by
    have hp : 0 < 2/(n:ℝ) := div_pos (by norm_num) hnp
    linarith only [hnr,hτlo,hp]
  rw [heathBrownBetaBound_reciprocal_scale hr hτ (by field_simp)]
  by_cases hnr' : n ≤ r
  · have hnr'' : (n:ℝ) ≤ r := by exact_mod_cast hnr'
    have hD : (n:ℝ)*((n:ℝ)-1) ≤ (r:ℝ)*((r:ℝ)-1) := by
      gcongr
      linarith only [hnr]
    have hi : 1/((r:ℝ)*((r:ℝ)-1)) ≤ 1/((n:ℝ)*((n:ℝ)-1)) :=
      one_div_le_one_div_of_le hDn hD
    have hm : -1/((r:ℝ)*((r:ℝ)-1)) ≤
        max ((τ-(r:ℝ))/((r:ℝ)*((r:ℝ)-1)))
          (max (-1/((r:ℝ)*((r:ℝ)-1))) (-2*τ/((r:ℝ)^2*((r:ℝ)-1)))) :=
      (le_max_left _ _).trans (le_max_right _ _)
    simp only [neg_div] at hm ⊢
    linarith only [hi,hm]
  · have hrn : (r:ℝ) ≤ (n:ℝ)-1 := by
      have hh : r+1 ≤ n := by omega
      have hh' : (r:ℝ)+1 ≤ n := by exact_mod_cast hh
      linarith only [hh']
    have hfactor : 0 ≤ (n:ℝ)*((n:ℝ)-1)-(n:ℝ)-(r:ℝ)+2 := by
      nlinarith only [hnr,hrn,sq_nonneg ((n:ℝ)-2)]
    have hpoly := mul_nonneg
      (show 0 ≤ (n:ℝ)-1-(r:ℝ) by linarith only [hrn]) hfactor
    have ht := (div_le_iff₀ hnp).mp
      (show 2/(n:ℝ) ≤ τ-(n:ℝ)+2 by linarith only [hτlo])
    have hheight := mul_le_mul_of_nonneg_right ht
      (show 0 ≤ (n:ℝ)-1 by linarith only [hnr])
    have hfirst : -1/((n:ℝ)*((n:ℝ)-1)) ≤
        (τ-(r:ℝ))/((r:ℝ)*((r:ℝ)-1)) := by
      apply (div_le_div_iff₀ hDn hDr).mpr
      nlinarith only [hpoly,hheight]
    have hm := le_max_left ((τ-(r:ℝ))/((r:ℝ)*((r:ℝ)-1)))
      (max (-1/((r:ℝ)*((r:ℝ)-1))) (-2*τ/((r:ℝ)^2*((r:ℝ)-1))))
    simp only [neg_div] at hfirst
    linarith only [hfirst,hm]

example {n r : ℕ} (hn : 4 ≤ n) (hr : 3 ≤ r) {τ : ℝ}
    (hτlo : (n:ℝ)-2+2/(n:ℝ) ≤ τ) :
    1-1/((n:ℝ)*((n:ℝ)-1)) ≤ τ*heathBrownBetaBound r (1/τ) :=
  raw_derivative_plateau_all_orders hn hr hτlo

#print axioms raw_derivative_plateau_all_orders

/-- At the first missing endpoint, every raw integer derivative order fails
the strict ordinary Gram gap at a height inside the required interval. -/
theorem first_missing_endpoint_raw_obstruction {r : ℕ} (hr : 3 ≤ r) :
    (15/4:ℝ) ∈ Set.Icc (2*((45*(39/40)-36)/2)/3) ((45*(39/40)-36)/2) ∧
    ¬ ((15/4:ℝ)*heathBrownBetaBound r (4/15) < 2*(39/40)-1) := by
  refine ⟨by norm_num, ?_⟩
  have hh := raw_derivative_plateau_all_orders (n:=5) (by omega) hr
    (τ:=15/4) (by norm_num)
  norm_num at hh ⊢
  exact hh

/-- At the second missing endpoint, the analogous zeta gap fails for every
raw integer derivative order inside the required zeta height interval. -/
theorem second_missing_endpoint_raw_obstruction {r : ℕ} (hr : 3 ≤ r) :
    (16/3:ℝ) ∈ Set.Ico 2 (4*(40*(41/42)-35)/3) ∧
    ¬ ((16/3:ℝ)*heathBrownBetaBound r (3/16) < 41/42) := by
  refine ⟨by norm_num, ?_⟩
  have hh := raw_derivative_plateau_all_orders (n:=7) (by omega) hr
    (τ:=16/3) (by norm_num)
  norm_num at hh ⊢
  exact hh

/-- The same obstruction occurs at every printed lower endpoint of the
integer tail. This concerns the raw majorant, not the true beta function. -/
theorem tail_lower_endpoint_raw_obstruction {n r : ℕ}
    (hn : 6 ≤ n) (hr : 3 ≤ r) :
    let σ := 1-1/(2*(n:ℝ)*((n:ℝ)-1))
    let τ := (n:ℝ)-1-1/(2*(n:ℝ)*((n:ℝ)-1))
    τ ∈ Set.Icc (2*((n:ℝ)-1)/3) ((n:ℝ)-1) ∧
      ¬ (τ*heathBrownBetaBound r (1/τ) < 2*σ-1) := by
  dsimp only
  have hnr : (6:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith only [hnr]
  have hnm : (0:ℝ) < (n:ℝ)-1 := by linarith only [hnr]
  have hD : 0 < 2*(n:ℝ)*((n:ℝ)-1) := by positivity
  have hDlarge : (2:ℝ) ≤ 2*(n:ℝ)*((n:ℝ)-1) := by
    nlinarith only [hnr, sq_nonneg ((n:ℝ)-1)]
  have ha := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hDlarge
  have ha0 : 0 ≤ 1/(2*(n:ℝ)*((n:ℝ)-1)) := le_of_lt (one_div_pos.mpr hD)
  have hb : 2/(n:ℝ) ≤ 1/2 := (div_le_iff₀ hnp).mpr (by linarith only [hnr])
  have hh := raw_derivative_plateau_all_orders (n:=n) (by omega) hr
    (τ:=(n:ℝ)-1-1/(2*(n:ℝ)*((n:ℝ)-1))) (by linarith only [ha,hb])
  have he : 1-1/((n:ℝ)*((n:ℝ)-1)) =
      2*(1-1/(2*(n:ℝ)*((n:ℝ)-1)))-1 := by
    field_simp
    ring
  rw [he] at hh
  exact ⟨⟨by linarith only [hnr,ha], by linarith only [ha0]⟩, not_lt_of_ge hh⟩

example {r : ℕ} (hr : 3 ≤ r) :
    (15/4:ℝ) ∈ Set.Icc (2*((45*(39/40)-36)/2)/3) ((45*(39/40)-36)/2) ∧
    ¬ ((15/4:ℝ)*heathBrownBetaBound r (4/15) < 2*(39/40)-1) :=
  first_missing_endpoint_raw_obstruction hr

example {r : ℕ} (hr : 3 ≤ r) :
    (16/3:ℝ) ∈ Set.Ico 2 (4*(40*(41/42)-35)/3) ∧
    ¬ ((16/3:ℝ)*heathBrownBetaBound r (3/16) < 41/42) :=
  second_missing_endpoint_raw_obstruction hr

example {n r : ℕ} (hn : 6 ≤ n) (hr : 3 ≤ r) :
    let σ := 1-1/(2*(n:ℝ)*((n:ℝ)-1))
    let τ := (n:ℝ)-1-1/(2*(n:ℝ)*((n:ℝ)-1))
    τ ∈ Set.Icc (2*((n:ℝ)-1)/3) ((n:ℝ)-1) ∧
      ¬ (τ*heathBrownBetaBound r (1/τ) < 2*σ-1) :=
  tail_lower_endpoint_raw_obstruction hn hr

#print axioms first_missing_endpoint_raw_obstruction
#print axioms second_missing_endpoint_raw_obstruction
#print axioms tail_lower_endpoint_raw_obstruction

/-- The half-open tail cells cover the entire printed near-one range.
This is interval selection only; it asserts no analytic endpoint bound. -/
theorem exists_printed_tail_cell {σ : ℝ} (hlo : 59/60 ≤ σ) (hhi : σ < 1) :
    ∃ n : ℕ, 6 ≤ n ∧
      1-1/(2*(n:ℝ)*((n:ℝ)-1)) ≤ σ ∧
      σ < 1-1/(2*(n:ℝ)*((n:ℝ)+1)) := by
  classical
  have hη : 0 < 1-σ := by linarith only [hhi]
  obtain ⟨m, hm⟩ := exists_nat_gt (1/(1-σ))
  have he : ∃ j : ℕ, σ < 1-1/(2*((j:ℝ)+6)*((j:ℝ)+7)) := by
    refine ⟨m, ?_⟩
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hp : 0 < (m:ℝ)+6 := by linarith only [hm0]
    have hd : (m:ℝ)+6 ≤ 2*((m:ℝ)+6)*((m:ℝ)+7) := by
      nlinarith only [hm0, sq_nonneg (m:ℝ)]
    have hinv := one_div_le_one_div_of_le hp hd
    have hsmall : 1/((m:ℝ)+6) < 1-σ := by
      apply (div_lt_iff₀ hp).mpr
      have hh := (div_lt_iff₀ hη).mp hm
      nlinarith only [hh,hη]
    linarith only [hinv,hsmall]
  let j := Nat.find he
  have hj := Nat.find_spec he
  change σ < 1-1/(2*((j:ℝ)+6)*((j:ℝ)+7)) at hj
  refine ⟨j+6, by omega, ?_, ?_⟩
  · cases hj0 : j with
    | zero => norm_num [hj0] at *; exact hlo
    | succ k =>
      have hk : k < Nat.find he := by change k < j; omega
      have hh := le_of_not_gt (Nat.find_min he hk)
      convert hh using 1
      push_cast
      ring
  · convert hj using 1
    push_cast
    ring

/-- Every nonendpoint in the printed integer tail has the exact printed
bound, with its actual interval index chosen rather than assumed. -/
theorem exists_printed_tail_bound_regular {σ : ℝ}
    (hlo : 59/60 ≤ σ) (hhi : σ < 1)
    (hendpoint : ∀ n : ℕ, 6 ≤ n → σ ≠ 1-1/(2*(n:ℝ)*((n:ℝ)-1))) :
    ∃ n : ℕ, 6 ≤ n ∧
      1-1/(2*(n:ℝ)*((n:ℝ)-1)) ≤ σ ∧
      σ < 1-1/(2*(n:ℝ)*((n:ℝ)+1)) ∧
      TaoTrudgianYang2025.zeroDensityExponent σ ≤
        ((3/((n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))):ℝ):EReal) := by
  obtain ⟨n,hn,hleft,hright⟩ := exists_printed_tail_cell hlo hhi
  refine ⟨n,hn,hleft,hright,?_⟩
  exact zeroDensityExponent_le_pintz_tail_interior hn
    (lt_of_le_of_ne hleft (Ne.symm (hendpoint n hn))) hright.le

example {σ : ℝ} (hlo : 59/60 ≤ σ) (hhi : σ < 1) :
    ∃ n : ℕ, 6 ≤ n ∧
      1-1/(2*(n:ℝ)*((n:ℝ)-1)) ≤ σ ∧
      σ < 1-1/(2*(n:ℝ)*((n:ℝ)+1)) :=
  exists_printed_tail_cell hlo hhi

example {σ : ℝ} (hlo : 59/60 ≤ σ) (hhi : σ < 1)
    (hendpoint : ∀ n : ℕ, 6 ≤ n → σ ≠ 1-1/(2*(n:ℝ)*((n:ℝ)-1))) :
    ∃ n : ℕ, 6 ≤ n ∧
      1-1/(2*(n:ℝ)*((n:ℝ)-1)) ≤ σ ∧
      σ < 1-1/(2*(n:ℝ)*((n:ℝ)+1)) ∧
      TaoTrudgianYang2025.zeroDensityExponent σ ≤
        ((3/((n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))):ℝ):EReal) :=
  exists_printed_tail_bound_regular hlo hhi hendpoint

#print axioms exists_printed_tail_cell
#print axioms exists_printed_tail_bound_regular

end LiteratureTableScratch
