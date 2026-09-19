import Mathlib.Tactic

/-!
# Exact rational-function sign certificates

This module supplies the exact denominator and sign layer used by every
displayed rational bound in the Tao--Trudgian--Yang paper. Denominators that
are negative in the source display are normalized by negating numerator and
denominator together; no inequality is multiplied by a denominator until the
corresponding strict sign theorem is available.
-/

namespace TaoTrudgianYang2025

/-- A rational function with affine numerator and denominator. -/
structure RationalAffineFraction where
  numeratorSlope : ℚ
  numeratorConstant : ℚ
  denominatorSlope : ℚ
  denominatorConstant : ℚ

namespace RationalAffineFraction

/-- Evaluate a rational affine fraction over the reals. -/
noncomputable def eval (f : RationalAffineFraction) (sigma : ℝ) : ℝ :=
  ((f.numeratorSlope : ℝ) * sigma + f.numeratorConstant) /
    ((f.denominatorSlope : ℝ) * sigma + f.denominatorConstant)

/-- Negate numerator and denominator coefficients simultaneously. -/
def normalizeSign (f : RationalAffineFraction) : RationalAffineFraction where
  numeratorSlope := -f.numeratorSlope
  numeratorConstant := -f.numeratorConstant
  denominatorSlope := -f.denominatorSlope
  denominatorConstant := -f.denominatorConstant

/-- Simultaneous sign normalization preserves the represented function,
including at a zero denominator under Lean's totalized field division. -/
theorem eval_normalizeSign (f : RationalAffineFraction) (sigma : ℝ) :
    f.normalizeSign.eval sigma = f.eval sigma := by
  simp only [normalizeSign, eval, Rat.cast_neg, neg_mul]
  rw [← neg_add, ← neg_add, neg_div_neg_eq]

end RationalAffineFraction

/-- The improved Heath--Brown denominator is positive on its exact range. -/
theorem heathBrownDensity_denominator_pos {sigma : ℝ}
    (hLower : 7 / 10 < sigma) (_hUpper : sigma ≤ 1) :
    0 < 10 * sigma - 7 := by
  nlinarith

/-- Both denominators in the improved Bourgain maximum are positive on the
exact source interval. -/
theorem improvedBourgainDensity_denominators_pos {sigma : ℝ}
    (hLower : 17 / 22 ≤ sigma) (_hUpper : sigma ≤ 4 / 5) :
    0 < 9 * sigma - 6 ∧ 0 < 8 * (2 * sigma - 1) := by
  constructor <;> nlinarith

/-- Denominator sign for optimized Bourgain piece one. -/
theorem optimizedBourgainPieceOne_denominator_pos {sigma : ℝ}
    (hLower : 3 / 4 < sigma) (_hUpper : sigma ≤ 14 / 15) :
    0 < 12 * (4 * sigma - 3) := by
  nlinarith

/-- Denominator sign for optimized Bourgain piece two. -/
theorem optimizedBourgainPieceTwo_denominator_pos {sigma : ℝ}
    (hLower : 14 / 15 < sigma) (_hUpper : sigma ≤ 2841 / 3016) :
    0 < 2493 * sigma - 2014 := by
  nlinarith

/-- Denominator sign for optimized Bourgain piece three. -/
theorem optimizedBourgainPieceThree_denominator_pos {sigma : ℝ}
    (hLower : 2841 / 3016 < sigma) (_hUpper : sigma ≤ 859 / 908) :
    0 < 163248 * sigma - 134765 := by
  nlinarith

/-- Denominator sign for optimized Bourgain piece four. -/
theorem optimizedBourgainPieceFour_denominator_pos {sigma : ℝ}
    (hLower : 859 / 908 < sigma) (_hUpper : sigma ≤ 1625 / 1692) :
    0 < 2742 * sigma - 2279 := by
  nlinarith

/-- Denominator sign for optimized Bourgain piece five. -/
theorem optimizedBourgainPieceFive_denominator_pos {sigma : ℝ}
    (hLower : 1625 / 1692 < sigma)
    (_hUpper : sigma ≤ 3334585 / 3447984) :
    0 < 20732766 * sigma - 17313767 := by
  nlinarith

/-- Denominator sign for optimized Bourgain piece six. -/
theorem optimizedBourgainPieceSix_denominator_pos {sigma : ℝ}
    (hLower : 3334585 / 3447984 < sigma)
    (_hUpper : sigma ≤ 974605 / 1005296) :
    0 < 9 * (81024 * sigma - 69517) := by
  nlinarith

/-- Denominator sign for optimized Bourgain piece seven. -/
theorem optimizedBourgainPieceSeven_denominator_pos {sigma : ℝ}
    (hLower : 974605 / 1005296 < sigma)
    (_hUpper : sigma ≤ 5857 / 6032) :
    0 < 3616 * sigma - 3197 := by
  nlinarith

/-- Denominator sign for optimized Bourgain piece eight. -/
theorem optimizedBourgainPieceEight_denominator_pos {sigma : ℝ}
    (hLower : 5857 / 6032 < sigma) (_hUpper : sigma < 1) :
    0 < 1447460 * sigma - 1311509 := by
  nlinarith

/-- Clause (i) energy denominators are positive. -/
theorem energyClauseOne_denominators_pos {sigma : ℝ}
    (hLower : 3 / 4 ≤ sigma) (_hUpper : sigma ≤ 5 / 6) :
    0 < 2 * (3 * sigma - 1) ∧ 0 < 5 * (4 * sigma - 1) := by
  constructor <;> nlinarith

/-- Clause (ii) energy denominators are positive. -/
theorem energyClauseTwo_denominators_pos {sigma : ℝ}
    (hLower : 7 / 10 ≤ sigma) (_hUpper : sigma ≤ 3 / 4) :
    0 < 2 * (5 * sigma + 3) ∧ 0 < 2 * sigma + 15 := by
  constructor <;> nlinarith

/-- Clause (iii) uses positive normalized versions of the first two source
denominators, whose displayed forms have the opposite sign. -/
theorem energyClauseThree_denominators_pos {sigma : ℝ}
    (hLower : 173 / 229 ≤ sigma) (_hUpper : sigma ≤ 443 / 586) :
    0 < 16 * (125 * sigma - 93) ∧
      0 < 10 * (125 * sigma - 93) ∧
      0 < 20 * (15 * sigma - 2) := by
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Clause (iv) uses the positive normalization of `171 - 230 sigma`. -/
theorem energyClauseFour_denominators_pos {sigma : ℝ}
    (hLower : 443 / 586 ≤ sigma) (_hUpper : sigma ≤ 373 / 493) :
    0 < 5 * (230 * sigma - 171) ∧ 0 < 5 * (55 * sigma - 7) := by
  constructor <;> nlinarith

/-- Clause (v) uses the positive normalization of `26 - 35 sigma`. -/
theorem energyClauseFive_denominators_pos {sigma : ℝ}
    (hLower : 373 / 493 ≤ sigma) (_hUpper : sigma ≤ 103 / 136) :
    0 < 30 * (35 * sigma - 26) ∧
      0 < 85 * sigma - 62 ∧
      0 < 31 * sigma + 2 := by
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Clause (vi) energy denominators are positive. -/
theorem energyClauseSix_denominators_pos {sigma : ℝ}
    (hLower : 103 / 136 ≤ sigma) (_hUpper : sigma ≤ 42 / 55) :
    0 < 7 * (11 * sigma - 8) ∧ 0 < 2 * (5 * sigma + 3) := by
  constructor <;> nlinarith

/-- Clause (vii) energy denominators are positive. -/
theorem energyClauseSeven_denominators_pos {sigma : ℝ}
    (hLower : 42 / 55 ≤ sigma) (_hUpper : sigma ≤ 79 / 103) :
    0 < 6 * (15 * sigma - 11) ∧ 0 < 4 * (4 * sigma - 1) := by
  constructor <;> nlinarith

/-- Clause (viii) energy denominators are positive. -/
theorem energyClauseEight_denominators_pos {sigma : ℝ}
    (hLower : 79 / 103 ≤ sigma) (_hUpper : sigma ≤ 84 / 109) :
    0 < 2 * (37 * sigma - 27) ∧ 0 < 2 * (13 * sigma - 3) := by
  constructor <;> nlinarith

/-- Clause (ix) energy denominators are positive. -/
theorem energyClauseNine_denominators_pos {sigma : ℝ}
    (hLower : 84 / 109 ≤ sigma) (_hUpper : sigma ≤ 5 / 6) :
    0 < 9 * (3 * sigma - 2) ∧ 0 < 5 * (4 * sigma - 1) := by
  constructor <;> nlinarith

end TaoTrudgianYang2025
