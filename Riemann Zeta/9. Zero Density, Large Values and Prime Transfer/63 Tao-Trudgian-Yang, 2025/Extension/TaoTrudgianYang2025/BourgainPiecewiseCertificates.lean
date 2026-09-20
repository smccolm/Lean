import TaoTrudgianYang2025.GeneratedCertificates
import TaoTrudgianYang2025.PiecewiseEnvelope

/-!
# Exact certificates for the optimized Bourgain interval table

The eight functions and seven crossover points are copied literally from the
paper. This module proves exact endpoint agreement and exact coverage of the
open interval `(3/4, 1)`; it does not assert the analytic zero-density bound.
-/

namespace TaoTrudgianYang2025

private theorem div_eq_scaled_div (a b c : ℝ) (hc : c ≠ 0) :
    a / b = (c * a) / (c * b) :=
  (mul_div_mul_left a b hc).symm

noncomputable def bourgainPieceOne (sigma : ℝ) : ℝ :=
  generatedBourgainPiece1.bound.eval sigma

noncomputable def bourgainPieceTwo (sigma : ℝ) : ℝ :=
  generatedBourgainPiece2.bound.eval sigma

noncomputable def bourgainPieceThree (sigma : ℝ) : ℝ :=
  generatedBourgainPiece3.bound.eval sigma

noncomputable def bourgainPieceFour (sigma : ℝ) : ℝ :=
  generatedBourgainPiece4.bound.eval sigma

noncomputable def bourgainPieceFive (sigma : ℝ) : ℝ :=
  generatedBourgainPiece5.bound.eval sigma

noncomputable def bourgainPieceSix (sigma : ℝ) : ℝ :=
  generatedBourgainPiece6.bound.eval sigma

noncomputable def bourgainPieceSeven (sigma : ℝ) : ℝ :=
  generatedBourgainPiece7.bound.eval sigma

noncomputable def bourgainPieceEight (sigma : ℝ) : ℝ :=
  generatedBourgainPiece8.bound.eval sigma

/-! The generated normalized fractions are checked against Bourgain's
`4k / (2(1+k)sigma - 1 - ell)` formula inside Lean. -/

theorem bourgainPieceOne_eq_candidateFormula (sigma : ℝ) :
    bourgainPieceOne sigma =
      4 * generatedBourgainPiece1.k /
        (2 * (1 + generatedBourgainPiece1.k) * sigma - 1 -
          generatedBourgainPiece1.ell) := by
  norm_num [bourgainPieceOne, generatedBourgainPiece1,
    RationalAffineFraction.eval]
  convert div_eq_scaled_div 11 (48 * sigma - 36) (4 / 85) (by norm_num) using 1;
    ring

theorem bourgainPieceTwo_eq_candidateFormula (sigma : ℝ) :
    bourgainPieceTwo sigma =
      4 * generatedBourgainPiece2.k /
        (2 * (1 + generatedBourgainPiece2.k) * sigma - 1 -
          generatedBourgainPiece2.ell) := by
  norm_num [bourgainPieceTwo, generatedBourgainPiece2,
    RationalAffineFraction.eval]
  convert div_eq_scaled_div 391 (2493 * sigma - 2014) (4 / 4595)
    (by norm_num) using 1; ring

theorem bourgainPieceThree_eq_candidateFormula (sigma : ℝ) :
    bourgainPieceThree sigma =
      4 * generatedBourgainPiece3.k /
        (2 * (1 + generatedBourgainPiece3.k) * sigma - 1 -
          generatedBourgainPiece3.ell) := by
  norm_num [bourgainPieceThree, generatedBourgainPiece3,
    RationalAffineFraction.eval]
  convert div_eq_scaled_div 22232 (163248 * sigma - 134765) (1 / 76066)
    (by norm_num) using 1; ring

theorem bourgainPieceFour_eq_candidateFormula (sigma : ℝ) :
    bourgainPieceFour sigma =
      4 * generatedBourgainPiece4.k /
        (2 * (1 + generatedBourgainPiece4.k) * sigma - 1 -
          generatedBourgainPiece4.ell) := by
  norm_num [bourgainPieceFour, generatedBourgainPiece4,
    RationalAffineFraction.eval]
  convert div_eq_scaled_div 356 (2742 * sigma - 2279) (1 / 1282)
    (by norm_num) using 1; ring

theorem bourgainPieceFive_eq_candidateFormula (sigma : ℝ) :
    bourgainPieceFive sigma =
      4 * generatedBourgainPiece5.k /
        (2 * (1 + generatedBourgainPiece5.k) * sigma - 1 -
          generatedBourgainPiece5.ell) := by
  norm_num [bourgainPieceFive, generatedBourgainPiece5,
    RationalAffineFraction.eval]
  convert div_eq_scaled_div 2609588 (20732766 * sigma - 17313767)
    (1 / 9713986) (by norm_num) using 1; ring

theorem bourgainPieceSix_eq_candidateFormula (sigma : ℝ) :
    bourgainPieceSix sigma =
      4 * generatedBourgainPiece6.k /
        (2 * (1 + generatedBourgainPiece6.k) * sigma - 1 -
          generatedBourgainPiece6.ell) := by
  norm_num [bourgainPieceSix, generatedBourgainPiece6,
    RationalAffineFraction.eval]
  convert div_eq_scaled_div 75872 (729216 * sigma - 625653) (1 / 345640)
    (by norm_num) using 1; ring

theorem bourgainPieceSeven_eq_candidateFormula (sigma : ℝ) :
    bourgainPieceSeven sigma =
      4 * generatedBourgainPiece7.k /
        (2 * (1 + generatedBourgainPiece7.k) * sigma - 1 -
          generatedBourgainPiece7.ell) := by
  norm_num [bourgainPieceSeven, generatedBourgainPiece7,
    RationalAffineFraction.eval]
  convert div_eq_scaled_div 288 (3616 * sigma - 3197) (1 / 1736)
    (by norm_num) using 1; ring

theorem bourgainPieceEight_eq_candidateFormula (sigma : ℝ) :
    bourgainPieceEight sigma =
      4 * generatedBourgainPiece8.k /
        (2 * (1 + generatedBourgainPiece8.k) * sigma - 1 -
          generatedBourgainPiece8.ell) := by
  norm_num [bourgainPieceEight, generatedBourgainPiece8,
    RationalAffineFraction.eval]
  convert div_eq_scaled_div 86152 (1447460 * sigma - 1311509) (1 / 702192)
    (by norm_num) using 1; ring

/-- Consecutive optimized Bourgain pieces agree at all seven exact rational
crossover points. -/
theorem optimizedBourgain_endpoint_agreement :
    bourgainPieceOne (14 / 15) = bourgainPieceTwo (14 / 15) ∧
    bourgainPieceTwo (2841 / 3016) = bourgainPieceThree (2841 / 3016) ∧
    bourgainPieceThree (859 / 908) = bourgainPieceFour (859 / 908) ∧
    bourgainPieceFour (1625 / 1692) = bourgainPieceFive (1625 / 1692) ∧
    bourgainPieceFive (3334585 / 3447984) =
      bourgainPieceSix (3334585 / 3447984) ∧
    bourgainPieceSix (974605 / 1005296) =
      bourgainPieceSeven (974605 / 1005296) ∧
    bourgainPieceSeven (5857 / 6032) =
      bourgainPieceEight (5857 / 6032) := by
  norm_num [bourgainPieceOne, bourgainPieceTwo, bourgainPieceThree,
    bourgainPieceFour, bourgainPieceFive, bourgainPieceSix,
    bourgainPieceSeven, bourgainPieceEight, generatedBourgainPiece1,
    generatedBourgainPiece2, generatedBourgainPiece3,
    generatedBourgainPiece4, generatedBourgainPiece5,
    generatedBourgainPiece6, generatedBourgainPiece7,
    generatedBourgainPiece8, RationalAffineFraction.eval]

/-- The eight source intervals cover exactly `(3/4, 1)`, with each internal
endpoint owned by the piece on its left. -/
theorem optimizedBourgain_interval_cover :
    Set.Ioc (3 / 4 : ℝ) (14 / 15) ∪
      (Set.Ioc (14 / 15) (2841 / 3016) ∪
      (Set.Ioc (2841 / 3016) (859 / 908) ∪
      (Set.Ioc (859 / 908) (1625 / 1692) ∪
      (Set.Ioc (1625 / 1692) (3334585 / 3447984) ∪
      (Set.Ioc (3334585 / 3447984) (974605 / 1005296) ∪
      (Set.Ioc (974605 / 1005296) (5857 / 6032) ∪
        Set.Ioo (5857 / 6032) 1)))))) =
      Set.Ioo (3 / 4) 1 := by
  ext sigma
  simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioo]
  constructor
  · rintro (h | h | h | h | h | h | h | h) <;>
      constructor <;> norm_num at * <;> linarith
  · intro h
    by_cases h₁ : sigma ≤ (14 / 15 : ℝ)
    · exact Or.inl ⟨h.1, h₁⟩
    by_cases h₂ : sigma ≤ (2841 / 3016 : ℝ)
    · exact Or.inr (Or.inl ⟨lt_of_not_ge h₁, h₂⟩)
    by_cases h₃ : sigma ≤ (859 / 908 : ℝ)
    · exact Or.inr (Or.inr (Or.inl ⟨lt_of_not_ge h₂, h₃⟩))
    by_cases h₄ : sigma ≤ (1625 / 1692 : ℝ)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨lt_of_not_ge h₃, h₄⟩)))
    by_cases h₅ : sigma ≤ (3334585 / 3447984 : ℝ)
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨lt_of_not_ge h₄, h₅⟩))))
    by_cases h₆ : sigma ≤ (974605 / 1005296 : ℝ)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨lt_of_not_ge h₅, h₆⟩)))))
    by_cases h₇ : sigma ≤ (5857 / 6032 : ℝ)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨lt_of_not_ge h₆, h₇⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨lt_of_not_ge h₇, h.2⟩))))))

end TaoTrudgianYang2025
