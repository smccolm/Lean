import TaoTrudgianYang2025.PiecewiseEnvelope

/-!
# Exact certificates for the optimized Bourgain interval table

The eight functions and seven crossover points are copied literally from the
paper. This module proves exact endpoint agreement and exact coverage of the
open interval `(3/4, 1)`; it does not assert the analytic zero-density bound.
-/

namespace TaoTrudgianYang2025

noncomputable def bourgainPieceOne (sigma : ℝ) : ℝ :=
  11 / (12 * (4 * sigma - 3))

noncomputable def bourgainPieceTwo (sigma : ℝ) : ℝ :=
  391 / (2493 * sigma - 2014)

noncomputable def bourgainPieceThree (sigma : ℝ) : ℝ :=
  22232 / (163248 * sigma - 134765)

noncomputable def bourgainPieceFour (sigma : ℝ) : ℝ :=
  356 / (2742 * sigma - 2279)

noncomputable def bourgainPieceFive (sigma : ℝ) : ℝ :=
  2609588 / (20732766 * sigma - 17313767)

noncomputable def bourgainPieceSix (sigma : ℝ) : ℝ :=
  75872 / (9 * (81024 * sigma - 69517))

noncomputable def bourgainPieceSeven (sigma : ℝ) : ℝ :=
  288 / (3616 * sigma - 3197)

noncomputable def bourgainPieceEight (sigma : ℝ) : ℝ :=
  86152 / (1447460 * sigma - 1311509)

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
    bourgainPieceSeven, bourgainPieceEight]

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
