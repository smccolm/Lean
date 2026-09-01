import GafniTao.FordLCoordinatePositive

/-!
# Ford Lemma 3.3: the exact `U₀`/`U₁` partition

Ford splits the solutions of (3.2) according to whether at least one of the
`k` polynomial-coordinate pairs is diagonal.  These definitions retain the
literal solution type and this file proves the exact partition identity before
any analytic estimate is applied.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordLHasDiagonal
    {k d T : ℕ} {Ψ : FordIntegerPolynomialSystem k d T}
    {s P Q p q r : ℕ} (v : FordLSolution Ψ s P Q p q r) : Prop :=
  ∃ i : Fin k, v.1.1.1 i = v.1.1.2 i

abbrev FordLDiagonalSolution
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :=
  {v : FordLSolution Ψ s P Q p q r // fordLHasDiagonal v}

abbrev FordLOffDiagonalSolution
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :=
  {v : FordLSolution Ψ s P Q p q r // ¬ fordLHasDiagonal v}

def fordLDiagonalCount
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) : ℕ :=
  Nat.card (FordLDiagonalSolution Ψ s P Q p q r)

def fordLOffDiagonalCount
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) : ℕ :=
  Nat.card (FordLOffDiagonalSolution Ψ s P Q p q r)

noncomputable def fordLSolutionEquivDiagonalSum
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :
    FordLSolution Ψ s P Q p q r ≃
      FordLDiagonalSolution Ψ s P Q p q r ⊕
        FordLOffDiagonalSolution Ψ s P Q p q r := by
  classical
  exact
    { toFun := fun v ↦ if h : fordLHasDiagonal v then Sum.inl ⟨v, h⟩
        else Sum.inr ⟨v, h⟩
      invFun := fun u ↦ u.elim Subtype.val Subtype.val
      left_inv := by
        intro v
        dsimp
        split <;> rfl
      right_inv := by
        intro u
        rcases u with ⟨v, hv⟩ | ⟨v, hv⟩
        · dsimp
          rw [dif_pos hv]
        · dsimp
          rw [dif_neg hv] }

theorem fordLCount_eq_diagonal_add_offDiagonal
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :
    fordLCount Ψ s P Q p q r =
      fordLDiagonalCount Ψ s P Q p q r +
        fordLOffDiagonalCount Ψ s P Q p q r := by
  have hL : fordLCount Ψ s P Q p q r =
      Nat.card (FordLSolution Ψ s P Q p q r) := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [hL, Nat.card_congr
    (fordLSolutionEquivDiagonalSum Ψ s P Q p q r), Nat.card_sum]
  rfl

theorem fordLCount_le_two_mul_max_partition
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :
    fordLCount Ψ s P Q p q r ≤
      2 * max (fordLDiagonalCount Ψ s P Q p q r)
        (fordLOffDiagonalCount Ψ s P Q p q r) := by
  rw [fordLCount_eq_diagonal_add_offDiagonal]
  omega

#print axioms fordLCount_eq_diagonal_add_offDiagonal
#print axioms fordLCount_le_two_mul_max_partition

end

end GafniTao
