import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Factorial.Basic
import Tao2026.Anatomy

/-!
# Consecutive intervals with unusual anatomy

Definitions here transcribe Tao's Definitions 1.2 and 1.3. The distinction
between unions of interval elements (`badSet`, `veryBadSet`) and right
endpoints (`factorialThreeSet`) is part of the API.
-/

namespace Tao2026

open scoped BigOperators

/-- The finite interval `{N+1, ..., N+H}`. -/
def consecutiveInterval (N H : ℕ) : Finset ℕ := Finset.Ioc N (N + H)

/-- The product `(N+1) ... (N+H)`. -/
def consecutiveProduct (N H : ℕ) : ℕ := ∏ n ∈ consecutiveInterval N H, n

/-- Tao Definition 1.2(i). The option-valued largest prime factor makes the
product `1` case false, as required by the source footnote. -/
def IsBadInterval (N H : ℕ) : Prop :=
  ∃ p : ℕ, largestPrimeFactor (consecutiveProduct N H) = some p ∧
    p ^ 2 ∣ consecutiveProduct N H

/-- Tao Definition 1.2(ii). -/
def IsVeryBadInterval (N H : ℕ) : Prop := Powerful (consecutiveProduct N H)

/-- Tao Definition 1.2(iii). -/
def IsFactorialThreeInterval (N H : ℕ) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ a < N ∧
    squarefreeComponent (consecutiveProduct N H) =
      squarefreeComponent a.factorial

/-- Tao Definition 1.3(i): all naturals contained in a bad interval. -/
def badSet : Set ℕ :=
  {n | ∃ N H : ℕ, n ∈ consecutiveInterval N H ∧ IsBadInterval N H}

/-- Tao Definition 1.3(ii): all naturals contained in a very bad interval. -/
def veryBadSet : Set ℕ :=
  {n | ∃ N H : ℕ, n ∈ consecutiveInterval N H ∧ IsVeryBadInterval N H}

/-- Tao Definition 1.3(iii): right endpoints of type-`F₃` intervals. -/
def factorialThreeSet : Set ℕ :=
  {n | ∃ N H : ℕ, n = N + H ∧ IsFactorialThreeInterval N H}

/-- The one-term bad set `B¹`. -/
def badOneTermSet : Set ℕ :=
  {n | 1 ≤ n ∧ IsBadInterval (n - 1) 1}

/-- The one-term very bad set `VB¹`. -/
def veryBadOneTermSet : Set ℕ :=
  {n | 1 ≤ n ∧ IsVeryBadInterval (n - 1) 1}

/-- The one-term type-`F₃` endpoint set `F₃¹`. -/
def factorialThreeOneTermSet : Set ℕ :=
  {n | ∃ N : ℕ, n = N + 1 ∧ IsFactorialThreeInterval N 1}

/-- A strictly ordered triple solving Tao's factorial-square equation. -/
def IsFactorialSquareTriple (a₁ a₂ a₃ : ℕ) : Prop :=
  1 ≤ a₁ ∧ a₁ < a₂ ∧ a₂ < a₃ ∧
    ∃ m : ℕ, a₁.factorial * a₂.factorial * a₃.factorial = m ^ 2

/-- The finite set counted in Theorem 1.10, represented as nested triples. -/
noncomputable def factorialSquareTriplesUpTo (x : ℕ) : Finset (ℕ × ℕ × ℕ) := by
  classical
  exact
    ((Finset.Icc 1 x).product ((Finset.Icc 1 x).product (Finset.Icc 1 x))).filter
      fun t => IsFactorialSquareTriple t.1 t.2.1 t.2.2

@[simp]
theorem consecutiveInterval_zero (N : ℕ) : consecutiveInterval N 0 = ∅ := by
  simp [consecutiveInterval]

@[simp]
theorem consecutiveProduct_zero (N : ℕ) : consecutiveProduct N 0 = 1 := by
  simp [consecutiveProduct]

@[simp]
theorem consecutiveInterval_one (N : ℕ) : consecutiveInterval N 1 = {N + 1} := by
  ext n
  simp [consecutiveInterval]

@[simp]
theorem consecutiveProduct_one (N : ℕ) : consecutiveProduct N 1 = N + 1 := by
  simp [consecutiveProduct]

theorem not_isBadInterval_zero_length (N : ℕ) : ¬IsBadInterval N 0 := by
  rw [IsBadInterval, consecutiveProduct_zero]
  rintro ⟨p, hp, _⟩
  have hnone : largestPrimeFactor 1 = none :=
    largestPrimeFactor_eq_none_iff.mpr (Or.inr rfl)
  rw [hnone] at hp
  cases hp

theorem badOneTermSet_subset_badSet : badOneTermSet ⊆ badSet := by
  intro n hn
  rcases hn with ⟨hnpos, hbad⟩
  refine ⟨n - 1, 1, ?_, hbad⟩
  simp [consecutiveInterval]
  omega

theorem veryBadOneTermSet_subset_veryBadSet :
    veryBadOneTermSet ⊆ veryBadSet := by
  intro n hn
  rcases hn with ⟨hnpos, hbad⟩
  refine ⟨n - 1, 1, ?_, hbad⟩
  simp [consecutiveInterval]
  omega

theorem factorialThreeOneTermSet_subset_factorialThreeSet :
    factorialThreeOneTermSet ⊆ factorialThreeSet := by
  rintro n ⟨N, rfl, hinterval⟩
  exact ⟨N, 1, rfl, hinterval⟩

end Tao2026
