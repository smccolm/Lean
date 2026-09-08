import Mathlib.Data.Nat.Sqrt
import Tao2026.FactorialIntervals

/-!
# One-term type-F₃ endpoints

This file records the elementary lower-bound side of Tao's display `f31`.
It first identifies the one-term endpoint condition with equality of the
squarefree components of `n` and a smaller factorial, then with an actual
square multiple.  Taking the factorial index `a = 1` embeds every square
larger than one into `F₃¹`.
-/

namespace Tao2026

/-- Literal source characterization of the one-term set `F₃¹`. -/
theorem mem_factorialThreeOneTermSet_iff {n : ℕ} :
    n ∈ factorialThreeOneTermSet ↔
      ∃ a : ℕ, 1 ≤ a ∧ a < n - 1 ∧
        squarefreeComponent n = squarefreeComponent a.factorial := by
  constructor
  · rintro ⟨N, rfl, hinterval⟩
    rcases hinterval with ⟨_, a, ha, haN, hcomponents⟩
    refine ⟨a, ha, ?_, ?_⟩
    · simpa using haN
    · simpa using hcomponents
  · rintro ⟨a, ha, han, hcomponents⟩
    have hn : n = (n - 1) + 1 := by omega
    refine ⟨n - 1, hn, ?_⟩
    refine ⟨by omega, a, ha, han, ?_⟩
    have hsum : (n - 1) + 1 = n := by omega
    simpa only [consecutiveProduct_one, hsum] using hcomponents

/-- A one-term endpoint is exactly a square multiple of the squarefree
component of a sufficiently smaller factorial. -/
theorem mem_factorialThreeOneTermSet_iff_exists_sq_mul {n : ℕ} :
    n ∈ factorialThreeOneTermSet ↔
      ∃ a r : ℕ, 1 ≤ a ∧ a < n - 1 ∧
        n = r ^ 2 * squarefreeComponent a.factorial := by
  constructor
  · intro hn
    obtain ⟨a, ha, han, hcomponents⟩ :=
      mem_factorialThreeOneTermSet_iff.mp hn
    have hnpos : 0 < n := by omega
    obtain ⟨r, hr⟩ := exists_sq_mul_squarefreeComponent hnpos
    exact ⟨a, r, ha, han, by rw [← hcomponents]; exact hr.symm⟩
  · rintro ⟨a, r, ha, han, hn⟩
    have hnpos : 0 < n := by omega
    have hcomponent : squarefreeComponent n =
        squarefreeComponent a.factorial := by
      symm
      exact eq_squarefreeComponent_of_sq_mul hnpos
        (squarefree_squarefreeComponent a.factorial) hn.symm
    exact mem_factorialThreeOneTermSet_iff.mpr ⟨a, ha, han, hcomponent⟩

/-- Every square `q² > 1` belongs to `F₃¹`, by taking the factorial index
`a = 1`. -/
theorem square_mem_factorialThreeOneTermSet {q : ℕ} (hq : 2 ≤ q) :
    q ^ 2 ∈ factorialThreeOneTermSet := by
  apply mem_factorialThreeOneTermSet_iff_exists_sq_mul.mpr
  refine ⟨1, q, by omega, ?_, ?_⟩
  · have hqSq : 4 ≤ q ^ 2 := by nlinarith
    omega
  · simp

/-- The distinct nontrivial squares not exceeding `x`. -/
noncomputable def nontrivialSquaresUpTo (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 2 (Nat.sqrt x)).image fun q => q ^ 2

theorem card_nontrivialSquaresUpTo (x : ℕ) :
    (nontrivialSquaresUpTo x).card = Nat.sqrt x - 1 := by
  classical
  rw [nontrivialSquaresUpTo,
    Finset.card_image_of_injective _ (fun _ _ h =>
      Nat.pow_left_injective (by decide : 2 ≠ 0) h)]
  simp [Nat.card_Icc]

/-- All nontrivial squares up to `x` are one-term `F₃` endpoints up to `x`. -/
theorem nontrivialSquaresUpTo_subset_factorialThreeNumbersUpTo (x : ℕ) :
    nontrivialSquaresUpTo x ⊆ factorialThreeNumbersUpTo x := by
  classical
  intro n hn
  rw [nontrivialSquaresUpTo, Finset.mem_image] at hn
  obtain ⟨q, hqRange, rfl⟩ := hn
  have hqBounds : 2 ≤ q ∧ q ≤ Nat.sqrt x := Finset.mem_Icc.mp hqRange
  apply mem_factorialThreeNumbersUpTo.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by nlinarith [hqBounds.1], ?_⟩,
    factorialThreeOneTermSet_subset_factorialThreeSet
      (square_mem_factorialThreeOneTermSet hqBounds.1)⟩
  exact le_trans (Nat.pow_le_pow_left hqBounds.2 2) (Nat.sqrt_le' x)

/-- The square family already lies in the one-term subset on the same finite
range, which is the precise lower-bound observation preceding display `f31`. -/
theorem nontrivialSquaresUpTo_mem_factorialThreeOneTerm {x n : ℕ}
    (hn : n ∈ nontrivialSquaresUpTo x) :
    n ∈ Finset.Icc 1 x ∧ n ∈ factorialThreeOneTermSet := by
  classical
  rw [nontrivialSquaresUpTo, Finset.mem_image] at hn
  obtain ⟨q, hqRange, rfl⟩ := hn
  have hqBounds : 2 ≤ q ∧ q ≤ Nat.sqrt x := Finset.mem_Icc.mp hqRange
  refine ⟨Finset.mem_Icc.mpr ⟨by nlinarith [hqBounds.1], ?_⟩,
    square_mem_factorialThreeOneTermSet hqBounds.1⟩
  exact le_trans (Nat.pow_le_pow_left hqBounds.2 2) (Nat.sqrt_le' x)

/-- The source-faithful unconditional square-family lower bound for `F₃¹`. -/
theorem sqrt_sub_one_le_factorialThreeOneTermCount (x : ℕ) :
    Nat.sqrt x - 1 ≤ factorialThreeOneTermCount x := by
  classical
  rw [← card_nontrivialSquaresUpTo]
  unfold factorialThreeOneTermCount countUpTo
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter]
  exact nontrivialSquaresUpTo_mem_factorialThreeOneTerm hn

/-- The unconditional square-family lower bound for `F₃`. -/
theorem sqrt_sub_one_le_factorialThreeCount (x : ℕ) :
    Nat.sqrt x - 1 ≤ factorialThreeCount x := by
  exact le_trans (sqrt_sub_one_le_factorialThreeOneTermCount x)
    (factorialThreeOneTermCount_le_factorialThreeCount x)

/-- An explicit factorial-square triple supplied by every nontrivial square:
`1! (q²-1)! (q²)! = (q (q²-1)!)²`. -/
theorem square_factorialSquareTriple {q : ℕ} (hq : 2 ≤ q) :
    IsFactorialSquareTriple 1 (q ^ 2 - 1) (q ^ 2) := by
  have hqSq : 4 ≤ q ^ 2 := by nlinarith
  refine ⟨by omega, by omega, by omega, q * (q ^ 2 - 1).factorial, ?_⟩
  have hsucc : q ^ 2 - 1 + 1 = q ^ 2 := by omega
  rw [show (1 : ℕ).factorial = 1 by simp, one_mul, ← hsucc,
    Nat.factorial_succ]
  have hpred : q ^ 2 - 1 + 1 - 1 = q ^ 2 - 1 := by omega
  rw [hpred, hsucc]
  ring

/-- Consequently the factorial-square triple count already has the source's
elementary square-root lower family, before any analytic upper bound. -/
theorem sqrt_sub_one_le_factorialSquareTripleCount (x : ℕ) :
    Nat.sqrt x - 1 ≤ factorialSquareTripleCount x :=
  le_trans (sqrt_sub_one_le_factorialThreeCount x)
    (factorialThreeCount_le_factorialSquareTripleCount x)

end Tao2026
