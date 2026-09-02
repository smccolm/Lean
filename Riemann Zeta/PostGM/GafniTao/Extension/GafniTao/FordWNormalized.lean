import GafniTao.FordGoodDegrees
import GafniTao.FordLemma51Real

/-!
# Normalizing the `W_j` product in Ford's Lemma 5.1

This file factors the second branch of Ford's displayed `W_j` by its
trivial branch `2 s M₂^d`.  It then isolates the saving supplied by the
central degree band constructed in `FordGoodDegrees`.  All four normalized
terms remain literal; in particular, no unspecified bounded weight is used.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The four literal terms obtained after dividing the second branch of
Ford's `W_j` by `2 s M₂^d`, where `d=j+1`. -/
def fordWNormalizedFactor
    {k : ℕ} (s : ℕ) (M₂ : ℝ) (r M : ℕ) (N t : ℝ) (j : Fin k) : ℝ :=
  let d : ℕ := (j : ℕ) + 1
  1 / ((r : ℝ) * (M : ℝ) ^ d) +
    t / (2 * Real.pi * d * N ^ d) +
    (2 * Real.pi * d * (2 * N) ^ d) /
      ((r : ℝ) * (s : ℝ) * t * (M : ℝ) ^ d * M₂ ^ d) +
    1 / ((s : ℝ) * M₂ ^ d)

theorem fordWNormalizedFactor_nonneg
    {k s r M : ℕ} {M₂ N t : ℝ}
    (hs : 0 < s) (hM₂ : 0 < M₂) (hr : 0 < r) (hM : 0 < M)
    (hN : 0 < N) (ht : 0 < t) (j : Fin k) :
    0 ≤ fordWNormalizedFactor s M₂ r M N t j := by
  unfold fordWNormalizedFactor
  positivity

/-- Exact algebraic normalization of the nontrivial branch of `W_j`. -/
theorem fordWReal_secondBranch_eq_normalized
    {k s r M : ℕ} {M₂ N t : ℝ}
    (hs : 0 < s) (hM₂ : 0 < M₂) (hr : 0 < r) (hM : 0 < M)
    (hN : 0 < N) (ht : 0 < t) (j : Fin k) :
    2 * (s : ℝ) * M₂ ^ ((j : ℕ) + 1) /
          ((r : ℝ) * (M : ℝ) ^ ((j : ℕ) + 1)) +
        (s : ℝ) * t * M₂ ^ ((j : ℕ) + 1) /
          (Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * N ^ ((j : ℕ) + 1)) +
        4 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * (2 * N) ^ ((j : ℕ) + 1) /
          ((r : ℝ) * t * (M : ℝ) ^ ((j : ℕ) + 1)) + 2 =
      (2 * (s : ℝ) * M₂ ^ ((j : ℕ) + 1)) *
        fordWNormalizedFactor s M₂ r M N t j := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  have hd0 : ((((j : ℕ) + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hM₂0 : M₂ ≠ 0 := ne_of_gt hM₂
  have hN0 : N ≠ 0 := ne_of_gt hN
  have ht0 : t ≠ 0 := ne_of_gt ht
  unfold fordWNormalizedFactor
  (field_simp; ring)

theorem fordLemma51WReal_le_base_mul_normalized
    {k s r M : ℕ} {M₂ N t : ℝ}
    (hs : 0 < s) (hM₂ : 0 < M₂) (hr : 0 < r) (hM : 0 < M)
    (hN : 0 < N) (ht : 0 < t) (j : Fin k) :
    fordLemma51WReal s M₂ r M N t j ≤
      (2 * (s : ℝ) * M₂ ^ ((j : ℕ) + 1)) *
        fordWNormalizedFactor s M₂ r M N t j := by
  unfold fordLemma51WReal
  rw [← fordWReal_secondBranch_eq_normalized hs hM₂ hr hM hN ht j]
  exact min_le_right _ _

/-- The complete degree window `1 ≤ d ≤ k` is definitionally represented by
all of `Fin k`; this equivalence makes that reindexing explicit. -/
def fordFullDegreeWindowEquiv (k : ℕ) :
    FordLemma51DegreeWindow k 1 k ≃ Fin k where
  toFun j := j.1
  invFun j := ⟨j, by omega⟩
  left_inv j := by ext; rfl
  right_inv j := rfl

theorem fordFullDegreeWindow_prod
    {k : ℕ} (f : Fin k → ℝ) :
    (∏ j : FordLemma51DegreeWindow k 1 k, f j.1) = ∏ j : Fin k, f j := by
  exact (fordFullDegreeWindowEquiv k).prod_comp f

/-- Product envelope: the trivial branch controls every degree, while the
normalized second branch contributes a factor `q` on every good degree. -/
theorem fordLemma51WReal_full_prod_le
    {k s r M : ℕ} {M₂ N t q : ℝ}
    (hs : 0 < s) (hM₂ : 0 < M₂) (hr : 0 < r) (hM : 0 < M)
    (hN : 0 < N) (ht : 0 < t)
    (hgood : ∀ j ∈ fordGoodDegreeSet k,
      fordWNormalizedFactor s M₂ r M N t j ≤ q) :
    (∏ j : FordLemma51DegreeWindow k 1 k,
        fordLemma51WReal s M₂ r M N t j.1) ≤
      (2 * (s : ℝ)) ^ k * M₂ ^ fordVinogradovKappa k *
        q ^ (fordGoodDegreeSet k).card := by
  rw [fordFullDegreeWindow_prod]
  have hpoint : ∀ j : Fin k,
      fordLemma51WReal s M₂ r M N t j ≤
        (2 * (s : ℝ) * M₂ ^ ((j : ℕ) + 1)) *
          (if j ∈ fordGoodDegreeSet k then q else 1) := by
    intro j
    by_cases hj : j ∈ fordGoodDegreeSet k
    · rw [if_pos hj]
      calc
        fordLemma51WReal s M₂ r M N t j ≤
            (2 * (s : ℝ) * M₂ ^ ((j : ℕ) + 1)) *
              fordWNormalizedFactor s M₂ r M N t j :=
          fordLemma51WReal_le_base_mul_normalized hs hM₂ hr hM hN ht j
        _ ≤ (2 * (s : ℝ) * M₂ ^ ((j : ℕ) + 1)) * q := by
          gcongr
          exact hgood j hj
    · rw [if_neg hj, mul_one]
      unfold fordLemma51WReal
      exact min_le_left _ _
  calc
    ∏ j : Fin k, fordLemma51WReal s M₂ r M N t j ≤
        ∏ j : Fin k,
          ((2 * (s : ℝ) * M₂ ^ ((j : ℕ) + 1)) *
            (if j ∈ fordGoodDegreeSet k then q else 1)) := by
      apply Finset.prod_le_prod
      · intro j _
        exact fordLemma51WReal_nonneg hs hM₂.le hr hM hN ht j
      · intro j _
        exact hpoint j
    _ = (∏ j : Fin k, (2 * (s : ℝ) * M₂ ^ ((j : ℕ) + 1))) *
          ∏ j : Fin k, (if j ∈ fordGoodDegreeSet k then q else 1) := by
      rw [Finset.prod_mul_distrib]
    _ = (2 * (s : ℝ)) ^ k * M₂ ^ fordVinogradovKappa k *
          q ^ (fordGoodDegreeSet k).card := by
      rw [show (∏ j : Fin k, (2 * (s : ℝ) * M₂ ^ ((j : ℕ) + 1))) =
          (2 * (s : ℝ)) ^ k * M₂ ^ fordVinogradovKappa k by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, Finset.prod_pow_eq_pow_sum, sum_fin_degrees]
        rfl]
      rw [show (∏ j : Fin k, (if j ∈ fordGoodDegreeSet k then q else 1)) =
          q ^ (fordGoodDegreeSet k).card by
        rw [← Finset.prod_filter]
        simp [fordGoodDegreeSet]]

#print axioms fordWReal_secondBranch_eq_normalized
#print axioms fordLemma51WReal_full_prod_le

end

end GafniTao
