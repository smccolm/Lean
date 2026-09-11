import Tao2026.LargeSieveGlobal
import Tao2026.VinogradovPhase

/-!
# Circle characters for the global large sieve

This file connects the abstract finite analysis and Gram maps to the standard
additive characters at real circle frequencies.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace Tao2026

noncomputable section

variable {A : Type*}

/-- The length-indexed additive-character vector at a real frequency. -/
def circleCharacterVector (alpha : A → ℝ) (a : A) (n : ℕ) : ℂ :=
  standardAdditiveCharacter ((n : ℝ) * alpha a)

@[simp]
theorem circleCharacterVector_normSq
    (alpha : A → ℝ) (a : A) (n : ℕ) :
    Complex.normSq (circleCharacterVector alpha a n) = 1 := by
  rw [Complex.normSq_eq_norm_sq, circleCharacterVector,
    norm_standardAdditiveCharacter]
  norm_num

/-- A Gram entry of circle-character vectors is a character at the frequency
difference. -/
theorem circleCharacterVector_gram_term (alpha : A → ℝ)
    (a b : A) (n : ℕ) :
    starRingEnd ℂ (circleCharacterVector alpha a n) *
        circleCharacterVector alpha b n =
      standardAdditiveCharacter ((n : ℝ) * (alpha b - alpha a)) := by
  rw [circleCharacterVector, circleCharacterVector, starRingEnd_apply,
    show star (standardAdditiveCharacter ((n : ℝ) * alpha a)) =
      conj (standardAdditiveCharacter ((n : ℝ) * alpha a)) by rfl,
    ← standardAdditiveCharacter_neg]
  rw [← standardAdditiveCharacter_add]
  congr 1
  ring

/-- Exact Dirichlet-kernel formula for the finite Gram matrix of circle
characters. -/
theorem finiteGram_circleCharacterVector [Fintype A] (alpha : A → ℝ)
    (L : ℕ) (a b : A) :
    finiteGram (fun a (n : Fin L) => circleCharacterVector alpha a n) a b =
      ∑ n : Fin L,
        standardAdditiveCharacter (((n : ℕ) : ℝ) * (alpha b - alpha a)) := by
  unfold finiteGram
  apply sum_congr rfl
  intro n _
  exact circleCharacterVector_gram_term alpha a b n

/-- The diagonal circle-character Gram entry is exactly the vector length. -/
@[simp]
theorem finiteGram_circleCharacterVector_self [Fintype A]
    (alpha : A → ℝ) (L : ℕ) (a : A) :
    finiteGram (fun a (n : Fin L) => circleCharacterVector alpha a n) a a = L := by
  rw [finiteGram_circleCharacterVector]
  simp [standardAdditiveCharacter]

/-- Character vector indexed by a pair of shifts.  The second shift minus the
first is the frequency used in the Fejér smoothing argument. -/
def circleDifferenceVector {H : ℕ} (alpha : A → ℝ) (a : A)
    (p : Fin H × Fin H) : ℂ :=
  standardAdditiveCharacter
    (((((p.2 : ℕ) : ℤ) - (p.1 : ℕ) : ℤ) : ℝ) * alpha a)

/-- Finite Dirichlet kernel in the project additive-character normalization. -/
def circleDirichletKernel (H : ℕ) (theta : ℝ) : ℂ :=
  ∑ h : Fin H, standardAdditiveCharacter (((h : ℕ) : ℝ) * theta)

/-- Nonnegative Fejér kernel, represented as the squared norm of the finite
Dirichlet kernel. -/
def circleFejerKernel (H : ℕ) (theta : ℝ) : ℝ :=
  Complex.normSq (circleDirichletKernel H theta)

theorem circleFejerKernel_nonneg (H : ℕ) (theta : ℝ) :
    0 ≤ circleFejerKernel H theta :=
  Complex.normSq_nonneg _

theorem circleDifferenceVector_gram_term
    {H : ℕ} (alpha : A → ℝ) (a b : A) (p : Fin H × Fin H) :
    starRingEnd ℂ (circleDifferenceVector alpha a p) *
        circleDifferenceVector alpha b p =
      standardAdditiveCharacter
        (((((p.2 : ℕ) : ℤ) - (p.1 : ℕ) : ℤ) : ℝ) *
          (alpha b - alpha a)) := by
  rw [circleDifferenceVector, circleDifferenceVector,
    starRingEnd_apply,
    show star (standardAdditiveCharacter
        (((((p.2 : ℕ) : ℤ) - (p.1 : ℕ) : ℤ) : ℝ) * alpha a)) =
      conj (standardAdditiveCharacter
        (((((p.2 : ℕ) : ℤ) - (p.1 : ℕ) : ℤ) : ℝ) * alpha a)) by rfl,
    ← standardAdditiveCharacter_neg, ← standardAdditiveCharacter_add]
  congr 1
  ring

/-- The Gram matrix of the shift-difference family is exactly the Fejér
kernel at the corresponding frequency difference. -/
theorem finiteGram_circleDifferenceVector [Fintype A]
    (alpha : A → ℝ) (H : ℕ) (a b : A) :
    finiteGram (fun a (p : Fin H × Fin H) =>
      circleDifferenceVector alpha a p) a b =
      circleFejerKernel H (alpha b - alpha a) := by
  unfold finiteGram circleFejerKernel circleDirichletKernel
  rw [Complex.normSq_eq_conj_mul_self]
  rw [map_sum, sum_mul]
  simp_rw [mul_sum]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro h _
  apply sum_congr rfl
  intro k _
  rw [circleDifferenceVector_gram_term]
  rw [starRingEnd_apply,
    show star (standardAdditiveCharacter
        (((h : ℕ) : ℝ) * (alpha b - alpha a))) =
      conj (standardAdditiveCharacter
        (((h : ℕ) : ℝ) * (alpha b - alpha a))) by rfl,
    ← standardAdditiveCharacter_neg, ← standardAdditiveCharacter_add]
  congr 1
  push_cast
  ring

/-- Embed a target index and an auxiliary shift into a pair of shifts of
length `2L`.  Their difference is the target index. -/
def fejerPairEmbedding (L : ℕ) (p : Fin L × Fin L) :
    Fin (2 * L) × Fin (2 * L) :=
  (⟨p.2, by omega⟩, ⟨p.1 + p.2, by omega⟩)

theorem fejerPairEmbedding_injective (L : ℕ) :
    Function.Injective (fejerPairEmbedding L) := by
  intro p q hpq
  apply Prod.ext
  · have hsum := congrArg (fun x => x.2.val) hpq
    have hshift := congrArg (fun x => x.1.val) hpq
    have hsum' : p.1.val + p.2.val = q.1.val + q.2.val := by
      simpa only [fejerPairEmbedding] using hsum
    have hshift' : p.2.val = q.2.val := by
      simpa only [fejerPairEmbedding] using hshift
    exact Fin.ext (by omega)
  · have hshift := congrArg (fun x => x.1.val) hpq
    have hshift' : p.2.val = q.2.val := by
      simpa only [fejerPairEmbedding] using hshift
    exact Fin.ext hshift'

/-- On the embedded shift pairs, difference synthesis is exactly the original
circle-character synthesis. -/
theorem finiteSynthesis_difference_embedding [Fintype A]
    (alpha : A → ℝ) (z : A → ℂ) (L : ℕ) (p : Fin L × Fin L) :
    finiteSynthesis
        (fun a (q : Fin (2 * L) × Fin (2 * L)) =>
          circleDifferenceVector alpha a q) z
        (fejerPairEmbedding L p) =
      finiteSynthesis
        (fun a (n : Fin L) => circleCharacterVector alpha a n) z p.1 := by
  unfold finiteSynthesis circleDifferenceVector circleCharacterVector
  apply sum_congr rfl
  intro a _
  congr 2
  have hsub :
      (((p.1.val + p.2.val : ℕ) : ℤ) - (p.2.val : ℕ) : ℤ) =
        (p.1.val : ℕ) := by omega
  norm_num [fejerPairEmbedding, hsub]

/-- Fejér smoothing without loss: every original synthesis coordinate occurs
`L` times among the shift differences of length `2L`. -/
theorem mul_circleSynthesis_energy_le_difference_energy [Fintype A]
    (alpha : A → ℝ) (z : A → ℂ) (L : ℕ) :
    (L : ℝ) * ∑ n : Fin L,
        Complex.normSq (finiteSynthesis
          (fun a (n : Fin L) => circleCharacterVector alpha a n) z n) ≤
      ∑ q : Fin (2 * L) × Fin (2 * L),
        Complex.normSq (finiteSynthesis
          (fun a (q : Fin (2 * L) × Fin (2 * L)) =>
            circleDifferenceVector alpha a q) z q) := by
  let e := fejerPairEmbedding L
  let g : (Fin (2 * L) × Fin (2 * L)) → ℝ := fun q =>
    Complex.normSq (finiteSynthesis
      (fun a (q : Fin (2 * L) × Fin (2 * L)) =>
        circleDifferenceVector alpha a q) z q)
  calc
    (L : ℝ) * ∑ n : Fin L,
        Complex.normSq (finiteSynthesis
          (fun a (n : Fin L) => circleCharacterVector alpha a n) z n) =
      ∑ p : Fin L × Fin L, g (e p) := by
        rw [Fintype.sum_prod_type]
        simp_rw [g, e, finiteSynthesis_difference_embedding]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.mul_sum]
    _ = ∑ q ∈ Finset.univ.image e, g q := by
      rw [Finset.sum_image]
      exact (fejerPairEmbedding_injective L).injOn
    _ ≤ ∑ q ∈ (Finset.univ : Finset (Fin (2 * L) × Fin (2 * L))), g q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _
      · intro q _ _
        exact Complex.normSq_nonneg _
    _ = _ := by simp only [g]

theorem norm_finiteGram_circleDifferenceVector [Fintype A]
    (alpha : A → ℝ) (H : ℕ) (a b : A) :
    ‖finiteGram (fun a (p : Fin H × Fin H) =>
      circleDifferenceVector alpha a p) a b‖ =
      circleFejerKernel H (alpha b - alpha a) := by
  rw [finiteGram_circleDifferenceVector, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (circleFejerKernel_nonneg _ _)]

/-- A row and column bound for the Fejér kernel controls the original circle
synthesis energy. -/
theorem circleSynthesis_energy_le_of_fejer_bounds [Fintype A]
    (alpha : A → ℝ) (z : A → ℂ) (L : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b, circleFejerKernel (2 * L) (alpha b - alpha a) ≤
      C * L)
    (hcol : ∀ b, ∑ a, circleFejerKernel (2 * L) (alpha b - alpha a) ≤
      C * L) :
    ∑ n : Fin L, Complex.normSq (finiteSynthesis
        (fun a (n : Fin L) => circleCharacterVector alpha a n) z n) ≤
      C * ∑ a, Complex.normSq (z a) := by
  by_cases hL : L = 0
  · subst L
    simp only [Finset.univ_eq_empty, sum_empty]
    exact mul_nonneg hC (sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  · have hLpos : (0 : ℝ) < L := by positivity
    have hdiff := finiteSynthesis_energy_le_of_gram_bounds
      (fun a (p : Fin (2 * L) × Fin (2 * L)) =>
        circleDifferenceVector alpha a p) z (C * L)
      (fun a => by
        simpa only [norm_finiteGram_circleDifferenceVector] using hrow a)
      (fun b => by
        simpa only [norm_finiteGram_circleDifferenceVector] using hcol b)
    have hlower := mul_circleSynthesis_energy_le_difference_energy alpha z L
    have hmul :
        (L : ℝ) * ∑ n : Fin L, Complex.normSq (finiteSynthesis
          (fun a (n : Fin L) => circleCharacterVector alpha a n) z n) ≤
        (L : ℝ) * (C * ∑ a, Complex.normSq (z a)) := by
      calc
        _ ≤ ∑ q : Fin (2 * L) × Fin (2 * L),
            Complex.normSq (finiteSynthesis
              (fun a (q : Fin (2 * L) × Fin (2 * L)) =>
                circleDifferenceVector alpha a q) z q) := hlower
        _ ≤ (C * L) * ∑ a, Complex.normSq (z a) := hdiff
        _ = _ := by ring
    exact le_of_mul_le_mul_left hmul hLpos

/-- The finite circle large-sieve inequality reduced exactly to row and column
bounds for the Fejér kernel. -/
theorem circleAnalysis_energy_le_of_fejer_bounds [Fintype A]
    {L : ℕ} (alpha : A → ℝ) (f : Fin L → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b, circleFejerKernel (2 * L) (alpha b - alpha a) ≤
      C * L)
    (hcol : ∀ b, ∑ a, circleFejerKernel (2 * L) (alpha b - alpha a) ≤
      C * L) :
    ∑ a, Complex.normSq (finiteAnalysis
        (fun a (n : Fin L) => circleCharacterVector alpha a n) f a) ≤
      C * ∑ n, Complex.normSq (f n) := by
  apply finiteAnalysis_energy_le_of_synthesis_bound _ _ C hC
  intro z
  exact circleSynthesis_energy_le_of_fejer_bounds
    alpha z L C hC hrow hcol

end

end Tao2026
