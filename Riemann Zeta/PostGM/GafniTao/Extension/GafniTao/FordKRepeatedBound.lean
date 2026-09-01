import GafniTao.FordKPowerMoment

/-!
# Ford Lemma 3.2: total repeated-coordinate bound

The two orientations of every unordered repeated pair inject into the full
ordered square.  Combined with the exact cover and fixed-pair Fourier bound,
this yields Ford's `k^2` factor without replacing the singular class by an
unspecified union bound.
-/

open Finset
open scoped BigOperators
open MeasureTheory

namespace GafniTao

noncomputable section

def fordOrientedIndexPairToSquare {k : ℕ} :
    Bool × FordIndexPair k → Fin k × Fin k
  | (false, ij) => (ij.1.1, ij.1.2)
  | (true, ij) => (ij.1.2, ij.1.1)

theorem fordOrientedIndexPairToSquare_injective {k : ℕ} :
    Function.Injective (fordOrientedIndexPairToSquare (k := k)) := by
  rintro ⟨b, ij⟩ ⟨c, uv⟩ h
  cases b <;> cases c
  · simp only [fordOrientedIndexPairToSquare, Prod.mk.injEq] at h
    have hijuv : ij = uv := Subtype.ext (Prod.ext h.1 h.2)
    rw [hijuv]
  · simp only [fordOrientedIndexPairToSquare, Prod.mk.injEq] at h
    have h1 := congrArg Fin.val h.1
    have h2 := congrArg Fin.val h.2
    omega
  · simp only [fordOrientedIndexPairToSquare, Prod.mk.injEq] at h
    have h1 := congrArg Fin.val h.1
    have h2 := congrArg Fin.val h.2
    omega
  · simp only [fordOrientedIndexPairToSquare, Prod.mk.injEq] at h
    have hijuv : ij = uv := Subtype.ext (Prod.ext h.2 h.1)
    rw [hijuv]

theorem two_mul_card_fordIndexPair_le_sq (k : ℕ) :
    2 * Nat.card (FordIndexPair k) ≤ k ^ 2 := by
  have hcard : Nat.card (Bool × FordIndexPair k) ≤
      Nat.card (Fin k × Fin k) :=
    Nat.card_le_card_of_injective _ fordOrientedIndexPairToSquare_injective
  simpa [Nat.card_prod, Nat.card_eq_fintype_card, pow_two] using hcard

theorem fordK_repeated_card_le_k_sq_integral
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    (Nat.card (FordKRepeatedSolution Ψ s P Q q) : ℝ) ≤
      (k : ℝ) ^ 2 * fordKRepeatedIntegral Ψ s P Q q := by
  have hI : 0 ≤ fordKRepeatedIntegral Ψ s P Q q := by
    unfold fordKRepeatedIntegral
    exact integral_nonneg fun _ ↦ by positivity
  have hcover := fordK_repeated_card_le_pair_sum
    (s := s) (P := P) (Q := Q) (q := q) Ψ
  have hcoverR : (Nat.card (FordKRepeatedSolution Ψ s P Q q) : ℝ) ≤
      2 * ∑ ij : FordIndexPair k,
        (Nat.card (FordKLeftRepeatAt Ψ s P Q q ij) : ℝ) := by
    exact_mod_cast hcover
  have hsum : (∑ ij : FordIndexPair k,
      (Nat.card (FordKLeftRepeatAt Ψ s P Q q ij) : ℝ)) ≤
      (Nat.card (FordIndexPair k) : ℝ) *
        fordKRepeatedIntegral Ψ s P Q q := by
    calc
      (∑ ij : FordIndexPair k,
          (Nat.card (FordKLeftRepeatAt Ψ s P Q q ij) : ℝ)) ≤
          ∑ _ij : FordIndexPair k, fordKRepeatedIntegral Ψ s P Q q := by
        exact Finset.sum_le_sum fun ij _ ↦ fordK_left_repeat_card_le_integral Ψ ij
      _ = (Nat.card (FordIndexPair k) : ℝ) *
          fordKRepeatedIntegral Ψ s P Q q := by
        simp [Nat.card_eq_fintype_card]
  have hpairsR : (2 : ℝ) * Nat.card (FordIndexPair k) ≤ (k : ℝ) ^ 2 := by
    exact_mod_cast two_mul_card_fordIndexPair_le_sq k
  calc
    (Nat.card (FordKRepeatedSolution Ψ s P Q q) : ℝ) ≤
        2 * ∑ ij : FordIndexPair k,
          (Nat.card (FordKLeftRepeatAt Ψ s P Q q ij) : ℝ) := hcoverR
    _ ≤ 2 * ((Nat.card (FordIndexPair k) : ℝ) *
          fordKRepeatedIntegral Ψ s P Q q) := by gcongr
    _ = ((2 : ℝ) * Nat.card (FordIndexPair k)) *
          fordKRepeatedIntegral Ψ s P Q q := by ring
    _ ≤ (k : ℝ) ^ 2 * fordKRepeatedIntegral Ψ s P Q q := by gcongr

#print axioms two_mul_card_fordIndexPair_le_sq
#print axioms fordK_repeated_card_le_k_sq_integral

end

end GafniTao
