import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

/-! The explicit Legendre good model for an elliptic curve with integral j.
The specified coordinate change is needed to prove faithfulness of the
realized inertia action, not just potential good reduction. This serves
the positive-characteristic exceptional-fiber census, reverse genus and
good reduction in DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Legendre local model proof.
No Hasse-invariant development or characteristic-zero Hahn series is needed. -/
namespace Dubon2026.SourceEllipticLegendre
noncomputable section
variable {M : Type*} [Field M]
section Val

variable (A : ValuationSubring M)

lemma val_lambda {j l : M} (hj : A.valuation j ≤ 1) (h2 : A.valuation (2 : M) = 1)
    (hjl : j * (l ^ 2 * (l - 1) ^ 2) = 256 * (l ^ 2 - l + 1) ^ 3) :
    A.valuation l = 1 ∧ A.valuation (l - 1) = 1 := by
  have h256 : A.valuation (256 : M) = 1 := by
    rw [show (256 : M) = 2 ^ 8 by norm_num, Valuation.map_pow, h2, one_pow]
  have hv1 : A.valuation (1 : M) = 1 := Valuation.map_one _
  have hvneg1 : A.valuation (-1 : M) = 1 := by rw [Valuation.map_neg, hv1]

  have hle : A.valuation l ≤ 1 := by
    by_contra h
    push Not at h
    have hl0 : 0 < A.valuation l := lt_trans zero_lt_one h
    have hlm1 : A.valuation (l - 1) = A.valuation l := by
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left]
      rwa [hvneg1]
    have hquad : A.valuation (l ^ 2 - l + 1) = A.valuation l ^ 2 := by
      have h1 : A.valuation (-l + 1) < A.valuation (l ^ 2) := by
        rw [Valuation.map_pow]
        refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
        · rw [Valuation.map_neg]
          calc A.valuation l = A.valuation l * 1 := (mul_one _).symm
            _ < A.valuation l * A.valuation l := mul_lt_mul_of_pos_left h hl0
            _ = A.valuation l ^ 2 := (sq _).symm
        · rw [hv1]; exact one_lt_pow₀ h (by norm_num)
      rw [show l ^ 2 - l + 1 = l ^ 2 + (-l + 1) by ring, A.valuation.map_add_eq_of_lt_left h1,
        Valuation.map_pow]
    have hL : A.valuation (j * (l ^ 2 * (l - 1) ^ 2)) ≤ A.valuation l ^ 4 := by
      rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow, hlm1]
      calc A.valuation j * (A.valuation l ^ 2 * A.valuation l ^ 2)
          ≤ 1 * (A.valuation l ^ 2 * A.valuation l ^ 2) := mul_le_mul_left hj _
        _ = A.valuation l ^ 4 := by rw [one_mul, ← pow_add]
    have hR : A.valuation (256 * (l ^ 2 - l + 1) ^ 3) = A.valuation l ^ 6 := by
      rw [Valuation.map_mul, h256, one_mul, Valuation.map_pow, hquad, ← pow_mul]
    rw [hjl, hR] at hL
    have : A.valuation l ^ 4 < A.valuation l ^ 6 := pow_lt_pow_right₀ h (by norm_num)
    exact absurd (lt_of_le_of_lt hL this) (lt_irrefl _)
  have hle1 : A.valuation (l - 1) ≤ 1 := by
    rw [sub_eq_add_neg]
    exact le_trans (Valuation.map_add _ _ _) (max_le hle (le_of_eq hvneg1))

  have hl : A.valuation l = 1 := by
    rcases lt_or_eq_of_le hle with h | h
    · exfalso
      have hquad : A.valuation (l ^ 2 - l + 1) = 1 := by
        have h1 : A.valuation (l ^ 2 - l) < A.valuation (1 : M) := by
          rw [hv1, sub_eq_add_neg]
          refine Valuation.map_add_lt _ ?_ ?_
          · rw [Valuation.map_pow]; exact pow_lt_one₀ zero_le' h (by norm_num)
          · rw [Valuation.map_neg]; exact h
        rw [A.valuation.map_add_eq_of_lt_right h1, hv1]
      have hL : A.valuation (j * (l ^ 2 * (l - 1) ^ 2)) < 1 := by
        rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow]
        calc A.valuation j * (A.valuation l ^ 2 * A.valuation (l - 1) ^ 2)
            ≤ 1 * (A.valuation l ^ 2 * 1) := by
              apply mul_le_mul' hj
              exact mul_le_mul_right (pow_le_one₀ zero_le' hle1) _
          _ = A.valuation l ^ 2 := by rw [one_mul, mul_one]
          _ < 1 := pow_lt_one₀ zero_le' h (by norm_num)
      have hR : A.valuation (256 * (l ^ 2 - l + 1) ^ 3) = 1 := by
        rw [Valuation.map_mul, h256, one_mul, Valuation.map_pow, hquad, one_pow]
      rw [hjl, hR] at hL
      exact lt_irrefl _ hL
    · exact h

  have hl1 : A.valuation (l - 1) = 1 := by
    rcases lt_or_eq_of_le hle1 with h | h
    · exfalso
      have hquad : A.valuation (l ^ 2 - l + 1) = 1 := by
        have h1 : A.valuation ((l - 1) ^ 2 + (l - 1)) < A.valuation (1 : M) := by
          rw [hv1]
          refine Valuation.map_add_lt _ ?_ h
          rw [Valuation.map_pow]; exact pow_lt_one₀ zero_le' h (by norm_num)
        rw [show l ^ 2 - l + 1 = ((l - 1) ^ 2 + (l - 1)) + 1 by ring,
          A.valuation.map_add_eq_of_lt_right h1, hv1]
      have hL : A.valuation (j * (l ^ 2 * (l - 1) ^ 2)) < 1 := by
        rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow, hl, one_pow,
          one_mul]
        calc A.valuation j * A.valuation (l - 1) ^ 2 ≤ 1 * A.valuation (l - 1) ^ 2 :=
              mul_le_mul_left hj _
          _ = A.valuation (l - 1) ^ 2 := one_mul _
          _ < 1 := pow_lt_one₀ zero_le' h (by norm_num)
      have hR : A.valuation (256 * (l ^ 2 - l + 1) ^ 3) = 1 := by
        rw [Valuation.map_mul, h256, one_mul, Valuation.map_pow, hquad, one_pow]
      rw [hjl, hR] at hL
      exact lt_irrefl _ hL
    · exact h
  exact ⟨hl, hl1⟩

end Val


end
end Dubon2026.SourceEllipticLegendre
