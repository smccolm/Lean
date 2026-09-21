import TaoTrudgianYang2025.JutilaPatternEntry

/-!
# Jutila's actual-pattern entry into complete smooth reflection

The same reflected prefix length is used for every pair. All three
non-main contributions are retained: the Mellin truncation, omitted
frequencies, and zero mode. The square-root factor uses the actual
ordinate difference, not the minimum separation.
-/

open MeasureTheory
open scoped Interval BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Complete fixed-length reflected upper bound at a nonzero difference. -/
def jutilaReflectionEnvelope (Q M q : ℕ) (H C K L D t : ℝ) : ℝ :=
  (Q : ℝ) * C / Real.sqrt |t| *
      (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
    (Q : ℝ) * K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) +
    (Q : ℝ) * L * (1 + |t|) ^ (q + 2) /
      ((Q : ℝ) ^ (q + 2) * (M : ℝ) ^ q) +
    (Q : ℝ) * D / |t| ^ q

/-- A genuine source-pattern consumer of complete reflection. Constants
are fixed before the pattern, extraction radius, dual cutoff, and power.
This reduces the large-values problem to actual reflected prefix moments;
it does not claim that those moments have already been optimized. -/
theorem jutila_reflected_pattern_entry (cutoff : GMSmoothCutoff)
    (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L D : ℝ, 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (δ : ℝ), 30 ≤ P.scale → 1 < P.V → 4 ≤ δ →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          P.ordinates.card ≤ 6 * (2 * Nat.ceil δ + 1) * W.card ∧
          0 < Q ∧ P.N / 2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * P.N ∧
          IsSeparated δ W ∧ InBaseInterval P.T W ∧
          ∀ (M k : ℕ) (H : ℝ), 0 < M → 0 < k → 1 ≤ H → H ≤ δ/2 →
            (W.card : ℝ) * ((P.V-1)/3) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 ∨
              (W.card : ℝ) ^ 2 * ((P.V-1)/3) ^ (4*k) ≤
                (2 * (Q : ℝ)) ^ (2*k) *
                  ∑ t ∈ W, ∑ u ∈ W, if t = u then 0 else
                    jutilaReflectionEnvelope Q M q H C K L D (u-t) ^ (2*k) := by
  classical
  obtain ⟨C, K, L, D, hC, hK, hL, hD, hreflection⟩ :=
    heathBrownTracePolynomial_reflection_with_length cutoff q hq
  refine ⟨C, K, L, D, hC, hK, hL, hD, ?_⟩
  intro P δ hN hV hδ
  obtain ⟨W, Q, c, hsub, hcard, hQ, hlow, hhigh, hsep, hbase, _hc, _hlarge, hgram⟩ :=
    P.jutila_spaced_gram_entry cutoff hN hV (by linarith : 0 < δ)
  refine ⟨W, Q, hsub, hcard, hQ, hlow, hhigh, hsep, hbase, ?_⟩
  intro M k H hM hk hH hHδ
  rcases hgram k hk with hsmall | hlarge
  · exact Or.inl hsmall
  right
  apply hlarge.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold jutilaOffDiagonalMoment
  apply Finset.sum_le_sum
  intro t ht
  apply Finset.sum_le_sum
  intro u hu
  by_cases heq : t = u
  · simp [heq]
  simp only [if_neg heq]
  have hdist : δ ≤ |u-t| := by
    simpa only [Real.dist_eq] using hsep u hu t ht (Ne.symm heq)
  have hpoint := hreflection (t := u-t) (T₀ := |u-t|)
    (H := H) (Q := Q) (M := M)
    (hδ.trans hdist) le_rfl hH (by linarith) hQ hM
  exact pow_le_pow_left₀ (norm_nonneg _) hpoint (2*k)

end TaoTrudgianYang2025
