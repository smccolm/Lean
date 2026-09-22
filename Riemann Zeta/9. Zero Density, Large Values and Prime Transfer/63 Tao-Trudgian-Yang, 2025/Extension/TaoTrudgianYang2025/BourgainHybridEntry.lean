import TaoTrudgianYang2025.BourgainPatternEntry
import TaoTrudgianYang2025.JutilaHybridPatterns

/-!
# Near/far Gram entry retaining the zeta moment

Near bins keep the proved square-root tail and zero mode. Far bins use
the actual ceiling dual length and the new retained-zeta trace bound.
-/

open Finset
open scoped BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Actual near and far alternatives at the native ceiling dual length. -/
def bourgainTraceHybridMajorant (q k Q H j : ℕ) (T : ℝ) (W : Finset ℝ)
    (E F A C K L D η : ℝ) : ℝ :=
  if 2 ^ (j+1) ≤ Q then
    (2 : ℝ) ^ (2*k-1) * ((heathBrownDifferenceBin W j).card : ℝ) *
      (E ^ (2*k) * (Q : ℝ) ^ k +
        ((Q : ℝ) * F / ((2 ^ j : ℕ) : ℝ) ^ q) ^ (2*k))
  else
    bourgainTraceBinMajorant q k Q (heathBrownFixedReflectionLength Q H j) j
      T H W A C K L D η

set_option maxHeartbeats 400000 in
/-- An actual source pattern satisfies the near/far powered Gram bound.
Near bins consume square-root nonzero-tail cancellation; far bins consume
the uniform reflected integrals at the genuine ceiling dual length. -/
theorem bourgain_hybrid_pattern_retained (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∃ E F A C K L D : ℝ,
      0 < E ∧ 0 < F ∧ 0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (δ : ℝ),
        30 ≤ P.scale → 1 < P.V → 0 ≤ P.T → 4 ≤ δ →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          P.ordinates.card ≤ 6 * (2 * Nat.ceil δ + 1) * W.card ∧
          0 < Q ∧ P.N / 2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * P.N ∧
          IsSeparated δ W ∧ InBaseInterval P.T W ∧
          ∀ H : ℕ, 0 < H → 4*(H : ℝ) ≤ δ →
            (W.card : ℝ) * ((P.V-1)/3) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 ∨
              (W.card : ℝ) ^ 2 * ((P.V-1)/3) ^ (4*k) ≤
                (2 * (Q : ℝ)) ^ (2*k) *
                  ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor P.T) + 1),
                    bourgainTraceHybridMajorant q k Q H j P.T W E F A C K L D η := by
  classical
  obtain ⟨E, F, hE, hF, hnear⟩ := jutila_near_trace_bin_moment_uniform cutoff q k
  obtain ⟨A, C, K, L, D, hA, hC, hK, hL, hD, hfar⟩ :=
    bourgain_trace_bin_moment_retained cutoff q k hq hk hη
  refine ⟨E, F, A, C, K, L, D, hE, hF, hA, hC, hK, hL, hD, ?_⟩
  intro P δ hN hV hT hδ
  obtain ⟨W, Q, c, hsub, hcard, hQ, hlow, hhigh, hsep, hbase, _hc, _hlarge, hgram⟩ :=
    P.jutila_spaced_gram_entry cutoff hN hV (by linarith : 0 < δ)
  refine ⟨W, Q, hsub, hcard, hQ, hlow, hhigh, hsep, hbase, ?_⟩
  intro H hH hHδ
  rcases hgram k hk with hsmall | hlarge
  · exact Or.inl hsmall
  right
  apply hlarge.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hsep1 : IsSeparated 1 W := fun x hx y hy hne =>
    (by linarith : (1 : ℝ) ≤ δ).trans (hsep x hx y hy hne)
  rw [jutila_off_diagonal_moment_eq_bins cutoff Q k hsep1 hbase]
  apply Finset.sum_le_sum
  intro j hj
  unfold bourgainTraceHybridMajorant
  by_cases hnearQ : 2 ^ (j+1) ≤ Q
  · rw [if_pos hnearQ]
    exact hnear Q j W hQ hsep1 hnearQ
  rw [if_neg hnearQ]
  by_cases hne : (heathBrownDifferenceBin W j).Nonempty
  · have hparams := jutila_spaced_bin_parameters hδ hHδ hsep hne
    exact hfar Q (heathBrownFixedReflectionLength Q H j) j P.T H W hQ
      (heathBrownFixedReflectionLength_pos Q H j) hparams.1 hT
      (by exact_mod_cast hH) hparams.2 hsep1 hbase
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    have hbudget := bourgainMomentBudget_nonneg q
      (U := (2^k*(heathBrownFixedReflectionLength Q H j)^k : ℕ))
      (T := P.T) W (Nat.cast_nonneg _) (Nat.cast_nonneg H)
    unfold bourgainTraceBinMajorant bourgainPrefixMomentMajorant heathBrownReflectionBinError
    positivity


end TaoTrudgianYang2025
