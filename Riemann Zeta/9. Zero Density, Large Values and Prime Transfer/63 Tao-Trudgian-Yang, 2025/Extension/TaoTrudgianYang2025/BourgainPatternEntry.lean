import TaoTrudgianYang2025.BourgainTraceBins
import TaoTrudgianYang2025.JutilaBinnedPatterns

/-!
# Actual large-value patterns enter the retained-zeta bin bound

The same source-derived subfamily and physical scale from the genuine
Gram entry are used in the reflected trace estimate. No sampling array,
moment estimate or relationship to the source pattern is assumed.
-/

open Finset
open scoped BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Every occupied bin is reflected at its own physical displacement scale. -/
theorem bourgain_spaced_off_diagonal_moment_retained (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∃ A C K L D : ℝ,
      0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ (Q : ℕ) (M : ℕ → ℕ) (T H δ : ℝ) (W : Finset ℝ),
        0 < Q → (∀ j, 0 < M j) → 0 ≤ T → 1 ≤ H → 4 ≤ δ → 4*H ≤ δ →
        IsSeparated δ W → InBaseInterval T W →
        jutilaOffDiagonalMoment cutoff Q W k ≤
          ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
            bourgainTraceBinMajorant q k Q (M j) j T H W A C K L D η := by
  classical
  obtain ⟨A, C, K, L, D, hA, hC, hK, hL, hD, hbin⟩ :=
    bourgain_trace_bin_moment_retained cutoff q k hq hk hη
  refine ⟨A, C, K, L, D, hA, hC, hK, hL, hD, ?_⟩
  intro Q M T H δ W hQ hM hT hH hδ hHδ hsep hbase
  have hsep1 : IsSeparated 1 W := fun x hx y hy hne =>
    (by linarith : (1 : ℝ) ≤ δ).trans (hsep x hx y hy hne)
  rw [jutila_off_diagonal_moment_eq_bins cutoff Q k hsep1 hbase]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hne : (heathBrownDifferenceBin W j).Nonempty
  · have hparams := jutila_spaced_bin_parameters hδ hHδ hsep hne
    exact hbin Q (M j) j T H W hQ (hM j) hparams.1 hT hH hparams.2 hsep1 hbase
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    have hbudget := bourgainMomentBudget_nonneg q (U := (2^k*(M j)^k : ℕ))
      (T := T) W (Nat.cast_nonneg _) (zero_le_one.trans hH)
    unfold bourgainTraceBinMajorant bourgainPrefixMomentMajorant heathBrownReflectionBinError
    positivity

/-- Actual large-value patterns now enter the fully bounded reflection
integral and bin sum. This is an explicit finite-scale estimate, not yet the
optimized Jutila exponent. All constants precede the source pattern. -/
theorem bourgain_binned_pattern_retained (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∃ A C K L D : ℝ,
      0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (δ : ℝ),
        30 ≤ P.scale → 1 < P.V → 0 ≤ P.T → 4 ≤ δ →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          P.ordinates.card ≤ 6 * (2 * Nat.ceil δ + 1) * W.card ∧
          0 < Q ∧ P.N / 2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * P.N ∧
          IsSeparated δ W ∧ InBaseInterval P.T W ∧
          ∀ (M : ℕ → ℕ) (H : ℝ), (∀ j, 0 < M j) → 1 ≤ H → 4*H ≤ δ →
            (W.card : ℝ) * ((P.V-1)/3) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 ∨
              (W.card : ℝ) ^ 2 * ((P.V-1)/3) ^ (4*k) ≤
                (2 * (Q : ℝ)) ^ (2*k) *
                  ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor P.T) + 1),
                    bourgainTraceBinMajorant q k Q (M j) j P.T H W A C K L D η := by
  obtain ⟨A, C, K, L, D, hA, hC, hK, hL, hD, hm⟩ :=
    bourgain_spaced_off_diagonal_moment_retained cutoff q k hq hk hη
  refine ⟨A, C, K, L, D, hA, hC, hK, hL, hD, ?_⟩
  intro P δ hN hV hT hδ
  obtain ⟨W, Q, c, hsub, hcard, hQ, hlow, hhigh, hsep, hbase, _hc, _hlarge, hgram⟩ :=
    P.jutila_spaced_gram_entry cutoff hN hV (by linarith : 0 < δ)
  refine ⟨W, Q, hsub, hcard, hQ, hlow, hhigh, hsep, hbase, ?_⟩
  intro M H hM hH hHδ
  rcases hgram k hk with hsmall | hlarge
  · exact Or.inl hsmall
  right
  exact hlarge.trans (mul_le_mul_of_nonneg_left
    (hm Q M P.T H δ W hQ hM hT hH hδ hHδ hsep hbase) (by positivity))


end TaoTrudgianYang2025
