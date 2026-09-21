import TaoTrudgianYang2025.JutilaGram
import TaoTrudgianYang2025.HeathBrownEnergyFinite
import GuthMaynard.LargeValuesFinal

/-!
# Actual large-value patterns enter Jutila's Gram argument

The three-piece source localization supplies one fixed polynomial and a
subfamily containing at least one third of the source ordinates. The
closed-to-half-open support loss is retained as `(P.V - 1) / 3`.
All physical scales, separation and height bounds remain linked to `P`.
-/

open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- An actual source pattern, not a separately assumed sampling array,
supplies the finite amplified Gram entry at every positive integer power. -/
theorem LargeValuePattern.jutila_gram_entry (P : LargeValuePattern)
    (cutoff : GMSmoothCutoff) (hN : 30 ≤ P.scale) (hV : 1 < P.V) :
    ∃ (W : Finset ℝ) (Q : ℕ) (c : ℕ → ℂ),
      W ⊆ P.reflectedOrdinates ∧ P.ordinates.card ≤ 3 * W.card ∧
      0 < Q ∧ P.N / 2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * P.N ∧
      IsSeparated 1 W ∧ InBaseInterval P.T W ∧
      (∀ n ∈ dyadicInterval Q, ‖c n‖ ≤ 1) ∧
      (∀ t ∈ W, (P.V - 1) / 3 ≤ ‖gmSmoothDirichletPoly cutoff Q c t‖) ∧
      (∀ k : ℕ, 0 < k →
        (W.card : ℝ) * ((P.V - 1) / 3) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 ∨
          (W.card : ℝ) ^ 2 * ((P.V - 1) / 3) ^ (4*k) ≤
            (2 * (Q : ℝ)) ^ (2*k) * jutilaOffDiagonalMoment cutoff Q W k) := by
  have hcoeff : ∀ n ∈ dyadicInterval P.scale, ‖P.reflectedCoeffs n‖ ≤ 1 := by
    intro n hn
    exact P.reflectedCoeffs_one_bounded n
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩)
  obtain ⟨W, Q, c, hsub, hcard, hscale, hc, hlarge, _hmatrix⟩ :=
    source_large_values_localize_to_matrix cutoff hN P.reflectedCoeffs
      P.reflectedOrdinates (P.V - 1) (by linarith) hcoeff P.reflectedHalfOpen_large
  have hQbounds : 0 < Q ∧ P.scale ≤ 2*Q ∧ Q ≤ 2*P.scale := by
    rcases hscale with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · dsimp only [gmSourceLeftScale]
      omega
    · omega
    · dsimp only [gmSourceRightScale]
      omega
  refine ⟨W, Q, c, hsub, ?_, hQbounds.1, ?_, ?_, ?_, ?_, hc, hlarge, ?_⟩
  · simpa only [P.reflectedOrdinates_card] using hcard
  · rw [P.N_eq_scale, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    exact_mod_cast (by omega : P.scale ≤ Q*2)
  · rw [P.N_eq_scale]
    exact_mod_cast hQbounds.2.2
  · intro t ht u hu hne
    exact P.reflectedOrdinates_isSeparated t (hsub ht) u (hsub hu) hne
  · intro t ht
    exact P.reflectedOrdinates_inBaseInterval t (hsub ht)
  · intro k hk
    exact jutila_smooth_amplified_gram cutoff Q W c (by linarith) hc hlarge hk

/-- Reflection needs larger separation. The actual packing loss is kept
explicit and all amplified Gram statements are rebuilt on the subfamily. -/
theorem LargeValuePattern.jutila_spaced_gram_entry (P : LargeValuePattern)
    (cutoff : GMSmoothCutoff) (hN : 30 ≤ P.scale) (hV : 1 < P.V)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (W : Finset ℝ) (Q : ℕ) (c : ℕ → ℂ),
      W ⊆ P.reflectedOrdinates ∧
      P.ordinates.card ≤ 6 * (2 * Nat.ceil δ + 1) * W.card ∧
      0 < Q ∧ P.N / 2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * P.N ∧
      IsSeparated δ W ∧ InBaseInterval P.T W ∧
      (∀ n ∈ dyadicInterval Q, ‖c n‖ ≤ 1) ∧
      (∀ t ∈ W, (P.V - 1) / 3 ≤ ‖gmSmoothDirichletPoly cutoff Q c t‖) ∧
      (∀ k : ℕ, 0 < k →
        (W.card : ℝ) * ((P.V - 1) / 3) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 ∨
          (W.card : ℝ) ^ 2 * ((P.V - 1) / 3) ^ (4*k) ≤
            (2 * (Q : ℝ)) ^ (2*k) * jutilaOffDiagonalMoment cutoff Q W k) := by
  obtain ⟨U, Q, c, hU, hcard, hQ, hlow, hhigh, hsep, hbase, hc, hlarge, _hgram⟩ :=
    P.jutila_gram_entry cutoff hN hV
  obtain ⟨W, hsub, hspaced, hpack⟩ := exists_dilated_separated_subset hδ hsep
  refine ⟨W, Q, c, hsub.trans hU, ?_, hQ, hlow, hhigh, hspaced,
    (fun t ht => hbase t (hsub ht)), hc, (fun t ht => hlarge t (hsub ht)), ?_⟩
  · calc
      P.ordinates.card ≤ 3 * U.card := hcard
      _ ≤ 3 * (2 * (2 * Nat.ceil δ + 1) * W.card) := Nat.mul_le_mul_left _ hpack
      _ = _ := by ring
  · intro k hk
    exact jutila_smooth_amplified_gram cutoff Q W c (by linarith) hc
      (fun t ht => hlarge t (hsub ht)) hk

end TaoTrudgianYang2025
