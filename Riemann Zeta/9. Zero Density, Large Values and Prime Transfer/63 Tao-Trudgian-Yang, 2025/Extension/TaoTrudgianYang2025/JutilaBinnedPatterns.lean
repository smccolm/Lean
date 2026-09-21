import TaoTrudgianYang2025.JutilaTraceBins
import TaoTrudgianYang2025.JutilaPatternEntry

/-!
# Actual-pattern consumer of the powered bin estimates

Separation supplies the reflection hypotheses on every occupied bin.
Every bin may use its own positive dual length, but that length is common
to every ordered pair in that bin. All physical scales stay linked to the
original large-value pattern.
-/

open Finset
open scoped BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- A sufficiently spaced actual pair makes its dyadic bin admissible for
complete reflection. This derives the scale conditions instead of assuming
them independently of the ordinate set. -/
theorem jutila_spaced_bin_parameters {W : Finset ℝ} {δ H : ℝ} {j : ℕ}
    (hδ : 4 ≤ δ) (hHδ : 4*H ≤ δ) (hsep : IsSeparated δ W)
    (hbin : (heathBrownDifferenceBin W j).Nonempty) :
    2 ≤ j ∧ H ≤ ((2 ^ j : ℕ) : ℝ) / 2 := by
  obtain ⟨p, hp⟩ := hbin
  have hoff := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
  have hpW := Finset.mem_product.mp hoff.1
  have hdist : δ ≤ |p.1-p.2| := by
    simpa only [Real.dist_eq] using hsep p.1 hpW.1 p.2 hpW.2 hoff.2
  have hsep1 : IsSeparated 1 W := fun x hx y hy hne =>
    (by linarith : (1 : ℝ) ≤ δ).trans (hsep x hx y hy hne)
  have hb := heathBrownDifferenceBin_bounds hsep1 hp
  constructor
  · by_contra hj
    have hpow : (2 : ℕ) ^ (j+1) ≤ 2 ^ 2 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hupper : ((2 ^ (j+1) : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hpow
    linarith
  · have heq : ((2 ^ (j+1) : ℕ) : ℝ) = 2 * ((2 ^ j : ℕ) : ℝ) := by
      push_cast
      rw [pow_succ]
      ring
    rw [heq] at hb
    linarith

/-- All occupied bins are reflected at their actual physical scale.
Unoccupied bins cause no exceptional case in the final sum. -/
theorem jutila_spaced_off_diagonal_moment_uniform (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ A C K L D T₀ : ℝ,
      0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧ 1 ≤ T₀ ∧
      ∀ (Q : ℕ) (M : ℕ → ℕ) (T H δ : ℝ) (W : Finset ℝ),
        0 < Q → (∀ j, 0 < M j) → T₀ ≤ T → 1 ≤ H → 4 ≤ δ → 4*H ≤ δ →
        IsSeparated δ W → InBaseInterval T W →
        jutilaOffDiagonalMoment cutoff Q W k ≤
          ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
            jutilaTraceBinMajorant q k Q (M j) j T H W A C K L D ε η := by
  classical
  obtain ⟨A, C, K, L, D, T₀, hA, hC, hK, hL, hD, hT₀, hbin⟩ :=
    jutila_trace_bin_moment_uniform cutoff q k hq hk hε hη
  refine ⟨A, C, K, L, D, T₀, hA, hC, hK, hL, hD, hT₀, ?_⟩
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
    have hTp : 0 < T := lt_of_lt_of_le zero_lt_one (hT₀.trans hT)
    have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
    unfold jutilaTraceBinMajorant jutilaPrefixMomentMajorant heathBrownReflectionBinError
    positivity

/-- Actual large-value patterns now enter the fully bounded reflection
integral and bin sum. This is an explicit finite-scale estimate, not yet the
optimized Jutila exponent. All constants precede the source pattern. -/
theorem jutila_binned_pattern_bound (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ A C K L D T₀ : ℝ,
      0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧ 1 ≤ T₀ ∧
      ∀ (P : LargeValuePattern) (δ : ℝ),
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → 4 ≤ δ →
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
                    jutilaTraceBinMajorant q k Q (M j) j P.T H W A C K L D ε η := by
  obtain ⟨A, C, K, L, D, T₀, hA, hC, hK, hL, hD, hT₀, hm⟩ :=
    jutila_spaced_off_diagonal_moment_uniform cutoff q k hq hk hε hη
  refine ⟨A, C, K, L, D, T₀, hA, hC, hK, hL, hD, hT₀, ?_⟩
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

