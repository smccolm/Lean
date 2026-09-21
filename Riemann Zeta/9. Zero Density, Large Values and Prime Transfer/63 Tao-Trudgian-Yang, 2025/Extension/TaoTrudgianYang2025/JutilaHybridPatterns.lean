import TaoTrudgianYang2025.JutilaBinnedPatterns
import GuthMaynard.LargeValuesS2

/-!
# Near/far schedule for Jutila's actual source patterns

Below the stationary scale the complete nonzero Poisson tail has square-
root size. The separate zero mode retains arbitrary-order decay. Above
that scale the reflected prefix uses the native ceiling dual length.
-/

open Finset
open scoped BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Below the first stationary scale, square-root cancellation in the
complete nonzero Poisson tail is combined with the separate zero mode. -/
theorem jutila_near_trace_bin_moment_uniform (cutoff : GMSmoothCutoff)
    (q k : ℕ) :
    ∃ E F : ℝ, 0 < E ∧ 0 < F ∧
      ∀ (Q j : ℕ) (W : Finset ℝ), 0 < Q → IsSeparated 1 W →
        2 ^ (j+1) ≤ Q →
        (∑ p ∈ heathBrownDifferenceBin W j,
          ‖heathBrownTracePolynomial cutoff Q (p.1-p.2)‖ ^ (2*k)) ≤
          (2 : ℝ) ^ (2*k-1) * ((heathBrownDifferenceBin W j).card : ℝ) *
            (E ^ (2*k) * (Q : ℝ) ^ k +
              ((Q : ℝ) * F / ((2 ^ j : ℕ) : ℝ) ^ q) ^ (2*k)) := by
  obtain ⟨E, hE, htail⟩ := exists_norm_gmTraceNonzeroTailAt_le_sqrt_near cutoff
  obtain ⟨F, hF, hzero⟩ := gmTraceZeroMode_separated_bound cutoff q
  refine ⟨E, F, hE, hF, ?_⟩
  intro Q j W hQ hsep hj
  have hpoint (p : ℝ × ℝ) (hp : p ∈ heathBrownDifferenceBin W j) :
      ‖heathBrownTracePolynomial cutoff Q (p.1-p.2)‖ ≤
        E * Real.sqrt Q + (Q : ℝ) * F / ((2 ^ j : ℕ) : ℝ) ^ q := by
    have hb := heathBrownDifferenceBin_bounds hsep hp
    have hu : |p.1-p.2| ≤ (Q : ℝ) := hb.2.le.trans (by exact_mod_cast hj)
    have ht := htail Q (p.1-p.2) hQ hu
    have hz := hzero Q (by positivity : (0 : ℝ) < (2 ^ j : ℕ)) hb.1
    have hs := norm_heathBrownTracePolynomial_le_zero_add_tail cutoff Q hQ (p.1-p.2)
    linarith
  have hpower (p : ℝ × ℝ) (hp : p ∈ heathBrownDifferenceBin W j) :
      ‖heathBrownTracePolynomial cutoff Q (p.1-p.2)‖ ^ (2*k) ≤
        (2 : ℝ) ^ (2*k-1) *
          (E ^ (2*k) * (Q : ℝ) ^ k +
            ((Q : ℝ) * F / ((2 ^ j : ℕ) : ℝ) ^ q) ^ (2*k)) := by
    have hsqrt : (Real.sqrt (Q : ℝ)) ^ (2*k) = (Q : ℝ) ^ k := by
      rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg Q)]
    calc
      _ ≤ (E * Real.sqrt Q + (Q : ℝ) * F / ((2 ^ j : ℕ) : ℝ) ^ q) ^ (2*k) :=
        pow_le_pow_left₀ (norm_nonneg _) (hpoint p hp) _
      _ ≤ _ := by
        simpa only [mul_pow, hsqrt] using (even_two_mul k).add_pow_le
          (a := E * Real.sqrt Q) (b := (Q : ℝ) * F / ((2 ^ j : ℕ) : ℝ) ^ q)
  have hsum := Finset.sum_le_sum hpower
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  convert hsum using 1
  ring

/-- Explicit two-regime schedule. This is only notation for the bounds
proved below: it assumes neither the trace bound nor the Jutila exponent. -/
def jutilaTraceHybridMajorant (q k Q H j : ℕ) (T : ℝ) (W : Finset ℝ)
    (E F A C K L D ε η : ℝ) : ℝ :=
  if 2 ^ (j+1) ≤ Q then
    (2 : ℝ) ^ (2*k-1) * ((heathBrownDifferenceBin W j).card : ℝ) *
      (E ^ (2*k) * (Q : ℝ) ^ k +
        ((Q : ℝ) * F / ((2 ^ j : ℕ) : ℝ) ^ q) ^ (2*k))
  else
    jutilaTraceBinMajorant q k Q (heathBrownFixedReflectionLength Q H j) j
      T H W A C K L D ε η

set_option maxHeartbeats 400000 in
/-- An actual source pattern satisfies the near/far powered Gram bound.
Near bins consume square-root nonzero-tail cancellation; far bins consume
the uniform reflected integrals at the genuine ceiling dual length. -/
theorem jutila_hybrid_pattern_bound (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ E F A C K L D T₀ : ℝ,
      0 < E ∧ 0 < F ∧ 0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧ 1 ≤ T₀ ∧
      ∀ (P : LargeValuePattern) (δ : ℝ),
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → 4 ≤ δ →
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
                    jutilaTraceHybridMajorant q k Q H j P.T W E F A C K L D ε η := by
  classical
  obtain ⟨E, F, hE, hF, hnear⟩ := jutila_near_trace_bin_moment_uniform cutoff q k
  obtain ⟨A, C, K, L, D, T₀, hA, hC, hK, hL, hD, hT₀, hfar⟩ :=
    jutila_trace_bin_moment_uniform cutoff q k hq hk hε hη
  refine ⟨E, F, A, C, K, L, D, T₀, hE, hF, hA, hC, hK, hL, hD, hT₀, ?_⟩
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
  unfold jutilaTraceHybridMajorant
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
    have hTp : 0 < P.T := lt_of_lt_of_le zero_lt_one (hT₀.trans hT)
    unfold jutilaTraceBinMajorant jutilaPrefixMomentMajorant heathBrownReflectionBinError
    positivity

end TaoTrudgianYang2025
