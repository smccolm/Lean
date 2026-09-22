import TaoTrudgianYang2025.BourgainPhysicalMain
import TaoTrudgianYang2025.JutilaPhysicalPatterns

/-!
# The actual retained-zeta Gram bound at physical scales

The native source subfamily, scale, near-bin cancellation, fixed dual
length and all three reflection errors are consumed in one theorem.
The zeta-square moment remains an actual term, not a theorem parameter.
-/

open Finset
open scoped BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Near contribution, normalized retained main, and complete reflection errors. -/
def bourgainPhysicalEnvelope (q k Q H : ℕ) (T : ℝ) (W : Finset ℝ)
    (E F A C K L D η : ℝ) : ℝ :=
  (2 : ℝ) ^ (2*k-1) *
    ((W.card : ℝ)^2 *
        (E^(2*k)*(Q : ℝ)^k + ((Q : ℝ)*F/(H : ℝ)^q)^(2*k)) +
      jutilaMomentLoss k H T A 0 η * bourgainPhysicalMain q k Q H T W C +
      (W.card : ℝ)^2 * (heathBrownSharpUniformReflectionError K L D q Q H T)^(2*k))

/-- Actual separation makes the complete near/far sum bounded at source
scales. Reflection errors consume the proved sharp native bound, not a
separately supplied numerical certificate. -/
theorem bourgain_hybrid_sum_le_physical (q k Q H : ℕ) (T δ : ℝ) (W : Finset ℝ)
    {E F A C K L D η : ℝ}
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) (hη : 0 ≤ η)
    (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T)
    (hδ : 4 ≤ δ) (hHδ : 4*(H : ℝ) ≤ δ) (hsep : IsSeparated δ W) :
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      bourgainTraceHybridMajorant q k Q H j T W E F A C K L D η) ≤
      ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) *
        bourgainPhysicalEnvelope q k Q H T W E F A C K L D η := by
  classical
  let N : ℝ := (W.card : ℝ)^2 *
    (E^(2*k)*(Q : ℝ)^k + ((Q : ℝ)*F/(H : ℝ)^q)^(2*k))
  let B : ℝ := jutilaMomentLoss k H T A 0 η * bourgainPhysicalMain q k Q H T W C
  let Z : ℝ := (W.card : ℝ)^2 * (heathBrownSharpUniformReflectionError K L D q Q H T)^(2*k)
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hrem := bourgainMomentRemainder_nonneg q T (Nat.cast_nonneg H) W
  have hB : 0 ≤ B := by dsimp [B, jutilaMomentLoss, bourgainPhysicalMain]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z, heathBrownSharpUniformReflectionError]; positivity
  have hstep (j : ℕ) (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1)) :
      bourgainTraceHybridMajorant q k Q H j T W E F A C K L D η ≤
        (2 : ℝ) ^ (2*k-1) * (N+B+Z) := by
    have hc := jutila_bin_card_le_square W j
    unfold bourgainTraceHybridMajorant
    by_cases hnear : 2 ^ (j+1) ≤ Q
    · rw [if_pos hnear]
      have hn :
          ((heathBrownDifferenceBin W j).card : ℝ) *
            (E^(2*k)*(Q : ℝ)^k + ((Q : ℝ)*F/((2^j : ℕ) : ℝ)^q)^(2*k)) ≤ N := by
        by_cases hne : (heathBrownDifferenceBin W j).Nonempty
        · have hs := (jutila_spaced_bin_parameters hδ hHδ hsep hne).2
          have hscale : (H : ℝ) ≤ ((2^j : ℕ) : ℝ) := by linarith
          dsimp [N]
          gcongr
        · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
          simpa using hN
      calc
        _ = (2 : ℝ) ^ (2*k-1) *
            (((heathBrownDifferenceBin W j).card : ℝ) *
              (E^(2*k)*(Q : ℝ)^k + ((Q : ℝ)*F/((2^j : ℕ) : ℝ)^q)^(2*k))) := by ring
        _ ≤ (2 : ℝ) ^ (2*k-1) * N := mul_le_mul_of_nonneg_left hn (by positivity)
        _ ≤ _ := by gcongr; linarith
    rw [if_neg hnear]
    have hmain := bourgain_reflected_main_le_physical q k Q H j T W
      hA hC hη hQ hH hT hj hnear
    have hz :
        ((heathBrownDifferenceBin W j).card : ℝ) *
          (heathBrownReflectionBinError q Q (heathBrownFixedReflectionLength Q H j) H
            ((2^(j+1) : ℕ) : ℝ) ((2^j : ℕ) : ℝ) K L D)^(2*k) ≤ Z := by
      by_cases hne : (heathBrownDifferenceBin W j).Nonempty
      · have hs := jutila_spaced_bin_parameters hδ hHδ hsep hne
        have hn : 2*H ≤ 2^j := by
          have hr : (2 : ℝ)*H ≤ ((2^j : ℕ) : ℝ) := by linarith [hs.2]
          exact_mod_cast hr
        have he := heathBrownReflectionBinError_fixed_le_sharp_uniform
          K L D q Q H j T hK hL hD hQ hH hj ⟨hs.1, hn⟩ hnear
        have hnonneg : 0 ≤ heathBrownReflectionBinError q Q
            (heathBrownFixedReflectionLength Q H j) H
            ((2^(j+1) : ℕ) : ℝ) ((2^j : ℕ) : ℝ) K L D := by
          unfold heathBrownReflectionBinError
          positivity
        dsimp [Z]
        exact mul_le_mul hc (pow_le_pow_left₀ hnonneg he _) (by positivity) (by positivity)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simpa using hZ
    unfold bourgainTraceBinMajorant
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (add_le_add hmain hz).trans (by dsimp [B]; linarith)
  have hs := Finset.sum_le_sum hstep
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, N, B, Z,
    bourgainPhysicalEnvelope] using hs

/-- The actual source pattern satisfies the physical-scale powered Gram
bound after all displacement bins have been eliminated. This still retains
the explicit losses and errors needed for the eventual optimization. -/
theorem bourgain_physical_pattern_retained (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∃ E F A C K L D : ℝ,
      0 < E ∧ 0 < F ∧ 0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (δ : ℝ),
        30 ≤ P.scale → 1 < P.V → 1 ≤ P.T → 4 ≤ δ →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          P.ordinates.card ≤ 6 * (2 * Nat.ceil δ + 1) * W.card ∧
          0 < Q ∧ P.N / 2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * P.N ∧
          IsSeparated δ W ∧ InBaseInterval P.T W ∧
          ∀ H : ℕ, 0 < H → 4*(H : ℝ) ≤ δ →
            (W.card : ℝ) * ((P.V-1)/3) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 ∨
              (W.card : ℝ) ^ 2 * ((P.V-1)/3) ^ (4*k) ≤
                (2 * (Q : ℝ)) ^ (2*k) *
                  (((Nat.log 2 (Nat.floor P.T) + 1 : ℕ) : ℝ) *
                    bourgainPhysicalEnvelope q k Q H P.T W E F A C K L D η) := by
  obtain ⟨E, F, A, C, K, L, D, hE, hF, hA, hC, hK, hL, hD, hp⟩ :=
    bourgain_hybrid_pattern_retained cutoff q k hq hk hη
  refine ⟨E, F, A, C, K, L, D, hE, hF, hA, hC, hK, hL, hD, ?_⟩
  intro P δ hN hV hT hδ
  obtain ⟨W, Q, hsub, hcard, hQ, hlow, hhigh, hsep, hbase, hbound⟩ := hp P δ hN hV (zero_le_one.trans hT) hδ
  refine ⟨W, Q, hsub, hcard, hQ, hlow, hhigh, hsep, hbase, ?_⟩
  intro H hH hHδ
  rcases hbound H hH hHδ with hsmall | hlarge
  · exact Or.inl hsmall
  right
  exact hlarge.trans (mul_le_mul_of_nonneg_left
    (bourgain_hybrid_sum_le_physical q k Q H P.T δ W hE.le hF.le hA.le hC.le
      hK.le hL.le hD.le hη.le hQ hH hT hδ hHδ hsep) (by positivity))


end TaoTrudgianYang2025
