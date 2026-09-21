import TaoTrudgianYang2025.JutilaPoweredMoments

/-!
# Uniform powered moments with arbitrary unit coefficients

This is the dyadic input for the reflected-prefix moment in Jutila's
argument. The constants are uniform in the coefficients, including the
translation phases occurring in the reflected polynomial.
-/

open Complex Finset
open scoped BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The actual power of a source polynomial is a wide polynomial at the
powered support, with its factorization coefficients. -/
theorem jutila_source_power_identity (N k : ℕ) (a : ℕ → ℂ) (t : ℝ)
    (hN : 0 < N) (hk : 0 < k) :
    wideDirichletPoly (N ^ k) k (finitePoweredLineCoeffs N k a 0) (-t) =
      sourceDirichletPoly N a t ^ k := by
  have h := wideDirichletPoly_finitePoweredLineCoeffs N k a 0 (-t) hN hk
  simp only [Complex.ofReal_zero, Complex.cpow_zero, one_mul, zero_add,
    Complex.ofReal_neg] at h
  rw [h]
  unfold finitePowPoly sourceDirichletPoly
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  ring

/-- Exact powering followed by Cauchy--Schwarz on its k dyadic pieces.
No coefficient estimate has yet been applied. -/
theorem jutila_source_power_moment_le_blocks (N k : ℕ) (W : Finset ℝ)
    (a : ℕ → ℂ) (hN : 0 < N) (hk : 0 < k) :
    (∑ t ∈ W, ∑ u ∈ W, ‖sourceDirichletPoly N a (t-u)‖ ^ (2*k)) ≤
      (k : ℝ) * ∑ r ∈ Finset.range k, ∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly (2 ^ r * N ^ k)
          (finitePoweredLineCoeffs N k a 0) (t-u)‖ ^ 2 := by
  have hpoint (t : ℝ) :
      ‖sourceDirichletPoly N a t‖ ^ (2*k) ≤
        (k : ℝ) * ∑ r ∈ Finset.range k,
          ‖sourceDirichletPoly (2 ^ r * N ^ k)
            (finitePoweredLineCoeffs N k a 0) t‖ ^ 2 := by
    have hCS := complex_sum_sq_le_card_mul_sum_sq (Finset.range k)
      (fun r => dirichletPoly (2 ^ r * N ^ k)
        (finitePoweredLineCoeffs N k a 0) (-t))
    rw [← wideDirichletPoly_eq_sum_blocks,
      jutila_source_power_identity N k a t hN hk, norm_pow, ← pow_mul] at hCS
    simp_rw [dirichletPoly_neg_eq_sourceDirichletPoly] at hCS
    simpa only [Finset.card_range, mul_comm k 2] using hCS
  calc
    _ ≤ ∑ t ∈ W, ∑ u ∈ W, (k : ℝ) * ∑ r ∈ Finset.range k,
        ‖sourceDirichletPoly (2 ^ r * N ^ k)
          (finitePoweredLineCoeffs N k a 0) (t-u)‖ ^ 2 :=
      Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun u _ => hpoint (t-u)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      calc
        _ = ∑ t ∈ W, ∑ r ∈ Finset.range k, ∑ u ∈ W,
            (k : ℝ) * ‖sourceDirichletPoly (2 ^ r * N ^ k)
              (finitePoweredLineCoeffs N k a 0) (t-u)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]

/-- Uniform arbitrary-coefficient 2k-th ordered-difference moment.
The factor U is retained: these are unweighted polynomials, not
critical-line polynomials. The constants precede N, T, W and a. -/
theorem jutila_source_power_moment_uniform (k : ℕ) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → T₀ ≤ T → IsSeparated 1 W → InBaseInterval T W →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        (∑ t ∈ W, ∑ u ∈ W, ‖sourceDirichletPoly N a (t-u)‖ ^ (2*k)) ≤
          C * (2 ^ k * N ^ k : ℕ) *
            (((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ^ 2 * T ^ ε *
            ((W.card : ℝ) ^ 2 + (W.card : ℝ) * (2 ^ k * N ^ k : ℕ) +
              (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ)) := by
  obtain ⟨D, hD, hcoeff⟩ := finitePowCoeff_bound_uniform k η hη
  obtain ⟨A, T₀, hA, hT₀, hmoment⟩ := heathBrownWeightedMeanSquare_native ε hε
  let C : ℝ := (k : ℝ) ^ 2 * 2 * D ^ 2 * A
  refine ⟨C, T₀, by dsimp [C]; positivity, hT₀, ?_⟩
  intro N T W a hN hT hsep hbase ha
  let U : ℕ := 2 ^ k * N ^ k
  let B : ℝ := (W.card : ℝ) ^ 2 + (W.card : ℝ) * U +
    (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (hT₀.trans hT)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hblock (r : ℕ) (hr : r ∈ Finset.range k) :
      (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly (2 ^ r * N ^ k)
          (finitePoweredLineCoeffs N k a 0) (t-u)‖ ^ 2) ≤
      (D * (U : ℝ) ^ η) ^ 2 * (2 * (U : ℝ)) * (A * T ^ ε * B) := by
    have hrk := Finset.mem_range.mp hr
    have hQ : 0 < 2 ^ r * N ^ k := by positivity
    have hQU : 2 ^ r * N ^ k ≤ U := by
      exact Nat.mul_le_mul_right _ (pow_le_pow_right₀ (by omega) hrk.le)
    have hQUr : ((2 ^ r * N ^ k : ℕ) : ℝ) ≤ U := by exact_mod_cast hQU
    have hcoef : ∀ m ∈ dyadicInterval (2 ^ r * N ^ k),
        ‖finitePoweredLineCoeffs N k a 0 m‖ ≤ D * (U : ℝ) ^ η := by
      intro m hm
      have hsupport := heathBrown_poweredBlock_subset N k r m hrk hm
      have hmpos : 0 < m := by
        have := (Finset.mem_Ioc.mp hm).1
        omega
      exact (norm_finitePoweredLineCoeffs_le N k m a 0 hN le_rfl hsupport).trans
        ((hcoeff N a ha m hmpos).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg m)
            (by exact_mod_cast (Finset.mem_Ioc.mp hsupport).2) hη.le) hD.le))
    have hc := jutila_coefficient_moment_le (2 ^ r * N ^ k) W
      (finitePoweredLineCoeffs N k a 0) (by positivity) hcoef
    have hm := hmoment (2 ^ r * N ^ k) T W hQ hT hsep hbase
    have hm' : heathBrownWeightedMoment (2 ^ r * N ^ k) W ≤ A * T ^ ε * B := by
      apply hm.trans
      dsimp [B]
      gcongr
    calc
      _ ≤ (D * (U : ℝ) ^ η) ^ 2 * (2 * ((2 ^ r * N ^ k : ℕ) : ℝ)) *
          heathBrownWeightedMoment (2 ^ r * N ^ k) W := hc
      _ ≤ (D * (U : ℝ) ^ η) ^ 2 * (2 * ((2 ^ r * N ^ k : ℕ) : ℝ)) *
          (A * T ^ ε * B) := mul_le_mul_of_nonneg_left hm' (by positivity)
      _ ≤ _ := by gcongr
  have hwide := jutila_source_power_moment_le_blocks N k W a hN hk
  have hsum := Finset.sum_le_sum hblock
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hfinal := hwide.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg k))
  convert hfinal using 1
  dsimp [C, B, U]
  ring

end TaoTrudgianYang2025

