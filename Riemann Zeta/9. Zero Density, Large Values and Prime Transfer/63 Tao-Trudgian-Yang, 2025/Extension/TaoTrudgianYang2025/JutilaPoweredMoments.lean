import TaoTrudgianYang2025.JutilaGram

/-!
# Uniform powered critical-line moments for Jutila's argument

All constants are selected before the physical scale and ordinate set.
The coefficients retain their actual multiplicative factorization counts.
The moment theorem below is an input to, not a proof of, Jutila's
large-values estimate.
-/

open Complex Finset
open scoped BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- A bounded coefficient sequence is controlled by the actual weighted
ordered-difference moment at exactly the same scale. -/
theorem jutila_coefficient_moment_le (N : ℕ) (W : Finset ℝ)
    (a : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ B) :
    (∑ t ∈ W, ∑ u ∈ W, ‖sourceDirichletPoly N a (t-u)‖ ^ 2) ≤
      B ^ 2 * (2 * (N : ℝ)) * heathBrownWeightedMoment N W := by
  have hm := sourceDirichletPoly_differenceMoment_le_of_norm_le N W a (fun _ => B)
    (fun _ _ => hB) ha
  have hpoly (t : ℝ) :
      sourceDirichletPoly N (fun _ => (B : ℂ)) t =
        (B : ℂ) * sourceDirichletPoly N (fun _ => (1 : ℂ)) t := by
    simpa using sourceDirichletPoly_real_smul_coeffs N (fun _ => (1 : ℝ)) B t
  have hsum :
      (∑ t ∈ W, ∑ u ∈ W, ‖sourceDirichletPoly N (fun _ => (B : ℂ)) (t-u)‖ ^ 2) =
        B ^ 2 * (∑ t ∈ W, ∑ u ∈ W,
          ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (t-u)‖ ^ 2) := by
    simp_rw [hpoly, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hB, mul_pow]
    simp_rw [Finset.mul_sum]
  rw [hsum] at hm
  have hn := sourceCoefficientOne_differenceMoment_le_two_mul_weighted N W
  calc
    _ ≤ _ := hm
    _ ≤ B ^ 2 * ((2 * (N : ℝ)) * heathBrownWeightedMoment N W) :=
      mul_le_mul_of_nonneg_left hn (sq_nonneg B)
    _ = _ := by ring

/-- One divisor constant works for every powered scale and every dyadic
piece, rather than being reselected after the physical scale. -/
theorem jutila_powered_coefficients_uniform (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ r < k,
      ∀ m ∈ dyadicInterval (2 ^ r * N ^ k),
        ‖heathBrownPoweredCoeffs N k m‖ ≤
          C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η := by
  obtain ⟨C, hC, hbound⟩ := finitePowCoeff_bound_uniform k η hη
  refine ⟨C, hC, ?_⟩
  intro N hN r hr m hm
  have hsupport := heathBrown_poweredBlock_subset N k r m hr hm
  have hmpos : 0 < m := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  have hnorm := norm_finitePoweredLineCoeffs_le N k m (fun _ => (1 : ℂ))
    (1/2 : ℝ) hN (by norm_num) hsupport
  change ‖heathBrownPoweredCoeffs N k m‖ ≤ _ at hnorm
  have hdiv := hbound N (fun _ => (1 : ℂ)) (by simp) m hmpos
  exact hnorm.trans (hdiv.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg m)
      (by exact_mod_cast (Finset.mem_Ioc.mp hsupport).2) hη.le) hC.le))

/-- The full actual critical-line `2k`-moment, with uniform constants.
Its upper scale is the physical powered support endpoint `(2N)^k`.
The three terms are the proved Heath--Brown moment, not premises. -/
theorem jutila_weighted_power_moment_uniform (k : ℕ) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ), 0 < N → T₀ ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        heathBrownWeightedPowerMoment N k W ≤
          C * (((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ^ 2 * T ^ ε *
            ((W.card : ℝ) ^ 2 + (W.card : ℝ) * (2 ^ k * N ^ k : ℕ) +
              (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ)) := by
  obtain ⟨D, hD, hcoeff⟩ := jutila_powered_coefficients_uniform k hη
  obtain ⟨A, T₀, hA, hT₀, hmoment⟩ := heathBrownWeightedMeanSquare_native ε hε
  let C : ℝ := (k : ℝ) ^ 2 * 2 * (2 : ℝ) ^ k * D ^ 2 * A
  refine ⟨C, T₀, by dsimp [C]; positivity, hT₀, ?_⟩
  intro N T W hN hT hsep hbase
  let U : ℕ := 2 ^ k * N ^ k
  let B : ℝ := (W.card : ℝ) ^ 2 + (W.card : ℝ) * U +
    (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (hT₀.trans hT)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hblock (r : ℕ) (hr : r ∈ Finset.range k) :
      (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly (2 ^ r * N ^ k) (heathBrownPoweredCoeffs N k) (t-u)‖ ^ 2) ≤
      (D * (U : ℝ) ^ η) ^ 2 * (2 * (U : ℝ)) * (A * T ^ ε * B) := by
    have hrk := Finset.mem_range.mp hr
    have hQ : 0 < 2 ^ r * N ^ k := by positivity
    have hQU : 2 ^ r * N ^ k ≤ U := by
      exact Nat.mul_le_mul_right _ (pow_le_pow_right₀ (by omega) hrk.le)
    have hQUr : ((2 ^ r * N ^ k : ℕ) : ℝ) ≤ U := by exact_mod_cast hQU
    have hcoef := hcoeff N hN r hrk
    have hc := jutila_coefficient_moment_le (2 ^ r * N ^ k) W
      (heathBrownPoweredCoeffs N k) (by positivity) hcoef
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
  have hwide := sum_norm_heathBrownPoweredWide_sq_le_blocks N k W
  rw [sum_norm_heathBrownPoweredWide_sq N k W hN hk] at hwide
  have hsum := Finset.sum_le_sum hblock
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hfinal := hwide.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg k))
  have hid : (k : ℝ) *
      ((k : ℝ) * ((D * (U : ℝ) ^ η) ^ 2 * (2 * (U : ℝ)) * (A * T ^ ε * B))) =
      ((N ^ k : ℕ) : ℝ) * (C * ((U : ℝ) ^ η) ^ 2 * T ^ ε * B) := by
    dsimp [C, U]
    push_cast
    ring
  rw [hid] at hfinal
  exact (mul_le_mul_iff_right₀ (by exact_mod_cast pow_pos hN k :
    (0 : ℝ) < (N ^ k : ℕ))).mp hfinal

end TaoTrudgianYang2025
