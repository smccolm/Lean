import Tao2026.SmoothNumberSaddleOuterShell

/-!
# Adaptive outer-frequency prime shell

This module selects the dyadic prime scale
`ceil (exp (pi / t))` for an outer Perron frequency `t`.  Elementary ceiling
and logarithm estimates put that scale's prime phases inside the same
nonpositive-cosine window as the first outer shell.  A sufficiently large
Chebyshev--PNT threshold then gives an explicit cosine-loss lower bound on
this movable block whenever it lies below `y`.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval Chebyshev

namespace Tao2026

noncomputable section

def smoothSaddleOuterPrimeScale (t : ℝ) : ℕ :=
  Nat.ceil (Real.exp (Real.pi / t))

theorem exp_pi_div_le_smoothSaddleOuterPrimeScale (t : ℝ) :
    Real.exp (Real.pi / t) ≤ (smoothSaddleOuterPrimeScale t : ℝ) := by
  exact Nat.le_ceil _

theorem smoothSaddleOuterPrimeScale_lt_exp_pi_div_add_one (t : ℝ) :
    (smoothSaddleOuterPrimeScale t : ℝ) <
      Real.exp (Real.pi / t) + 1 := by
  exact Nat.ceil_lt_add_one (Real.exp_pos _).le

theorem smoothSaddleOuterPrimeScale_pos (t : ℝ) :
    0 < smoothSaddleOuterPrimeScale t := by
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

theorem pi_div_le_log_smoothSaddleOuterPrimeScale (t : ℝ) :
    Real.pi / t ≤
      Real.log (smoothSaddleOuterPrimeScale t : ℝ) := by
  rw [← Real.log_exp (Real.pi / t)]
  exact Real.log_le_log (Real.exp_pos _)
    (exp_pi_div_le_smoothSaddleOuterPrimeScale t)

theorem pi_div_log_smoothSaddleOuterPrimeScale_le
    {t : ℝ} (ht : 0 < t) :
    Real.pi / Real.log (smoothSaddleOuterPrimeScale t : ℝ) ≤ t := by
  have hscale := pi_div_le_log_smoothSaddleOuterPrimeScale t
  have hpdiv : 0 < Real.pi / t := div_pos Real.pi_pos ht
  have hlog : 0 < Real.log (smoothSaddleOuterPrimeScale t : ℝ) :=
    hpdiv.trans_le hscale
  apply (div_le_iff₀ hlog).mpr
  have := (div_le_iff₀ ht).mp hscale
  nlinarith

theorem log_smoothSaddleOuterPrimeScale_le
    {t : ℝ} (ht : 0 < t) :
    Real.log (smoothSaddleOuterPrimeScale t : ℝ) ≤
      Real.pi / t + Real.log 2 := by
  have hexpOne : 1 ≤ Real.exp (Real.pi / t) := by
    exact Real.one_le_exp (div_nonneg Real.pi_pos.le ht.le)
  have hscaleLt : (smoothSaddleOuterPrimeScale t : ℝ) <
      2 * Real.exp (Real.pi / t) := by
    refine (smoothSaddleOuterPrimeScale_lt_exp_pi_div_add_one t).trans_le ?_
    nlinarith
  calc
    Real.log (smoothSaddleOuterPrimeScale t : ℝ) ≤
        Real.log (2 * Real.exp (Real.pi / t)) := by
      exact Real.log_le_log (by exact_mod_cast smoothSaddleOuterPrimeScale_pos t)
        hscaleLt.le
    _ = Real.pi / t + Real.log 2 := by
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
      ring

theorem smoothSaddleOuterPrimeScale_frequency_upper
    {t : ℝ} (ht : 0 < t)
    (htSmall : 3 * t * Real.log 2 ≤ Real.pi) :
    t ≤ 4 * Real.pi /
      (3 * Real.log (smoothSaddleOuterPrimeScale t : ℝ)) := by
  have hscale := pi_div_le_log_smoothSaddleOuterPrimeScale t
  have hpdiv : 0 < Real.pi / t := div_pos Real.pi_pos ht
  have hlog : 0 < Real.log (smoothSaddleOuterPrimeScale t : ℝ) :=
    hpdiv.trans_le hscale
  have hlogUpper := log_smoothSaddleOuterPrimeScale_le ht
  have hprod := mul_le_mul_of_nonneg_left hlogUpper ht.le
  simp only [mul_add] at hprod
  rw [mul_div_cancel₀ _ ht.ne'] at hprod
  apply (le_div_iff₀ (mul_pos (by norm_num) hlog)).mpr
  nlinarith

theorem three_quarters_mul_log_le_log_nat_div_two
    {N : ℕ} (hN : 81 ≤ N) :
    (3 / 4 : ℝ) * Real.log (N : ℝ) ≤
      Real.log ((N / 2 : ℕ) : ℝ) := by
  have hNat : N ≤ 3 * (N / 2) := by omega
  have hthird : (N : ℝ) / 3 ≤ ((N / 2 : ℕ) : ℝ) := by
    apply (div_le_iff₀ (by norm_num)).mpr
    exact_mod_cast (by simpa [mul_comm] using hNat)
  have hlogThird :
      Real.log ((N : ℝ) / 3) ≤ Real.log ((N / 2 : ℕ) : ℝ) := by
    exact Real.log_le_log (by positivity) hthird
  rw [Real.log_div (by positivity) (by norm_num)] at hlogThird
  have hpow : (3 : ℝ) ^ 4 ≤ (N : ℝ) := by
    norm_num
    exact_mod_cast hN
  have hlogPow : Real.log ((3 : ℝ) ^ 4) ≤ Real.log (N : ℝ) := by
    exact Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlogPow
  norm_num at hlogPow
  nlinarith

theorem le_smoothSaddleOuterPrimeScale
    {B : ℕ} {t : ℝ} (hB : 1 < B) (ht : 0 < t)
    (htUpper : t ≤ Real.pi / Real.log (B : ℝ)) :
    B ≤ smoothSaddleOuterPrimeScale t := by
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast hB)
  have hprod : t * Real.log (B : ℝ) ≤ Real.pi :=
    (le_div_iff₀ hlogB).mp htUpper
  have hlogLe : Real.log (B : ℝ) ≤ Real.pi / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have hcast : (B : ℝ) ≤ Real.exp (Real.pi / t) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (B : ℝ))]
    exact Real.exp_le_exp.mpr hlogLe
  exact_mod_cast hcast.trans (exp_pi_div_le_smoothSaddleOuterPrimeScale t)

theorem exists_large_chebyshevTheta_quarter_threshold :
    ∃ B : ℕ, 41 ≤ B ∧ ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta (n : ℝ) ∧
        Chebyshev.theta (n : ℝ) ≤ (5 / 4 : ℝ) * n := by
  obtain ⟨C, _hC, hCtheta⟩ := exists_chebyshevTheta_quarter_threshold
  refine ⟨max 41 C, le_max_left _ _, ?_⟩
  intro n hn
  exact hCtheta n ((le_max_right 41 C).trans hn)

theorem smoothSaddleOuterPrimeScale_le
    {y : ℕ} {t : ℝ} (ht : 0 < t) (hy : 1 < y)
    (htOuter : Real.pi / Real.log (y : ℝ) ≤ t) :
    smoothSaddleOuterPrimeScale t ≤ y := by
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast hy)
  have hpi : Real.pi ≤ t * Real.log (y : ℝ) := by
    exact (div_le_iff₀ hlogy).mp htOuter
  apply Nat.ceil_le.mpr
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (y : ℝ))]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ ht).mpr
  nlinarith

theorem movingOuterShell_cosineLoss_lower
    {y N : ℕ} (hN : 4 ≤ N) (hNy : N ≤ y)
    {sigma t : ℝ} (hsigma0 : 0 ≤ sigma)
    (hlogHalf : (3 / 4 : ℝ) * Real.log (N : ℝ) ≤
      Real.log ((N / 2 : ℕ) : ℝ))
    (htLower : Real.pi / Real.log (N : ℝ) ≤ t)
    (htUpper : t ≤ 4 * Real.pi / (3 * Real.log (N : ℝ)))
    (hlower : (3 / 4 : ℝ) * N ≤ Chebyshev.theta (N : ℝ))
    (hupper : Chebyshev.theta ((N / 2 : ℕ) : ℝ) ≤
      (5 / 4 : ℝ) * (N / 2 : ℕ)) :
    (N : ℝ) ^ (-sigma) *
        ((N : ℝ) / (16 * Real.log (N : ℝ))) ≤
      smoothSaddleCosineLoss y sigma t := by
  let S := (Finset.Icc 2 y).filter Nat.Prime
  have hsubset : cepDyadicPrimeBlock N ⊆ S := by
    intro p hp
    have hpData := mem_cepDyadicPrimeBlock_iff.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨hpData.1.two_le, hpData.2.2.trans hNy⟩, hpData.1⟩
  have hterm (p : ℕ) (hp : p ∈ cepDyadicPrimeBlock N) :
      (N : ℝ) ^ (-sigma) ≤
        (p : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log (p : ℝ))) := by
    calc
      (N : ℝ) ^ (-sigma) ≤ (p : ℝ) ^ (-sigma) :=
        y_rpow_neg_le_prime_rpow_neg_of_mem_cepDyadicPrimeBlock hp hsigma0
      _ ≤ (p : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log (p : ℝ))) := by
        exact le_mul_of_one_le_right (by positivity)
          (one_le_cosineLossTerm_of_firstOuterShell
            hN hp hlogHalf htLower htUpper)
  calc
    (N : ℝ) ^ (-sigma) *
        ((N : ℝ) / (16 * Real.log (N : ℝ))) ≤
      (N : ℝ) ^ (-sigma) * ((cepDyadicPrimeBlock N).card : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (card_cepDyadicPrimeBlock_lower hN hlower hupper) (by positivity)
    _ = ∑ _p ∈ cepDyadicPrimeBlock N, (N : ℝ) ^ (-sigma) := by
      simp
      ring
    _ ≤ ∑ p ∈ cepDyadicPrimeBlock N,
        (p : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log (p : ℝ))) := by
      exact Finset.sum_le_sum fun p hp => hterm p hp
    _ ≤ ∑ p ∈ S, (p : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log (p : ℝ))) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p hp hnot => mul_nonneg (by positivity)
          (by linarith [Real.cos_le_one (t * Real.log (p : ℝ))]))
    _ = smoothSaddleCosineLoss y sigma t := rfl

theorem adaptiveMovingOuterShell_cosineLoss_lower
    {B y : ℕ} {sigma t : ℝ}
    (hB : 41 ≤ B)
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta (n : ℝ) ∧
        Chebyshev.theta (n : ℝ) ≤ (5 / 4 : ℝ) * n)
    (hsigma0 : 0 ≤ sigma) (ht : 0 < t) (hy : 1 < y)
    (htOuter : Real.pi / Real.log (y : ℝ) ≤ t)
    (htSmall : 3 * t * Real.log 2 ≤ Real.pi)
    (htScale : t ≤ Real.pi / Real.log ((2 * B : ℕ) : ℝ)) :
    (smoothSaddleOuterPrimeScale t : ℝ) ^ (-sigma) *
        ((smoothSaddleOuterPrimeScale t : ℝ) /
          (16 * Real.log (smoothSaddleOuterPrimeScale t : ℝ))) ≤
      smoothSaddleCosineLoss y sigma t := by
  have hTwoB : 2 * B ≤ smoothSaddleOuterPrimeScale t :=
    le_smoothSaddleOuterPrimeScale (by omega) ht htScale
  have hN81 : 81 ≤ smoothSaddleOuterPrimeScale t := by omega
  have hBN : B ≤ smoothSaddleOuterPrimeScale t := by omega
  have hBHalf : B ≤ smoothSaddleOuterPrimeScale t / 2 := by omega
  exact movingOuterShell_cosineLoss_lower
    (N := smoothSaddleOuterPrimeScale t)
    (by omega)
    (smoothSaddleOuterPrimeScale_le ht hy htOuter)
    hsigma0
    (three_quarters_mul_log_le_log_nat_div_two hN81)
    (pi_div_log_smoothSaddleOuterPrimeScale_le ht)
    (smoothSaddleOuterPrimeScale_frequency_upper ht htSmall)
    (hpnt _ hBN).1
    (hpnt _ hBHalf).2

end

end Tao2026
