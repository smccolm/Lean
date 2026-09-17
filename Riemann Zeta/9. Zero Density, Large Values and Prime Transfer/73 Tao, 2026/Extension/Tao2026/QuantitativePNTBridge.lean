import Tao2026.LowFrequencyPNT
import Tao2026.SpecializedRealScale
import Tao2026.TypeIIArithmetic

/-!
# Classical quantitative-PNT bridge

The low-frequency argument consumes a logarithmic-saving estimate for the
prefix sums of `Λ - 1`.  Classical quantitative versions of the prime number
theorem are normally stated instead as a de la Vallée Poussin error estimate
for Chebyshev's function `ψ`.  This file proves the exact conversion, including
the one-point endpoint discrepancy between `ψ(k)` and the half-open prefix
sum used by the Abel argument.

No quantitative prime number theorem is postulated as an axiom: the source
estimate remains an explicit proposition.
-/

open Complex Finset Filter Set
open scoped ArithmeticFunction.vonMangoldt BigOperators Topology

namespace Tao2026

noncomputable section

/-- The standard de la Vallée Poussin form of the classical quantitative
prime number theorem.  The constants are absolute and the bound is eventual
on real arguments. -/
def ClassicalChebyshevPsiDeLaValleePoussin : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))

/-- `ψ(k)` includes the endpoint `k`, whereas `cumsum Λ k` is the half-open
sum over `n < k`. -/
theorem cumsum_vonMangoldt_eq_psi_sub_endpoint (k : ℕ) :
    (cumsum Λ k : ℝ) = Chebyshev.psi k - Λ k := by
  rw [Chebyshev.psi_eq_sum_Icc]
  norm_num
  rw [show Finset.Icc 0 k = Finset.Iic k by ext n; simp]
  have hk : k ∈ Finset.Iic k := Finset.mem_Iic.mpr le_rfl
  unfold cumsum
  calc
    ∑ i ∈ Finset.range k, Λ i =
        ∑ i ∈ (Finset.Iic k).erase k, Λ i := by
      rw [← Nat.Iio_eq_range, Finset.Iic_erase]
    _ = (∑ i ∈ Finset.Iic k, Λ i) - Λ k := by
      rw [← Finset.sum_erase_add _ _ hk]
      ring

/-- A stretched exponential in `sqrt(log x)` beats every integral power of
`log x`.  This is the precise absorption needed by the PNT bridge. -/
theorem eventually_exp_neg_sqrt_log_le_log_pow_inv
    {c : ℝ} (hc : 0 < c) (A : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * Real.sqrt (Real.log x)) ≤
        1 / (Real.log x) ^ A := by
  have hdecay := eventually_exp_neg_log_rpow_le_log_rpow_neg
    (c := c) (ρ := (1 / 2 : ℝ)) (A := (A : ℝ)) hc (by norm_num)
  filter_upwards [hdecay,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with x hx hlog
  rw [Real.sqrt_eq_rpow]
  simpa [one_div, Real.rpow_neg hlog.le, Real.rpow_natCast] using hx

/-- The endpoint term `Λ(k)` is negligible compared with every requested
logarithmic-saving scale. -/
theorem eventually_log_pow_succ_le_self (A : ℕ) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (A + 1) ≤ x := by
  have hsmall := isLittleO_log_rpow_rpow_atTop ((A + 1 : ℕ) : ℝ)
    (s := (1 : ℝ)) zero_lt_one
  have hdenPositive : ∀ᶠ x : ℝ in atTop, 0 < ‖x ^ (1 : ℝ)‖ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hx)]
    exact zero_lt_one.trans hx
  filter_upwards
      [hsmall.eventuallyLT_norm_of_eventually_pos hdenPositive,
        eventually_ge_atTop (1 : ℝ)] with x hx hxOne
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hxOne
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _), Real.rpow_one,
    Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans_le hxOne),
    Real.rpow_natCast] at hx
  exact hx.le

/-- The classical real-variable `ψ` estimate implies the exact global
half-open Mangoldt discrepancy contract used by the low-frequency argument. -/
theorem classicalMangoldtDiscrepancyLogSaving_of_chebyshevPsiDeLaValleePoussin
    (hPNT : ClassicalChebyshevPsiDeLaValleePoussin) :
    ClassicalMangoldtDiscrepancyLogSaving := by
  obtain ⟨C, c, hC, hc, hpsi⟩ := hPNT
  intro A
  refine ⟨C + 1, by linarith, ?_⟩
  have hpsiNat := hpsi.filter_mono tendsto_natCast_atTop_atTop
  have hdecay := (eventually_exp_neg_sqrt_log_le_log_pow_inv hc A).filter_mono
    tendsto_natCast_atTop_atTop
  have hendpoint := (eventually_log_pow_succ_le_self A).filter_mono
    tendsto_natCast_atTop_atTop
  filter_upwards [hpsiNat, hdecay, hendpoint,
    eventually_ge_atTop (2 : ℕ)] with k hpsiK hdecayK hendpointK hk
  have hkReal : (0 : ℝ) ≤ k := by positivity
  have hlog : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hLambdaNonneg : (0 : ℝ) ≤ Λ k :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hLambda : (Λ k : ℝ) ≤ Real.log k :=
    ArithmeticFunction.vonMangoldt_le_log
  have hlogPowOne : Real.log (k : ℝ) ≤
      (k : ℝ) / (Real.log k) ^ A := by
    rw [le_div_iff₀ (pow_pos hlog A)]
    simpa [pow_succ'] using hendpointK
  rw [mangoldtDiscrepancyPartialSum_zero_eq,
    cumsum_vonMangoldt_eq_psi_sub_endpoint]
  change ‖(((Chebyshev.psi (k : ℝ) - (Λ k : ℝ) - (k : ℝ) : ℝ) : ℂ))‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    |(Chebyshev.psi k - Λ k) - k| ≤
        |Chebyshev.psi k - k| + |(Λ k : ℝ)| := by
      rw [show (Chebyshev.psi k - Λ k) - k =
        (Chebyshev.psi k - k) - Λ k by ring]
      exact abs_sub _ _
    _ ≤ C * k * Real.exp (-c * Real.sqrt (Real.log k)) + Real.log k := by
      apply add_le_add hpsiK
      rw [abs_of_nonneg hLambdaNonneg]
      exact hLambda
    _ ≤ C * k * (1 / (Real.log k) ^ A) +
        k / (Real.log k) ^ A := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hdecayK (mul_nonneg hC.le hkReal))
        hlogPowOne
    _ = (C + 1) * k / (Real.log k) ^ A := by ring

/-- Source-facing specialized Theorem 2.5 endpoint with the low-frequency
input stated in the classical `ψ` form.  After this bridge, the only other
analytic hypothesis is the named Vinogradov exponential-sum proposition. -/
theorem taoTheorem25Specialized_of_chebyshevPsiDeLaValleePoussin
    (hPNT : ClassicalChebyshevPsiDeLaValleePoussin)
    (hVinogradov : VinogradovExponentialSumEstimate) :
    TaoTheorem25SpecializedConclusion :=
  taoTheorem25Specialized_of_analyticInputs
    (classicalMangoldtDiscrepancyLogSaving_of_chebyshevPsiDeLaValleePoussin hPNT)
    hVinogradov

end

end Tao2026
