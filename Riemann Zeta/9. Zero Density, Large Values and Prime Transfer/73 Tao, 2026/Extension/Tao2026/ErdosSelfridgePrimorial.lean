import Tao2026.ErdosSelfridgeSquareValuations
import Tao2026.FactorialCoefficientBounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The eventual primorial contradiction after Erdős--Selfridge equation (23)

This file closes the asymptotic large-length part of Section 3.1 of the pinned
1975 proof.  The frozen prime number theorem bounds the product of primes below
`H` by `3^H` eventually.  Exact rational lower estimates for the two fractional
powers in equation (23) show that its left-hand side has an exponential base
strictly larger than `3`; polynomial-versus-exponential growth then contradicts
equation (23) for every sufficiently large `H`.

This is an eventual theorem, not the paper's explicit numerical cutoff.  The
finite range below an extracted threshold remains separate.
-/

namespace Tao2026

open scoped BigOperators Topology
open Filter

/-- For positive `H`, the source product over primes strictly below `H` is the
standard primorial at `H-1`. -/
theorem erdosSelfridgePrimeProduct_eq_primorial_sub_one {H : ℕ}
    (hH : 1 ≤ H) :
    erdosSelfridgePrimeProduct H = primorial (H - 1) := by
  rw [erdosSelfridgePrimeProduct, primorial_eq_prod_primesLE, Nat.primesLE]
  rw [Nat.sub_add_cancel hH]

/-- The frozen PNT gives the coarse primorial estimate required after equation
(23).  The statement is eventual because no explicit Rosser--Schoenfeld cutoff
is imported into this development. -/
theorem eventually_erdosSelfridgePrimeProduct_le_three_pow :
    ∀ᶠ H : ℕ in atTop,
      (erdosSelfridgePrimeProduct H : ℝ) ≤ (3 : ℝ) ^ H := by
  have hlog : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three
  have herrReal := eventually_abs_chebyshev_theta_error_le
    (Real.log 3 - 1) (sub_pos.mpr hlog)
  have herrNat : ∀ᶠ H : ℕ in atTop,
      |Chebyshev.theta H - H| ≤ (Real.log 3 - 1) * H :=
    tendsto_natCast_atTop_atTop.eventually herrReal
  filter_upwards [herrNat, eventually_ge_atTop 1] with H herr hH
  rw [abs_le] at herr
  have htheta : Chebyshev.theta H ≤ (H : ℝ) * Real.log 3 := by
    nlinarith
  have hlogPrimorial : Real.log (primorial H) ≤
      Real.log ((3 : ℝ) ^ H) := by
    have heq : Chebyshev.theta (H : ℝ) = Real.log (primorial H) := by
      simpa using Chebyshev.theta_eq_log_primorial (H : ℝ)
    rw [← heq, Real.log_pow]
    simpa [mul_comm] using htheta
  have hprimorialPos : (0 : ℝ) < primorial H := by
    exact_mod_cast primorial_pos H
  have hprimorial : (primorial H : ℝ) ≤ (3 : ℝ) ^ H := by
    exact (Real.strictMonoOn_log.le_iff_le
      (show (primorial H : ℝ) ∈ Set.Ioi 0 from hprimorialPos)
      (show (3 : ℝ) ^ H ∈ Set.Ioi 0 by
        change (0 : ℝ) < (3 : ℝ) ^ H
        exact pow_pos (by norm_num : (0 : ℝ) < 3) H)).mp hlogPrimorial
  have hlocalNat : erdosSelfridgePrimeProduct H ≤ primorial H := by
    rw [erdosSelfridgePrimeProduct_eq_primorial_sub_one hH]
    exact primorial_mono (Nat.sub_le H 1)
  have hlocalReal : (erdosSelfridgePrimeProduct H : ℝ) ≤
      (primorial H : ℝ) := by
    exact_mod_cast hlocalNat
  exact hlocalReal.trans hprimorial

/-- The effective exponential base on the left of equation (23). -/
noncomputable def erdosSelfridgeEquation23Base : ℝ :=
  (3 / 2 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) * (3 : ℝ) ^ (1 / 4 : ℝ)

private theorem fourteen_div_nine_lt_two_rpow_two_thirds :
    (14 / 9 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by
  calc
    (14 / 9 : ℝ) < (4 : ℝ) ^ ((3 : ℝ)⁻¹) := by
      rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
      norm_num
    _ = (2 : ℝ) ^ (2 / 3 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num)]
      congr 1

private theorem thirteen_div_ten_lt_three_rpow_one_quarter :
    (13 / 10 : ℝ) < (3 : ℝ) ^ (1 / 4 : ℝ) := by
  rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
  rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The left side of equation (23) has exponential base strictly larger than
the primorial comparison base `3`. -/
theorem three_lt_erdosSelfridgeEquation23Base :
    3 < erdosSelfridgeEquation23Base := by
  dsimp [erdosSelfridgeEquation23Base]
  calc
    3 < (3 / 2 : ℝ) * (14 / 9) * (13 / 10) := by norm_num
    _ < (3 / 2 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) * (13 / 10) := by
      gcongr
      exact fourteen_div_nine_lt_two_rpow_two_thirds
    _ < (3 / 2 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) *
        (3 : ℝ) ^ (1 / 4 : ℝ) := by
      gcongr
      exact thirteen_div_ten_lt_three_rpow_one_quarter

/-- Exact regrouping of the left side of equation (23) as a natural power of
its effective base. -/
theorem erdosSelfridge_equation23_left_eq_base_pow (H : ℕ) :
    (((3 : ℝ) / 2) ^ (H : ℝ)) *
          (2 : ℝ) ^ ((2 * (H : ℝ)) / 3) *
          (3 : ℝ) ^ ((H : ℝ) / 4) =
      erdosSelfridgeEquation23Base ^ H := by
  have htwo : (2 : ℝ) ^ ((2 * (H : ℝ)) / 3) =
      ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ H := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hthree : (3 : ℝ) ^ ((H : ℝ) / 4) =
      ((3 : ℝ) ^ (1 / 4 : ℝ)) ^ H := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [Real.rpow_natCast, htwo, hthree, erdosSelfridgeEquation23Base,
    mul_pow, mul_pow]

/-- The polynomially weighted `3^H` upper bound is eventually smaller than the
left side of equation (23). -/
theorem eventually_equation23_three_pow_lt_left :
    ∀ᶠ H : ℕ in atTop,
      (14 / 3 : ℝ) * (H : ℝ) ^ 2 * (3 : ℝ) ^ H <
        erdosSelfridgeEquation23Base ^ H := by
  have hratio : 1 < erdosSelfridgeEquation23Base / 3 :=
    (one_lt_div (by norm_num)).2 three_lt_erdosSelfridgeEquation23Base
  have hlittle :
      (fun H : ℕ => (H : ℝ) ^ 2) =o[atTop]
        (fun H : ℕ => (erdosSelfridgeEquation23Base / 3) ^ H) :=
    isLittleO_pow_const_const_pow_of_one_lt 2 hratio
  have hev := (Asymptotics.isLittleO_iff.mp hlittle)
    (by norm_num : (0 : ℝ) < 3 / 28)
  filter_upwards [hev] with H hH
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)] at hH
  have hrewrite : (erdosSelfridgeEquation23Base / 3 : ℝ) ^ H *
      (3 : ℝ) ^ H = erdosSelfridgeEquation23Base ^ H := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hbasePow : 0 < erdosSelfridgeEquation23Base ^ H := by
    exact pow_pos ((show (0 : ℝ) < 3 by norm_num).trans
      three_lt_erdosSelfridgeEquation23Base) H
  calc
    (14 / 3 : ℝ) * (H : ℝ) ^ 2 * (3 : ℝ) ^ H ≤
        (14 / 3 : ℝ) * ((3 / 28 : ℝ) *
          (erdosSelfridgeEquation23Base / 3) ^ H) * (3 : ℝ) ^ H := by
      gcongr
    _ = (1 / 2 : ℝ) * erdosSelfridgeEquation23Base ^ H := by
      rw [← hrewrite]
      ring
    _ < erdosSelfridgeEquation23Base ^ H := by nlinarith

/-- Equation (23), the PNT primorial bound, and exponential dominance exclude
all sufficiently large square-case multiplicity failures. -/
theorem eventually_not_erdosSelfridgePrimeMultiplicityFailureAt_two
    (hSS : SylvesterSchurConclusion) :
    ∀ᶠ H : ℕ in atTop, ∀ N : ℕ, H < N →
      ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  filter_upwards [eventually_erdosSelfridgePrimeProduct_le_three_pow,
    eventually_equation23_three_pow_lt_left,
    eventually_ge_atTop 64] with H hprime hgrowth hH
  intro N hHN hfail
  have heq23 := erdosSelfridge_equation23_of_failure hSS hH hHN hfail
  rw [erdosSelfridge_equation23_left_eq_base_pow] at heq23
  have hrhs :
      (14 / 3 : ℝ) * (H : ℝ) ^ 2 * erdosSelfridgePrimeProduct H ≤
        (14 / 3 : ℝ) * (H : ℝ) ^ 2 * (3 : ℝ) ^ H := by
    gcongr
  have himpossible : erdosSelfridgeEquation23Base ^ H <
      erdosSelfridgeEquation23Base ^ H := (heq23.trans_le hrhs).trans hgrowth
  exact (lt_irrefl _ himpossible)

/-- Threshold form of the eventual large-length square-case conclusion. -/
theorem exists_erdosSelfridgeSquareLargeLengthThreshold
    (hSS : SylvesterSchurConclusion) :
    ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H → ∀ N : ℕ, H < N →
      ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  simpa only [eventually_atTop] using
    eventually_not_erdosSelfridgePrimeMultiplicityFailureAt_two hSS

end Tao2026
