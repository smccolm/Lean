import DongWangWangZhang2026.TwistSelection
import DongWangWangZhang2026.PowerSumEstimate
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Actual convolution coefficients for the mean-comparison argument

This is the arithmetic reduction in Granville--Soundararajan (2003), Lemma 7.1,
specialized to the phase consumed by Dong--Wang--Wang--Zhang Lemma 2.2.
The coefficients are the actual Möbius convolution, not assumed error data.
The quantitative mean-value estimate is a separate, still open obligation.
-/

namespace DongWangWangZhang2026

open Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius

noncomputable section

/-- The positive-index phase as a genuine arithmetic function. -/
def phaseArithmetic (τ : ℝ) : ArithmeticFunction ℂ :=
  ⟨zetaTerm τ, zetaTerm_zero τ⟩

@[simp] theorem phaseArithmetic_apply (τ : ℝ) (n : ℕ) :
    phaseArithmetic τ n = zetaTerm τ n := rfl

theorem isMultiplicative_phaseArithmetic (τ : ℝ) :
    (phaseArithmetic τ).IsMultiplicative :=
  ⟨zetaTerm_one τ, fun {_ _} _ => zetaTerm_mul τ _ _⟩

/-- The coefficient `g = μ * f` in the source's mean-comparison proof. -/
def phaseMobiusCoeff (τ : ℝ) : ArithmeticFunction ℂ :=
  (μ : ArithmeticFunction ℂ) * phaseArithmetic τ

theorem isMultiplicative_phaseMobiusCoeff (τ : ℝ) :
    (phaseMobiusCoeff τ).IsMultiplicative :=
  isMultiplicative_moebius.intCast.mul (isMultiplicative_phaseArithmetic τ)

theorem phaseMobiusCoeff_mul_zeta (τ : ℝ) :
    phaseMobiusCoeff τ * (ζ : ArithmeticFunction ℂ) = phaseArithmetic τ := by
  rw [phaseMobiusCoeff, mul_assoc, mul_comm (phaseArithmetic τ),
    ← mul_assoc, coe_moebius_mul_coe_zeta, one_mul]

theorem sum_divisors_phaseMobiusCoeff (τ : ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors, phaseMobiusCoeff τ d) = zetaTerm τ n := by
  rw [← coe_mul_zeta_apply, phaseMobiusCoeff_mul_zeta, phaseArithmetic_apply]

/-- The prime-power coefficients are exact successive differences of the phase. -/
theorem phaseMobiusCoeff_prime_pow (τ : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    phaseMobiusCoeff τ (p ^ (k + 1)) =
      zetaTerm τ (p ^ (k + 1)) - zetaTerm τ (p ^ k) := by
  have hnext := sum_divisors_phaseMobiusCoeff τ (p ^ (k + 1))
  have hprev := sum_divisors_phaseMobiusCoeff τ (p ^ k)
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ] at hnext
  rw [Nat.sum_divisors_prime_pow hp] at hprev
  rw [hprev] at hnext
  linear_combination hnext

theorem phaseMobiusCoeff_prime (τ : ℝ) {p : ℕ} (hp : p.Prime) :
    phaseMobiusCoeff τ p = zetaTerm τ p - 1 := by
  simpa using phaseMobiusCoeff_prime_pow τ hp 0

theorem norm_phaseMobiusCoeff_prime_pow_le (τ : ℝ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) : ‖phaseMobiusCoeff τ (p ^ (k + 1))‖ ≤ 2 := by
  rw [phaseMobiusCoeff_prime_pow τ hp]
  calc
    ‖zetaTerm τ (p ^ (k + 1)) - zetaTerm τ (p ^ k)‖ ≤
        ‖zetaTerm τ (p ^ (k + 1))‖ + ‖zetaTerm τ (p ^ k)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_zetaTerm τ (pow_pos hp.pos _),
      norm_zetaTerm τ (pow_pos hp.pos _)]; norm_num

/-- Twisting the actual convolution commutes with its product decomposition. -/
theorem phaseMobiusCoeff_twist_convolution (τ α : ℝ) :
    (phaseMobiusCoeff τ).pmul (phaseArithmetic α) * phaseArithmetic α =
      phaseArithmetic (τ + α) := by
  ext n
  rw [ArithmeticFunction.mul_apply]
  simp only [pmul_apply, phaseArithmetic_apply]
  calc
    (∑ q ∈ n.divisorsAntidiagonal,
        phaseMobiusCoeff τ q.1 * zetaTerm α q.1 * zetaTerm α q.2) =
        ∑ q ∈ n.divisorsAntidiagonal, phaseMobiusCoeff τ q.1 * zetaTerm α n := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [mul_assoc, ← zetaTerm_mul, (Nat.mem_divisorsAntidiagonal.mp hq).1]
    _ = (∑ d ∈ n.divisors, phaseMobiusCoeff τ d) * zetaTerm α n := by
      rw [← Finset.sum_mul,
        Nat.sum_divisorsAntidiagonal (fun d _ => phaseMobiusCoeff τ d)]
    _ = zetaTerm (τ + α) n := by
      rw [sum_divisors_phaseMobiusCoeff, zetaTerm_add]

/-- The exact finite convolution identity, with the original real cutoff. -/
theorem zetaSum_eq_mobius_twisted_sum (x τ α : ℝ) :
    zetaSum x (τ + α) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
        phaseMobiusCoeff τ d * zetaTerm α d * zetaSum (x / d) α := by
  have hI (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have h := sum_Ioc_mul_eq_sum_sum
    ((phaseMobiusCoeff τ).pmul (phaseArithmetic α)) (phaseArithmetic α) ⌊x⌋₊
  rw [phaseMobiusCoeff_twist_convolution] at h
  simpa only [hI, pmul_apply, phaseArithmetic_apply, zetaSum,
    Nat.floor_div_natCast] using h

/-- For this completely multiplicative phase, all positive prime powers have the same norm. -/
theorem norm_phaseMobiusCoeff_prime_pow (τ : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ‖phaseMobiusCoeff τ (p ^ (k + 1))‖ = ‖zetaTerm τ p - 1‖ := by
  rw [phaseMobiusCoeff_prime_pow τ hp, pow_succ, zetaTerm_mul]
  rw [show zetaTerm τ (p ^ k) * zetaTerm τ p - zetaTerm τ (p ^ k) =
    zetaTerm τ (p ^ k) * (zetaTerm τ p - 1) by ring]
  rw [norm_mul, norm_zetaTerm τ (pow_pos hp.pos _), one_mul]

/-- Untwisted finite Möbius inversion, including every floor in the source sum. -/
theorem zetaSum_eq_mobius_floor_sum (x τ : ℝ) :
    zetaSum x τ = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
      phaseMobiusCoeff τ d * (⌊x / d⌋₊ : ℂ) := by
  have hI (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have h := sum_Ioc_mul_zeta_eq_sum (phaseMobiusCoeff τ) ⌊x⌋₊
  rw [phaseMobiusCoeff_mul_zeta] at h
  simpa only [hI, phaseArithmetic_apply, zetaSum, Nat.floor_div_natCast] using h

/-- The actual prefactor `x^(iα)/(1+iα)` in the mean-comparison formula. -/
def comparisonFactor (x α : ℝ) : ℂ :=
  (x : ℂ) ^ ((α : ℂ) * Complex.I) / ((α : ℂ) * Complex.I + 1)

theorem norm_comparisonFactor_le_one {x : ℝ} (hx : 0 < x) (α : ℝ) :
    ‖comparisonFactor x α‖ ≤ 1 := by
  have hd : 1 ≤ ‖(α : ℂ) * Complex.I + 1‖ := by
    simpa using Complex.re_le_norm ((α : ℂ) * Complex.I + 1)
  rw [comparisonFactor, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, Real.rpow_zero]
  exact (div_le_one (zero_lt_one.trans_le hd)).mpr hd

/-- Multiplicativity transports the inner power-sum main term to the source prefactor. -/
theorem phase_powerMain_transport {x : ℝ} (hx : 0 < x) (α : ℝ) {d : ℕ} (hd : 0 < d) :
    zetaTerm α d *
      (((x / d : ℝ) : ℂ) ^ ((α : ℂ) * Complex.I + 1) / ((α : ℂ) * Complex.I + 1)) =
        comparisonFactor x α * ((x / d : ℝ) : ℂ) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hz : 0 < x / d := div_pos hx hdR
  have hm : (d : ℂ) ^ ((α : ℂ) * Complex.I) *
      ((x / d : ℝ) : ℂ) ^ ((α : ℂ) * Complex.I) = (x : ℂ) ^ ((α : ℂ) * Complex.I) := by
    rw [← Complex.ofReal_natCast d,
      ← Complex.mul_cpow_ofReal_nonneg hdR.le hz.le, ← Complex.ofReal_mul,
      mul_div_cancel₀ _ hdR.ne']
  rw [zetaTerm_eq_cpow α hd.ne', Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hz.ne'),
    Complex.cpow_one, comparisonFactor]
  calc
    _ = ((d : ℂ) ^ ((α : ℂ) * Complex.I) * ((x / d : ℝ) : ℂ) ^ ((α : ℂ) * Complex.I)) *
      ((x / d : ℝ) : ℂ) / ((α : ℂ) * Complex.I + 1) := by ring
    _ = _ := by rw [hm]; ring

/-- Pointwise coefficient error, retaining both bounds needed for the short/long split. -/
theorem norm_twisted_cell_comparison_le {x : ℝ} (hx : 0 < x) (α : ℝ)
    {d : ℕ} (hd : 0 < d) (hdx : (d : ℝ) ≤ x) :
    ‖zetaTerm α d * zetaSum (x / d) α - comparisonFactor x α * (⌊x / d⌋₊ : ℂ)‖ ≤
      min (5 * (1 + α ^ 2)) (2 * (x / d)) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hz : 1 ≤ x / d := (le_div_iff₀ hdR).mpr (by simpa using hdx)
  have hz0 : 0 ≤ x / d := zero_le_one.trans hz
  have hfactor := norm_comparisonFactor_le_one hx α
  have hfloor : ‖((x / d : ℝ) : ℂ) - (⌊x / d⌋₊ : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact Nat.abs_sub_floor_le hz0
  have heq : zetaTerm α d * zetaSum (x / d) α -
      comparisonFactor x α * (⌊x / d⌋₊ : ℂ) =
      zetaTerm α d * (zetaSum (x / d) α -
        ((x / d : ℝ) : ℂ) ^ ((α : ℂ) * Complex.I + 1) / ((α : ℂ) * Complex.I + 1)) +
      comparisonFactor x α * (((x / d : ℝ) : ℂ) - (⌊x / d⌋₊ : ℂ)) := by
    rw [mul_sub, phase_powerMain_transport hx α hd]
    ring
  apply le_min
  · rw [heq]
    have h := norm_add_le
      (zetaTerm α d * (zetaSum (x / d) α -
        ((x / d : ℝ) : ℂ) ^ ((α : ℂ) * Complex.I + 1) / ((α : ℂ) * Complex.I + 1)))
      (comparisonFactor x α * (((x / d : ℝ) : ℂ) - (⌊x / d⌋₊ : ℂ)))
    simp only [norm_mul, norm_zetaTerm α hd, one_mul] at h
    have hb := mul_le_mul hfactor hfloor (norm_nonneg _) zero_le_one
    have hp := norm_zetaSum_sub_powerMain_le α hz
    nlinarith [h, hp, hb, sq_nonneg α]
  · calc
      _ ≤ ‖zetaTerm α d * zetaSum (x / d) α‖ +
          ‖comparisonFactor x α * (⌊x / d⌋₊ : ℂ)‖ := norm_sub_le _ _
      _ ≤ x / d + x / d := by
        rw [norm_mul, norm_zetaTerm α hd, one_mul, norm_mul, Complex.norm_natCast]
        exact add_le_add (norm_zetaSum_le hz0 α)
          ((mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _)).trans
            (by simpa using Nat.floor_le hz0))
      _ = 2 * (x / d) := by ring

/-- Actual twisted-mean error bounded by the explicit Möbius coefficient sum.
No coefficient mean-value estimate or desired comparison conclusion is assumed. -/
theorem norm_mean_comparison_le_mobius_error {x : ℝ} (hx : 0 < x) (τ α : ℝ) :
    ‖zetaSum x (τ + α) - comparisonFactor x α * zetaSum x τ‖ ≤
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
        ‖phaseMobiusCoeff τ d‖ * min (5 * (1 + α ^ 2)) (2 * (x / d)) := by
  rw [zetaSum_eq_mobius_twisted_sum x τ α, zetaSum_eq_mobius_floor_sum x τ,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  have heq : (∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
      (phaseMobiusCoeff τ d * zetaTerm α d * zetaSum (x / d) α -
        comparisonFactor x α * (phaseMobiusCoeff τ d * (⌊x / d⌋₊ : ℂ)))) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusCoeff τ d *
        (zetaTerm α d * zetaSum (x / d) α - comparisonFactor x α * (⌊x / d⌋₊ : ℂ)) := by
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [heq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro d hd
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_twisted_cell_comparison_le hx α (Finset.mem_Icc.mp hd).1
    ((Nat.cast_le.mpr (Finset.mem_Icc.mp hd).2).trans (Nat.floor_le hx.le))

end
end DongWangWangZhang2026
