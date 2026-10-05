import DongWangWangZhang2026.MeanComparison
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.AbelSummation

/-!
# Mean estimates for the actual Möbius coefficients

The logarithmically weighted coefficient identity supplies the elementary
mean estimate used in the Granville--Soundararajan comparison argument.
The input phase and coefficients are those of `MeanComparison`, without
an assumed mean-value bound.
-/

namespace DongWangWangZhang2026

open Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius

noncomputable section

/-- Pointwise multiplication by the real logarithm, viewed in the complex coefficients. -/
def coefficientLogMul (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => (Real.log n : ℂ) * f n, by simp⟩

@[simp] theorem coefficientLogMul_apply (f : ArithmeticFunction ℂ) (n : ℕ) :
    coefficientLogMul f n = (Real.log n : ℂ) * f n := rfl

/-- The logarithmic weight is a derivation for genuine Dirichlet convolution. -/
theorem coefficientLogMul_mul (f g : ArithmeticFunction ℂ) :
    coefficientLogMul (f * g) = coefficientLogMul f * g + f * coefficientLogMul g := by
  ext n
  simp only [coefficientLogMul_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hq).1
  have hleft := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hq
  have hright := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hq
  rw [← hprod, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr hleft) (Nat.cast_ne_zero.mpr hright)]
  push_cast
  ring

/-- The actual von Mangoldt function with its values embedded in `ℂ`. -/
def complexMangoldt : ArithmeticFunction ℂ :=
  ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℂ), by simp⟩

@[simp] theorem complexMangoldt_apply (n : ℕ) :
    complexMangoldt n = (ArithmeticFunction.vonMangoldt n : ℂ) := rfl

theorem sum_divisors_complexMangoldt (n : ℕ) :
    (∑ d ∈ n.divisors, complexMangoldt d) = (Real.log n : ℂ) := by
  simpa only [complexMangoldt_apply, Complex.ofReal_sum] using
    congrArg (fun y : ℝ => (y : ℂ)) (ArithmeticFunction.vonMangoldt_sum (n := n))

theorem coefficientLogMul_moebius_mul_zeta :
    coefficientLogMul (μ : ArithmeticFunction ℂ) * (ζ : ArithmeticFunction ℂ) =
      -complexMangoldt := by
  ext n
  rw [coe_mul_zeta_apply]
  have h := congrArg (fun y : ℝ => (y : ℂ))
    (ArithmeticFunction.sum_moebius_mul_log_eq (n := n))
  push_cast at h
  simpa only [coefficientLogMul_apply, intCoe_apply, ArithmeticFunction.neg_apply,
    complexMangoldt_apply, ArithmeticFunction.log_apply, mul_comm] using h

theorem coefficientLogMul_moebius :
    coefficientLogMul (μ : ArithmeticFunction ℂ) =
      -(μ : ArithmeticFunction ℂ) * complexMangoldt := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f * (μ : ArithmeticFunction ℂ))
    coefficientLogMul_moebius_mul_zeta
  dsimp only at h
  rw [mul_assoc, coe_zeta_mul_coe_moebius, mul_one] at h
  rw [h]
  ring

/-- Complete multiplicativity gives the exact twisted von Mangoldt convolution. -/
theorem coefficientLogMul_phase (τ : ℝ) :
    coefficientLogMul (phaseArithmetic τ) =
      phaseArithmetic τ * (phaseArithmetic τ).pmul complexMangoldt := by
  ext n
  rw [coefficientLogMul_apply, ArithmeticFunction.mul_apply]
  simp only [pmul_apply, phaseArithmetic_apply]
  symm
  calc
    (∑ q ∈ n.divisorsAntidiagonal,
      zetaTerm τ q.1 * (zetaTerm τ q.2 * complexMangoldt q.2)) =
        ∑ q ∈ n.divisorsAntidiagonal, zetaTerm τ n * complexMangoldt q.2 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [← mul_assoc, ← zetaTerm_mul, (Nat.mem_divisorsAntidiagonal.mp hq).1]
    _ = zetaTerm τ n * ∑ d ∈ n.divisors, complexMangoldt d := by
      rw [← Finset.mul_sum,
        Nat.sum_divisorsAntidiagonal' (fun _ d => complexMangoldt d)]
    _ = (Real.log n : ℂ) * zetaTerm τ n := by
      rw [sum_divisors_complexMangoldt, mul_comm]

/-- Exact logarithmic identity for `g = μ * n^(iτ)`, before taking norms. -/
theorem coefficientLogMul_phaseMobiusCoeff (τ : ℝ) :
    coefficientLogMul (phaseMobiusCoeff τ) =
      phaseMobiusCoeff τ * ((phaseArithmetic τ).pmul complexMangoldt - complexMangoldt) := by
  rw [phaseMobiusCoeff, coefficientLogMul_mul, coefficientLogMul_moebius,
    coefficientLogMul_phase]
  ring

/-- Absolute values of the actual Möbius coefficients. -/
def phaseMobiusAbs (τ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => ‖phaseMobiusCoeff τ n‖, by simp⟩

@[simp] theorem phaseMobiusAbs_apply (τ : ℝ) (n : ℕ) :
    phaseMobiusAbs τ n = ‖phaseMobiusCoeff τ n‖ := rfl

theorem phaseMobiusAbs_nonneg (τ : ℝ) (n : ℕ) : 0 ≤ phaseMobiusAbs τ n := by
  exact norm_nonneg (phaseMobiusCoeff τ n)

theorem isMultiplicative_phaseMobiusAbs (τ : ℝ) : (phaseMobiusAbs τ).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp only [phaseMobiusAbs_apply, (isMultiplicative_phaseMobiusCoeff τ).map_one, norm_one]
  · intro m n hmn
    simp only [phaseMobiusAbs_apply,
      (isMultiplicative_phaseMobiusCoeff τ).map_mul_of_coprime hmn, norm_mul]

/-- The phase logarithmic derivative is bounded by twice the genuine von Mangoldt function. -/
theorem norm_twisted_mangoldt_difference_le (τ : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖zetaTerm τ n * complexMangoldt n - complexMangoldt n‖ ≤
      2 * ArithmeticFunction.vonMangoldt n := by
  rw [← sub_one_mul, norm_mul, complexMangoldt_apply, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  apply mul_le_mul_of_nonneg_right _ ArithmeticFunction.vonMangoldt_nonneg
  have h := norm_sub_le (zetaTerm τ n) 1
  rw [norm_zetaTerm τ hn, norm_one] at h
  linarith

/-- Pointwise logarithmic domination, proved from the actual coefficient convolution. -/
theorem phaseMobiusAbs_mul_log_le_convolution (τ : ℝ) (n : ℕ) :
    phaseMobiusAbs τ n * Real.log n ≤
      2 * (phaseMobiusAbs τ * ArithmeticFunction.vonMangoldt) n := by
  have hi := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (coefficientLogMul_phaseMobiusCoeff τ)
  change (Real.log n : ℂ) * phaseMobiusCoeff τ n =
    ∑ q ∈ n.divisorsAntidiagonal, phaseMobiusCoeff τ q.1 *
      (zetaTerm τ q.2 * complexMangoldt q.2 - complexMangoldt q.2) at hi
  have hnorm : phaseMobiusAbs τ n * Real.log n =
      ‖(Real.log n : ℂ) * phaseMobiusCoeff τ n‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg n),
      phaseMobiusAbs_apply, mul_comm]
  rw [hnorm, hi, ArithmeticFunction.mul_apply, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro q hq
  rw [norm_mul]
  calc
    _ ≤ ‖phaseMobiusCoeff τ q.1‖ * (2 * ArithmeticFunction.vonMangoldt q.2) :=
      mul_le_mul_of_nonneg_left
        (norm_twisted_mangoldt_difference_le τ
          (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hq)))
        (norm_nonneg _)
    _ = 2 * (phaseMobiusAbs τ q.1 * ArithmeticFunction.vonMangoldt q.2) := by
      rw [phaseMobiusAbs_apply]
      ring

/-- Chebyshev controls the logarithmically weighted mean, uniformly in the phase. -/
theorem sum_phaseMobiusAbs_mul_log_le {x : ℝ} (hx : 0 ≤ x) (τ : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusAbs τ n * Real.log n) ≤
      2 * (Real.log 4 + 4) * x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusAbs τ n / n := by
  have hI (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hconv : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (phaseMobiusAbs τ * ArithmeticFunction.vonMangoldt) n) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusAbs τ d * Chebyshev.psi (x / d) := by
    simpa only [Chebyshev.psi, Nat.floor_div_natCast, hI] using
      sum_Ioc_mul_eq_sum_sum (phaseMobiusAbs τ) ArithmeticFunction.vonMangoldt ⌊x⌋₊
  calc
    _ ≤ 2 * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (phaseMobiusAbs τ * ArithmeticFunction.vonMangoldt) n := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun n _ => phaseMobiusAbs_mul_log_le_convolution τ n)
    _ = 2 * ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusAbs τ d * Chebyshev.psi (x / d) := by rw [hconv]
    _ ≤ 2 * ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
        phaseMobiusAbs τ d * ((Real.log 4 + 4) * (x / d)) := by
      apply mul_le_mul_of_nonneg_left _ zero_le_two
      apply Finset.sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left
        (Chebyshev.psi_le_const_mul_self (div_nonneg hx (Nat.cast_nonneg d)))
        (phaseMobiusAbs_nonneg τ d)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring

/-- The elementary multiplicative coefficient mean estimate required by the source comparison.
The absolute constant is explicit; no coefficient mean bound is a premise. -/
theorem sum_phaseMobiusAbs_le {x : ℝ} (hx : 1 < x) (τ : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusAbs τ n) ≤
      (2 * (Real.log 4 + 4) + 1) * x / Real.log x *
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusAbs τ n / n := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : Real.log x * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusAbs τ n) ≤
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusAbs τ n * Real.log n) +
        x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusAbs τ n / n := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hb := Real.log_le_self (div_pos hx0 hn0).le
    rw [Real.log_div hx0.ne' hn0.ne'] at hb
    have hm := mul_le_mul_of_nonneg_left hb (phaseMobiusAbs_nonneg τ n)
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith [hm]
  have hweighted := sum_phaseMobiusAbs_mul_log_le hx0.le τ
  have h := hlog.trans (add_le_add hweighted le_rfl)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (Real.log_pos hx)).mpr
  convert h using 1 <;> ring

/-- The actual reciprocal-weighted coefficient in the source Euler product. -/
def phaseMobiusWeight (τ : ℝ) (n : ℕ) : ℝ := phaseMobiusAbs τ n / n

theorem phaseMobiusWeight_nonneg (τ : ℝ) (n : ℕ) : 0 ≤ phaseMobiusWeight τ n :=
  div_nonneg (phaseMobiusAbs_nonneg τ n) (Nat.cast_nonneg n)

@[simp] theorem phaseMobiusWeight_one (τ : ℝ) : phaseMobiusWeight τ 1 = 1 := by
  simp [phaseMobiusWeight, (isMultiplicative_phaseMobiusCoeff τ).map_one]

theorem phaseMobiusWeight_mul (τ : ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    phaseMobiusWeight τ (m * n) = phaseMobiusWeight τ m * phaseMobiusWeight τ n := by
  rw [phaseMobiusWeight, (isMultiplicative_phaseMobiusAbs τ).map_mul_of_coprime hmn,
    Nat.cast_mul, ← div_mul_div_comm]
  rfl

/-- Each local factor is a convergent geometric series with its exact source value. -/
theorem hasSum_phaseMobiusWeight_prime_pow (τ : ℝ) {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => phaseMobiusWeight τ (p ^ k))
      (1 + ‖zetaTerm τ p - 1‖ / ((p : ℝ) - 1)) := by
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hratio : |1 / (p : ℝ)| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_lt_one (zero_lt_one.trans hpR)).mpr hpR
  have hg := (hasSum_geometric_of_norm_lt_one (ξ := (1 / (p : ℝ)))
    (by simpa only [Real.norm_eq_abs] using hratio)).mul_left
    (‖zetaTerm τ p - 1‖ / (p : ℝ))
  have ht : HasSum (fun k : ℕ => phaseMobiusWeight τ (p ^ (k + 1)))
      (‖zetaTerm τ p - 1‖ / ((p : ℝ) - 1)) := by
    convert hg using 1
    · funext k
      rw [phaseMobiusWeight, phaseMobiusAbs_apply, norm_phaseMobiusCoeff_prime_pow τ hp,
        Nat.cast_pow, pow_succ, one_div_pow]
      ring
    · field_simp [hp0, sub_ne_zero.mpr hpR.ne']
  simpa only [pow_zero, phaseMobiusWeight_one] using
    (HasSum.zero_add (f := fun k : ℕ => phaseMobiusWeight τ (p ^ k)) ht)

/-- A finite Euler-product majorant; no convergence of the unrestricted series at one is assumed. -/
theorem sum_phaseMobiusWeight_le_eulerProduct (τ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, phaseMobiusWeight τ n) ≤
      ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (1 + ‖zetaTerm τ p - 1‖ / ((p : ℝ) - 1)) := by
  let s := Finset.Icc 1 N
  have hs (n : ℕ) (hn : n ∈ s) : n ∈ Nat.factoredNumbers s := by
    apply Nat.mem_factoredNumbers_iff_forall_le.mpr
    refine ⟨by have := (Finset.mem_Icc.mp hn).1; omega, ?_⟩
    intro p hpn hp _
    exact Finset.mem_Icc.mpr ⟨hp.one_lt.le, hpn.trans (Finset.mem_Icc.mp hn).2⟩
  have heuler := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (phaseMobiusWeight_one τ) (fun {_ _} h => phaseMobiusWeight_mul τ h)
    (fun {p} hp => (hasSum_phaseMobiusWeight_prime_pow τ hp).summable.congr
      (fun k => (Real.norm_of_nonneg (phaseMobiusWeight_nonneg τ (p ^ k))).symm)) s
  have hfinite : (∑ n ∈ s, phaseMobiusWeight τ n) ≤
      ∏ p ∈ s.filter Nat.Prime, ∑' k : ℕ, phaseMobiusWeight τ (p ^ k) := by
    rw [← Finset.sum_subtype_of_mem (phaseMobiusWeight τ) hs]
    exact sum_le_hasSum _ (fun n _ => phaseMobiusWeight_nonneg τ n) heuler.2
  calc
    _ ≤ ∏ p ∈ s.filter Nat.Prime, ∑' k : ℕ, phaseMobiusWeight τ (p ^ k) := hfinite
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (hasSum_phaseMobiusWeight_prime_pow τ (Finset.mem_filter.mp hp).2).tsum_eq

/-- The higher prime powers contribute a uniformly summable correction. -/
theorem phase_prime_factor_error_le (τ : ℝ) {p : ℕ} (hp : p.Prime) :
    ‖zetaTerm τ p - 1‖ / ((p : ℝ) - 1) ≤
      ‖zetaTerm τ p - 1‖ / p + 4 / (p : ℝ) ^ 2 := by
  have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p : ℝ) := by positivity
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have ha : ‖zetaTerm τ p - 1‖ ≤ 2 := by
    have h := norm_sub_le (zetaTerm τ p) 1
    rw [norm_zetaTerm τ hp.pos, norm_one] at h
    linarith
  have heq : ‖zetaTerm τ p - 1‖ / ((p : ℝ) - 1) =
      ‖zetaTerm τ p - 1‖ / p + ‖zetaTerm τ p - 1‖ / ((p : ℝ) * (p - 1)) := by
    field_simp
    ring
  rw [heq]
  apply add_le_add le_rfl
  apply (div_le_div_iff₀ (mul_pos hp0 hp1) (sq_pos_of_pos hp0)).mpr
  nlinarith [mul_le_mul_of_nonneg_right ha (sq_nonneg (p : ℝ)),
    mul_nonneg hp0.le (sub_nonneg.mpr hp2)]

/-- The source Euler-product majorant with an explicit absolute constant. -/
theorem sum_phaseMobiusWeight_le_exp_prime (τ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, phaseMobiusWeight τ n) ≤
      Real.exp (8 + ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ‖1 - zetaTerm τ p‖ / p) := by
  let primes := (Finset.Icc 1 N).filter Nat.Prime
  have hseries : (∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ 2)⁻¹) ≤ 2 := by
    have hset : Finset.Ioo 0 (N + 1) = Finset.Icc 1 N := by
      ext n
      simp only [Finset.mem_Ioo, Finset.mem_Icc]
      omega
    simpa only [hset, Nat.cast_zero, zero_add, div_one] using
      (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))
  have hcorrection : (∑ p ∈ primes, 4 / (p : ℝ) ^ 2) ≤ 8 := by
    calc
      _ = 4 * ∑ p ∈ primes, ((p : ℝ) ^ 2)⁻¹ := by simp only [Finset.mul_sum, div_eq_mul_inv]
      _ ≤ 4 * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => by positivity)
      _ ≤ 4 * 2 := mul_le_mul_of_nonneg_left hseries (by norm_num)
      _ = 8 := by norm_num
  have hexponent : (∑ p ∈ primes, ‖zetaTerm τ p - 1‖ / ((p : ℝ) - 1)) ≤
      8 + ∑ p ∈ primes, ‖1 - zetaTerm τ p‖ / p := by
    calc
      _ ≤ ∑ p ∈ primes, (‖zetaTerm τ p - 1‖ / p + 4 / (p : ℝ) ^ 2) :=
        Finset.sum_le_sum (fun p hp => phase_prime_factor_error_le τ (Finset.mem_filter.mp hp).2)
      _ = (∑ p ∈ primes, ‖1 - zetaTerm τ p‖ / p) +
          ∑ p ∈ primes, 4 / (p : ℝ) ^ 2 := by
        simp only [Finset.sum_add_distrib, norm_sub_rev]
      _ ≤ _ := by linarith
  calc
    _ ≤ ∏ p ∈ primes, (1 + ‖zetaTerm τ p - 1‖ / ((p : ℝ) - 1)) :=
      sum_phaseMobiusWeight_le_eulerProduct τ N
    _ ≤ ∏ p ∈ primes, Real.exp (‖zetaTerm τ p - 1‖ / ((p : ℝ) - 1)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
        exact add_nonneg zero_le_one (div_nonneg (norm_nonneg _) (by linarith))
      · intro p _
        simpa only [add_comm] using Real.add_one_le_exp (‖zetaTerm τ p - 1‖ / ((p : ℝ) - 1))
    _ = Real.exp (∑ p ∈ primes, ‖zetaTerm τ p - 1‖ / ((p : ℝ) - 1)) :=
      (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

/-- Abel summation converts a nonnegative coefficient mean bound on the actual interval
into a reciprocal tail bound. The zero coefficient need not be discarded implicitly. -/
theorem reciprocal_tail_le_of_mean_bound (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    {a b K : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmean : ∀ u ∈ Set.Icc a b, (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, c n) ≤ K * u) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c n / n) ≤ K * (1 + Real.log (b / a)) := by
  open MeasureTheory in
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) :=
    (continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1)))
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) :=
    hcont.integrableOn_Icc
  have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun u : ℝ => u⁻¹) t :=
    fun t ht => (hasDerivAt_inv (ne_of_gt (ha.trans_le ht.1))).differentiableAt
  have habSum := sum_mul_eq_sub_sub_integral_mul c ha.le hab hdiff
    (by simpa only [deriv_inv'] using hint.neg)
  simp only [deriv_inv, neg_mul, MeasureTheory.integral_neg, sub_neg_eq_add] at habSum
  have hzero : 0 ≤ a⁻¹ * ∑ n ∈ Finset.Icc 0 ⌊a⌋₊, c n := by
    exact mul_nonneg (inv_nonneg.mpr ha.le) (Finset.sum_nonneg (fun n _ => hc n))
  have htop : b⁻¹ * (∑ n ∈ Finset.Icc 0 ⌊b⌋₊, c n) ≤ K := by
    calc
      _ ≤ b⁻¹ * (K * b) := mul_le_mul_of_nonneg_left
        (hmean b ⟨hab, le_rfl⟩) (inv_nonneg.mpr (ha.le.trans hab))
      _ = K := by field_simp [ne_of_gt (ha.trans_le hab)]
  have hintegrand := integrableOn_mul_sum_Icc c (m := 0) ha.le hint
  have hmajorant : MeasureTheory.IntegrableOn (fun t : ℝ => K * t⁻¹) (Set.Icc a b) :=
    ((continuousOn_const.mul (continuousOn_id.inv₀
      (fun t ht => ne_of_gt (ha.trans_le ht.1)))).integrableOn_Icc)
  have hintegral :
      (∫ t in Set.Ioc a b, (t ^ 2)⁻¹ * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) ≤
        K * Real.log (b / a) := by
    calc
      _ ≤ ∫ t in Set.Ioc a b, K * t⁻¹ := by
        apply MeasureTheory.setIntegral_mono_on
          (hintegrand.mono_set Set.Ioc_subset_Icc_self)
          (hmajorant.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc
        intro t ht
        calc
          _ ≤ (t ^ 2)⁻¹ * (K * t) := mul_le_mul_of_nonneg_left
            (hmean t ⟨ht.1.le, ht.2⟩) (by positivity)
          _ = _ := by field_simp [ne_of_gt (ha.trans ht.1)]
      _ = K * Real.log (b / a) := by
        rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const_mul,
          integral_inv_of_pos ha (ha.trans_le hab)]
  have heq : (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c n / n) =
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (n : ℝ)⁻¹ * c n := by
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [heq, habSum]
  nlinarith

/-- The reciprocal coefficient sum is monotone in its real cutoff. -/
theorem sum_phaseMobiusWeight_mono (τ : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, phaseMobiusWeight τ n) ≤
      ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, phaseMobiusWeight τ n := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hab))
    (fun n _ _ => phaseMobiusWeight_nonneg τ n)

/-- The source reciprocal tail estimate for the genuine Möbius coefficients,
with the mean-value hypothesis fully discharged. -/
theorem sum_phaseMobiusWeight_tail_le (τ : ℝ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, phaseMobiusWeight τ n) ≤
      (2 * (Real.log 4 + 4) + 1) / Real.log a *
        (∑ n ∈ Finset.Icc 1 ⌊b⌋₊, phaseMobiusWeight τ n) * (1 + Real.log (b / a)) := by
  apply reciprocal_tail_le_of_mean_bound (phaseMobiusAbs τ) (phaseMobiusAbs_nonneg τ)
    (zero_lt_one.trans ha) hab
  intro u hu
  have hu1 : 1 < u := ha.trans_le hu.1
  have hsum : (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, phaseMobiusAbs τ n) =
      ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, phaseMobiusAbs τ n := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
    simp only [ArithmeticFunction.map_zero, zero_add]
    congr 1
  rw [hsum]
  have hC : 0 ≤ 2 * (Real.log 4 + 4) + 1 := by positivity
  have hlog : Real.log a ≤ Real.log u := Real.log_le_log (zero_lt_one.trans ha) hu.1
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hu0 : 0 < u := zero_lt_one.trans hu1
  calc
    _ ≤ (2 * (Real.log 4 + 4) + 1) * u / Real.log u *
        ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, phaseMobiusWeight τ n := sum_phaseMobiusAbs_le hu1 τ
    _ ≤ (2 * (Real.log 4 + 4) + 1) * u / Real.log a *
        ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, phaseMobiusWeight τ n := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_left (mul_nonneg hC (zero_lt_one.trans hu1).le)
          (Real.log_pos ha) hlog
      · exact sum_phaseMobiusWeight_mono τ hu.2
      · exact Finset.sum_nonneg (fun n _ => phaseMobiusWeight_nonneg τ n)
      · positivity
    _ = _ := by ring

/-- Splitting the actual comparison error at a real cutoff consumes both coefficient estimates. -/
theorem norm_mean_comparison_le_split (τ α : ℝ) {a x : ℝ}
    (ha : 1 < a) (hax : a ≤ x) :
    ‖zetaSum x (τ + α) - comparisonFactor x α * zetaSum x τ‖ ≤
      ((5 * (1 + α ^ 2)) * ((2 * (Real.log 4 + 4) + 1) * a / Real.log a) +
        2 * x * ((2 * (Real.log 4 + 4) + 1) / Real.log a) * (1 + Real.log (x / a))) *
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusWeight τ n := by
  have hx : 0 < x := (zero_lt_one.trans ha).trans_le hax
  have hfloor : ⌊a⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hax
  have hsplit : Finset.Icc 1 ⌊x⌋₊ = Finset.Icc 1 ⌊a⌋₊ ∪ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisjoint : Disjoint (Finset.Icc 1 ⌊a⌋₊) (Finset.Ioc ⌊a⌋₊ ⌊x⌋₊) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have := (Finset.mem_Icc.mp hn).2
    have := (Finset.mem_Ioc.mp hn').1
    omega
  have hshort : (∑ d ∈ Finset.Icc 1 ⌊a⌋₊,
      ‖phaseMobiusCoeff τ d‖ * min (5 * (1 + α ^ 2)) (2 * (x / d))) ≤
      5 * (1 + α ^ 2) * ((2 * (Real.log 4 + 4) + 1) * a / Real.log a) *
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusWeight τ n := by
    calc
      _ ≤ 5 * (1 + α ^ 2) * ∑ d ∈ Finset.Icc 1 ⌊a⌋₊, phaseMobiusAbs τ d := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d _
        calc
          _ ≤ ‖phaseMobiusCoeff τ d‖ * (5 * (1 + α ^ 2)) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) (norm_nonneg _)
          _ = _ := by rw [phaseMobiusAbs_apply]; ring
      _ ≤ 5 * (1 + α ^ 2) *
          (((2 * (Real.log 4 + 4) + 1) * a / Real.log a) *
            ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, phaseMobiusWeight τ n) :=
        mul_le_mul_of_nonneg_left (sum_phaseMobiusAbs_le ha τ) (by positivity)
      _ ≤ _ := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_left (sum_phaseMobiusWeight_mono τ hax)
        have := Real.log_pos ha
        have := zero_lt_one.trans ha
        positivity
  have hlong : (∑ d ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊,
      ‖phaseMobiusCoeff τ d‖ * min (5 * (1 + α ^ 2)) (2 * (x / d))) ≤
      2 * x * ((2 * (Real.log 4 + 4) + 1) / Real.log a) * (1 + Real.log (x / a)) *
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusWeight τ n := by
    calc
      _ ≤ 2 * x * ∑ d ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊, phaseMobiusWeight τ d := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d _
        calc
          _ ≤ ‖phaseMobiusCoeff τ d‖ * (2 * (x / d)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg _)
          _ = _ := by rw [phaseMobiusWeight, phaseMobiusAbs_apply]; ring
      _ ≤ 2 * x * (((2 * (Real.log 4 + 4) + 1) / Real.log a) *
          (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusWeight τ n) * (1 + Real.log (x / a))) :=
        mul_le_mul_of_nonneg_left (sum_phaseMobiusWeight_tail_le τ ha hax) (by positivity)
      _ = _ := by ring
  apply (norm_mean_comparison_le_mobius_error hx τ α).trans
  nth_rw 1 [hsplit]
  rw [Finset.sum_union hdisjoint]
  calc
    _ ≤ _ := add_le_add hshort hlong
    _ = _ := by ring

/-- Uniform logarithmic comparison error for the actual sums, with all coefficient
mean and tail estimates discharged. This is the coefficient form of GS03 Lemma 7.1. -/
theorem norm_mean_comparison_le_log_weight (τ α : ℝ) {x : ℝ} (hx : 1 < x) :
    ‖zetaSum x (τ + α) - comparisonFactor x α * zetaSum x τ‖ ≤
      14 * (2 * (Real.log 4 + 4) + 1) * x / Real.log x *
        (1 + Real.log (1 + α ^ 2)) *
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusWeight τ n := by
  let K := 1 + α ^ 2
  let C := 2 * (Real.log 4 + 4) + 1
  let W := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, phaseMobiusWeight τ n
  have hK1 : 1 ≤ K := by dsimp [K]; nlinarith [sq_nonneg α]
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  have hC1 : 1 ≤ C := by
    have h : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    dsimp [C]
    linarith
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  have hW : 0 ≤ W := Finset.sum_nonneg (fun n _ => phaseMobiusWeight_nonneg τ n)
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  change _ ≤ 14 * C * x / Real.log x * (1 + Real.log K) * W
  by_cases hsmall : K ^ 2 ≤ x
  · have hKx : K < x := by nlinarith
    have ha : 1 < x / K := (lt_div_iff₀ hK0).mpr (by simpa using hKx)
    have hax : x / K ≤ x := div_le_self hx0.le hK1
    have hloghalf : 2 * Real.log K ≤ Real.log x := by
      have h := Real.log_le_log (sq_pos_of_pos hK0) hsmall
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    have hloga : Real.log (x / K) = Real.log x - Real.log K :=
      Real.log_div hx0.ne' hK0.ne'
    have hratio : x / (x / K) = K := by field_simp
    have hsplit := norm_mean_comparison_le_split τ α ha hax
    change _ ≤ (5 * K * (C * (x / K) / Real.log (x / K)) +
      2 * x * (C / Real.log (x / K)) * (1 + Real.log (x / (x / K)))) * W at hsplit
    rw [hratio] at hsplit
    have heq : 5 * K * (C * (x / K) / Real.log (x / K)) +
        2 * x * (C / Real.log (x / K)) * (1 + Real.log K) =
          C * x / Real.log (x / K) * (7 + 2 * Real.log K) := by
      field_simp
      ring
    rw [heq] at hsplit
    have hdenom : C * x / Real.log (x / K) ≤ 2 * (C * x / Real.log x) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (Real.log_pos ha) hlogx).mpr
      rw [hloga]
      nlinarith [mul_nonneg (mul_nonneg hC0 hx0.le) (sub_nonneg.mpr hloghalf)]
    have hcore : C * x / Real.log (x / K) * (7 + 2 * Real.log K) ≤
        14 * C * x / Real.log x * (1 + Real.log K) := by
      calc
        _ ≤ 2 * (C * x / Real.log x) * (7 + 2 * Real.log K) :=
          mul_le_mul_of_nonneg_right hdenom (by positivity)
        _ ≤ 14 * (C * x / Real.log x) * (1 + Real.log K) := by
          have hnonneg : 0 ≤ C * x / Real.log x := by positivity
          nlinarith [mul_nonneg hnonneg hlogK]
        _ = _ := by ring
    exact hsplit.trans (mul_le_mul_of_nonneg_right hcore hW)
  · have htrivial : ‖zetaSum x (τ + α) - comparisonFactor x α * zetaSum x τ‖ ≤ 2 * x * W := by
      apply (norm_mean_comparison_le_mobius_error hx0 τ α).trans
      rw [show 2 * x * W = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
        2 * x * phaseMobiusWeight τ d by dsimp only [W]; rw [Finset.mul_sum]]
      apply Finset.sum_le_sum
      intro d _
      calc
        _ ≤ ‖phaseMobiusCoeff τ d‖ * (2 * (x / d)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg _)
        _ = _ := by rw [phaseMobiusWeight, phaseMobiusAbs_apply]; ring
    have hlarge : Real.log x ≤ 2 * Real.log K := by
      have h := Real.log_le_log hx0 (le_of_lt (lt_of_not_ge hsmall))
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    have hfactor : 2 * x ≤ 14 * C * x / Real.log x * (1 + Real.log K) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hlogx).mpr
      have hstep : 2 * Real.log x ≤ 14 * C * (1 + Real.log K) := by
        have h := mul_le_mul_of_nonneg_right hC1 (show 0 ≤ 1 + Real.log K by positivity)
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hstep hx0.le]
    exact htrivial.trans (mul_le_mul_of_nonneg_right hfactor hW)

/-- GS03 Lemma 7.1 specialized to the actual completely multiplicative phases,
with an explicit absolute constant and no restriction on the twisting parameter. -/
theorem norm_mean_comparison_le_prime_error (τ α : ℝ) {x : ℝ} (hx : 1 < x) :
    ‖zetaSum x (τ + α) - comparisonFactor x α * zetaSum x τ‖ ≤
      (42 * (2 * (Real.log 4 + 4) + 1) * Real.exp 8) * x *
        Real.log (Real.exp 1 + |α|) / Real.log x *
          Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - zetaTerm τ p‖ / p) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr zero_le_one
  have hlogb : 1 ≤ Real.log (Real.exp 1 + |α|) := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right (abs_nonneg α))
    simpa only [Real.log_exp] using h
  have hlogs : 1 + Real.log (1 + α ^ 2) ≤ 3 * Real.log (Real.exp 1 + |α|) := by
    have hsquare : 1 + α ^ 2 ≤ (Real.exp 1 + |α|) ^ 2 := by
      nlinarith [sq_abs α, mul_nonneg (Real.exp_pos 1).le (abs_nonneg α)]
    have h := Real.log_le_log (show 0 < 1 + α ^ 2 by positivity) hsquare
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hbase := norm_mean_comparison_le_log_weight τ α hx
  have hC : 0 ≤ 14 * (2 * (Real.log 4 + 4) + 1) * x / Real.log x := by positivity
  have hfactor : 0 ≤ 14 * (2 * (Real.log 4 + 4) + 1) * x / Real.log x *
      (3 * Real.log (Real.exp 1 + |α|)) := mul_nonneg hC (by linarith)
  apply hbase.trans
  calc
    _ ≤ (14 * (2 * (Real.log 4 + 4) + 1) * x / Real.log x *
        (3 * Real.log (Real.exp 1 + |α|))) *
        Real.exp (8 + ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - zetaTerm τ p‖ / p) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hlogs hC
      · exact sum_phaseMobiusWeight_le_exp_prime τ ⌊x⌋₊
      · exact Finset.sum_nonneg (fun n _ => phaseMobiusWeight_nonneg τ n)
      · exact hfactor
    _ = _ := by rw [Real.exp_add]; ring

/-- The paper's normalized mean-comparison formula (2.2) for `f(n)=n^(it)`.
The error constant is absolute, and the spectral difference is the actual `t - t₀`. -/
theorem norm_normalized_mean_comparison_le (t t₀ : ℝ) {x : ℝ} (hx : 1 < x) :
    ‖zetaSum x t / (x : ℂ) - comparisonFactor x t₀ * (zetaSum x (t - t₀) / (x : ℂ))‖ ≤
      (42 * (2 * (Real.log 4 + 4) + 1) * Real.exp 8) *
        Real.log (Real.exp 1 + |t₀|) / Real.log x *
          Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ‖1 - zetaTerm (t - t₀) p‖ / p) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have heq : zetaSum x t / (x : ℂ) - comparisonFactor x t₀ * (zetaSum x (t - t₀) / (x : ℂ)) =
      (zetaSum x t - comparisonFactor x t₀ * zetaSum x (t - t₀)) / (x : ℂ) := by ring
  rw [heq, norm_div, Complex.norm_real, Real.norm_of_nonneg hx0.le]
  apply (div_le_iff₀ hx0).mpr
  have h := norm_mean_comparison_le_prime_error (t - t₀) t₀ hx
  rw [sub_add_cancel] at h
  convert h using 1
  ring

end
end DongWangWangZhang2026
