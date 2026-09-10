import Tao2026.PrimeEquidistribution
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Reciprocal phases for the Vinogradov estimate

This module develops the exact phase `N/t + M/t^j` and the finite integer
exponential sums occurring in Proposition 1.12(i) of the pinned Singmaster
paper.  The derivative formula is the first analytic input to both the
high-derivative Vinogradov estimate and the fixed-degree Weyl estimate.
-/

open Complex Finset Set
open scoped BigOperators ComplexConjugate

namespace Tao2026

noncomputable section

/-- The standard additive character `e(x) = exp(2πix)`. -/
def standardAdditiveCharacter (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * x)

/-- The standard additive character is continuous. -/
theorem continuous_standardAdditiveCharacter :
    Continuous standardAdditiveCharacter := by
  unfold standardAdditiveCharacter
  have hargument : Continuous
      (fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  simpa [mul_assoc] using hargument.cexp

@[simp]
theorem norm_standardAdditiveCharacter (x : ℝ) :
    ‖standardAdditiveCharacter x‖ = 1 := by
  rw [standardAdditiveCharacter, Complex.norm_exp]
  simp

theorem standardAdditiveCharacter_add (x y : ℝ) :
    standardAdditiveCharacter (x + y) =
    standardAdditiveCharacter x * standardAdditiveCharacter y := by
  rw [standardAdditiveCharacter, standardAdditiveCharacter,
    standardAdditiveCharacter, Complex.ofReal_add, mul_add, Complex.exp_add]

/-- The standard additive character is one on every integer. -/
@[simp]
theorem standardAdditiveCharacter_int (m : ℤ) :
    standardAdditiveCharacter (m : ℝ) = 1 := by
  unfold standardAdditiveCharacter
  rw [show
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
          push_cast
          ring_nf]
  exact Complex.exp_int_mul_two_pi_mul_I m

/-- Integer translation does not change the standard additive character. -/
@[simp]
theorem standardAdditiveCharacter_add_int (x : ℝ) (m : ℤ) :
    standardAdditiveCharacter (x + m) = standardAdditiveCharacter x := by
  rw [standardAdditiveCharacter_add, standardAdditiveCharacter_int, mul_one]

/-- The standard additive character is globally Lipschitz, with the exact
normalization constant coming from `e(x) = exp(2πix)`. -/
theorem norm_standardAdditiveCharacter_sub_le (x y : ℝ) :
    ‖standardAdditiveCharacter x - standardAdditiveCharacter y‖ ≤
      2 * Real.pi * |x - y| := by
  have hfactor :
      standardAdditiveCharacter x - standardAdditiveCharacter y =
        standardAdditiveCharacter y *
          (standardAdditiveCharacter (x - y) - 1) := by
    rw [mul_sub, mul_one, ← standardAdditiveCharacter_add]
    congr 1
    ring_nf
  rw [hfactor, norm_mul, norm_standardAdditiveCharacter, one_mul]
  unfold standardAdditiveCharacter
  have hexponent :
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((x - y : ℝ) : ℂ) =
        Complex.I * ((2 * Real.pi * (x - y) : ℝ) : ℂ) := by
    push_cast
    ring_nf
  rw [hexponent]
  calc
    ‖Complex.exp (Complex.I * (2 * Real.pi * (x - y) : ℝ)) - 1‖ ≤
        ‖(2 * Real.pi * (x - y) : ℝ)‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |x - y| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
        abs_of_nonneg Real.pi_pos.le]

theorem standardAdditiveCharacter_neg (x : ℝ) :
    standardAdditiveCharacter (-x) =
      conj (standardAdditiveCharacter x) := by
  rw [standardAdditiveCharacter, standardAdditiveCharacter,
    ← Complex.exp_conj]
  apply congrArg Complex.exp
  simp only [map_mul, Complex.conj_ofNat, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_neg]
  ring

/-- Multiplication by the conjugate converts a phase pair into its
difference, as in the Type II Cauchy--Schwarz expansion. -/
theorem standardAdditiveCharacter_mul_conj (x y : ℝ) :
    standardAdditiveCharacter x * conj (standardAdditiveCharacter y) =
      standardAdditiveCharacter (x - y) := by
  rw [← standardAdditiveCharacter_neg,
    ← standardAdditiveCharacter_add]
  congr 1

/-- The source phase, written with integer powers so that all higher
derivatives have a uniform algebraic form. -/
def reciprocalPhase (N M : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  N * t ^ (-1 : ℤ) + M * t ^ (-(j : ℤ))

/-- The scale `F = |N|/X + |M|/X^j` in the integer exponential-sum
proposition of the pinned source. -/
def reciprocalPhaseScale (N M : ℝ) (j : ℕ) (X : ℝ) : ℝ :=
  |N| / X + |M| / X ^ j

theorem reciprocalPhaseScale_nonneg
    (N M : ℝ) (j : ℕ) {X : ℝ} (hX : 0 < X) :
    0 ≤ reciprocalPhaseScale N M j X := by
  exact add_nonneg (div_nonneg (abs_nonneg N) hX.le)
    (div_nonneg (abs_nonneg M) (pow_pos hX j).le)

theorem reciprocalPhase_eq_div
    (N M : ℝ) (j : ℕ) (t : ℝ) :
    reciprocalPhase N M j t = N / t + M / t ^ j := by
  simp [reciprocalPhase, zpow_neg, div_eq_mul_inv]

/-- The source's reduction of `j = 1` to `j = 2`: the two reciprocal-linear
coefficients combine, and the quadratic reciprocal coefficient is set to
zero. -/
theorem reciprocalPhase_one_eq_absorb (N M t : ℝ) :
    reciprocalPhase N M 1 t = reciprocalPhase (N + M) 0 2 t := by
  rw [reciprocalPhase_eq_div, reciprocalPhase_eq_div]
  norm_num
  ring

/-- Type I rescaling of the reciprocal phase after writing the summation
variable as a product. -/
theorem reciprocalPhase_mul_rescale
    (N M : ℝ) (j : ℕ) (m n : ℝ) :
    reciprocalPhase N M j (m * n) =
      reciprocalPhase (N / m) (M / m ^ j) j n := by
  simp [reciprocalPhase_eq_div, mul_pow, div_div]

/-- Exact correlation-phase identity used after Cauchy--Schwarz in the Type II
estimate.  It is the source's displayed formula for `X_{n,n'}`. -/
theorem reciprocalPhase_mul_sub_mul
    (N M : ℝ) (j : ℕ) {m n n' : ℝ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    reciprocalPhase N M j (m * n) -
        reciprocalPhase N M j (m * n') =
      reciprocalPhase
        (N * (n' - n) / (n * n'))
        (M * (n' ^ j - n ^ j) / (n ^ j * n' ^ j)) j m := by
  rw [reciprocalPhase_eq_div, reciprocalPhase_eq_div,
    reciprocalPhase_eq_div]
  field_simp [hm, hn, hn']
  ring

/-- Additive-character version of the exact Type II correlation phase. -/
theorem standardAdditiveCharacter_reciprocalPhase_mul_conj
    (N M : ℝ) (j : ℕ) {m n n' : ℝ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    standardAdditiveCharacter (reciprocalPhase N M j (m * n)) *
        conj (standardAdditiveCharacter
          (reciprocalPhase N M j (m * n'))) =
      standardAdditiveCharacter
        (reciprocalPhase
          (N * (n' - n) / (n * n'))
          (M * (n' ^ j - n ^ j) / (n ^ j * n' ^ j)) j m) := by
  rw [standardAdditiveCharacter_mul_conj,
    reciprocalPhase_mul_sub_mul N M j hm hn hn']

/-- A finite exponential sum on the half-open integer interval `[a,b)`. -/
def reciprocalPhaseSum (N M : ℝ) (j a b : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (reciprocalPhase N M j n)

/-- Finite exponential-sum form of `reciprocalPhase_one_eq_absorb`. -/
theorem reciprocalPhaseSum_one_eq_absorb (N M : ℝ) (a b : ℕ) :
    reciprocalPhaseSum N M 1 a b =
      reciprocalPhaseSum (N + M) 0 2 a b := by
  unfold reciprocalPhaseSum
  apply Finset.sum_congr rfl
  intro n _hn
  rw [reciprocalPhase_one_eq_absorb]

theorem norm_reciprocalPhaseSum_le_card (N M : ℝ) (j a b : ℕ) :
    ‖reciprocalPhaseSum N M j a b‖ ≤ (Finset.Ico a b).card := by
  calc
    ‖reciprocalPhaseSum N M j a b‖ ≤
        ∑ n ∈ Finset.Ico a b,
          ‖standardAdditiveCharacter (reciprocalPhase N M j n)‖ := by
      exact norm_sum_le _ _
    _ = (Finset.Ico a b).card := by simp

/-- The coefficient in the `r`-th derivative of the monomial `t^m`. -/
def zpowDerivativeCoefficient (m : ℤ) (r : ℕ) : ℝ :=
  ∏ i ∈ Finset.range r, ((m : ℝ) - i)

/-- For a negative natural exponent, the derivative coefficient is a signed
ascending factorial. -/
theorem zpowDerivativeCoefficient_neg_nat (j r : ℕ) :
    zpowDerivativeCoefficient (-(j : ℤ)) r =
      (-1 : ℝ) ^ r * (j.ascFactorial r : ℝ) := by
  induction r with
  | zero => simp [zpowDerivativeCoefficient]
  | succ r ih =>
      rw [zpowDerivativeCoefficient, Finset.prod_range_succ]
      change
        (∏ i ∈ Finset.range r, (((-(j : ℤ) : ℤ) : ℝ) - i)) *
            (((-(j : ℤ) : ℤ) : ℝ) - r) = _
      rw [show
        (∏ i ∈ Finset.range r, (((-(j : ℤ) : ℤ) : ℝ) - i)) =
          zpowDerivativeCoefficient (-(j : ℤ)) r by rfl]
      rw [ih, Nat.ascFactorial_succ, pow_succ]
      push_cast
      ring

/-- Exact higher derivative of an integer power at a positive real point. -/
theorem iteratedDeriv_zpow_of_pos
    (m : ℤ) (r : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv r (fun y : ℝ => y ^ m) t =
      zpowDerivativeCoefficient m r * t ^ (m - r) := by
  have hwithin := iteratedDerivWithin_zpow (𝕜 := ℝ) (s := Ioi 0) m r isOpen_Ioi ht
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioi ht] at hwithin
  exact hwithin

/-- The reciprocal phase is smooth to every finite order at each positive
point. -/
theorem contDiffAt_reciprocalPhase_of_pos
    (N M : ℝ) (j r : ℕ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ r (reciprocalPhase N M j) t := by
  have hpowOne : ContDiffAt ℝ r (fun y : ℝ => y ^ (-1 : ℤ)) t := by
    exact ((analyticAt_id.zpow ht.ne').contDiffAt.of_le le_top)
  have hpowJ : ContDiffAt ℝ r (fun y : ℝ => y ^ (-(j : ℤ))) t := by
    exact ((analyticAt_id.zpow ht.ne').contDiffAt.of_le le_top)
  exact (contDiffAt_const.mul hpowOne).add (contDiffAt_const.mul hpowJ)

/-- Exact `r`-th derivative of the reciprocal phase.  This is the formal
counterpart of equation (expint1) before its absolute-value normalization. -/
theorem iteratedDeriv_reciprocalPhase
    (N M : ℝ) (j r : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv r (reciprocalPhase N M j) t =
      N * (zpowDerivativeCoefficient (-1) r * t ^ ((-1 : ℤ) - r)) +
      M * (zpowDerivativeCoefficient (-(j : ℤ)) r *
        t ^ (-(j : ℤ) - r)) := by
  have hpowOne : ContDiffAt ℝ r (fun y : ℝ => y ^ (-1 : ℤ)) t := by
    exact ((analyticAt_id.zpow ht.ne').contDiffAt.of_le le_top)
  have hpowJ : ContDiffAt ℝ r (fun y : ℝ => y ^ (-(j : ℤ))) t := by
    exact ((analyticAt_id.zpow ht.ne').contDiffAt.of_le le_top)
  have htermOne : ContDiffAt ℝ r (fun y : ℝ => N * y ^ (-1 : ℤ)) t :=
    contDiffAt_const.mul hpowOne
  have htermJ : ContDiffAt ℝ r (fun y : ℝ => M * y ^ (-(j : ℤ))) t :=
    contDiffAt_const.mul hpowJ
  change iteratedDeriv r
      ((fun y : ℝ => N * y ^ (-1 : ℤ)) +
        (fun y : ℝ => M * y ^ (-(j : ℤ)))) t = _
  rw [iteratedDeriv_add htermOne htermJ]
  simp only [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_zpow_of_pos (-1) r ht,
    iteratedDeriv_zpow_of_pos (-(j : ℤ)) r ht]

/-- The preceding derivative formula with the coefficients converted to the
signed factorials used in the source proof. -/
theorem iteratedDeriv_reciprocalPhase_signedFactorial
    (N M : ℝ) (j r : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv r (reciprocalPhase N M j) t =
      N * ((-1 : ℝ) ^ r * (r.factorial : ℝ) *
        t ^ ((-1 : ℤ) - r)) +
      M * ((-1 : ℝ) ^ r * (j.ascFactorial r : ℝ) *
        t ^ (-(j : ℤ) - r)) := by
  have hcoeffOne : zpowDerivativeCoefficient (-1) r =
      (-1 : ℝ) ^ r * (r.factorial : ℝ) := by
    simpa using zpowDerivativeCoefficient_neg_nat 1 r
  rw [iteratedDeriv_reciprocalPhase N M j r ht, hcoeffOne,
    zpowDerivativeCoefficient_neg_nat j r]

/-- The scaled coefficient `M_r` used in equation (expint1). -/
def reciprocalPhaseHigherCoefficient (M : ℝ) (j r : ℕ) : ℝ :=
  (j.ascFactorial r : ℝ) / (r.factorial : ℝ) * M

/-- The ascending-factorial coefficient is exactly the binomial coefficient
`binom(r+j-1,j-1)` displayed in the pinned source. -/
theorem reciprocalPhaseHigherCoefficient_eq_choose
    (M : ℝ) {j r : ℕ} (hj : 1 ≤ j) :
    reciprocalPhaseHigherCoefficient M j r =
      ((r + j - 1).choose (j - 1) : ℕ) * M := by
  rw [reciprocalPhaseHigherCoefficient,
    Nat.ascFactorial_eq_factorial_mul_choose']
  push_cast
  have hfac : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hfac]
  have htop : j + r - 1 = r + (j - 1) := by omega
  have htop' : r + j - 1 = r + (j - 1) := by omega
  rw [htop, htop', Nat.choose_symm_add]
  ring

/-- The binomial multiplier in `M_r` is positive, as used in the source's
comparison of `M_r` with `M`. -/
theorem one_le_reciprocalPhaseHigherCoefficientMultiplier
    {j r : ℕ} (hj : 1 ≤ j) :
    1 ≤ (r + j - 1).choose (j - 1) := by
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.choose_ne_zero (by omega))

/-- The elementary source bound
`binom(r+j-1,j-1) ≤ (r+j)^r`. -/
theorem reciprocalPhaseHigherCoefficientMultiplier_le_pow
    {j r : ℕ} (hj : 1 ≤ j) :
    (r + j - 1).choose (j - 1) ≤ (r + j) ^ r := by
  have htop : r + j - 1 = r + (j - 1) := by omega
  rw [htop, Nat.add_comm r (j - 1), Nat.choose_symm_add]
  exact (Nat.choose_le_pow _ _).trans
    (Nat.pow_le_pow_left (by omega) _)

/-- Absolute-value form of the exact `M_r` coefficient. -/
theorem abs_reciprocalPhaseHigherCoefficient
    (M : ℝ) {j r : ℕ} (hj : 1 ≤ j) :
    |reciprocalPhaseHigherCoefficient M j r| =
      ((r + j - 1).choose (j - 1) : ℕ) * |M| := by
  rw [reciprocalPhaseHigherCoefficient_eq_choose M hj, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg _)]

/-- The lower comparison `|M| ≤ |M_r|`. -/
theorem abs_le_abs_reciprocalPhaseHigherCoefficient
    (M : ℝ) {j r : ℕ} (hj : 1 ≤ j) :
    |M| ≤ |reciprocalPhaseHigherCoefficient M j r| := by
  rw [abs_reciprocalPhaseHigherCoefficient M hj]
  have hmult : (1 : ℝ) ≤ ((r + j - 1).choose (j - 1) : ℕ) := by
    exact_mod_cast
      one_le_reciprocalPhaseHigherCoefficientMultiplier (r := r) hj
  calc
    |M| = 1 * |M| := by simp
    _ ≤ ((r + j - 1).choose (j - 1) : ℕ) * |M| :=
      mul_le_mul_of_nonneg_right hmult (abs_nonneg M)

/-- A nonzero reciprocal coefficient remains nonzero after passing to any
higher derivative order. -/
theorem reciprocalPhaseHigherCoefficient_ne_zero
    {M : ℝ} {j r : ℕ} (hj : 1 ≤ j) (hM : M ≠ 0) :
    reciprocalPhaseHigherCoefficient M j r ≠ 0 := by
  rw [reciprocalPhaseHigherCoefficient_eq_choose M hj]
  exact mul_ne_zero (by
    exact_mod_cast
      (Nat.ne_zero_of_lt
        (one_le_reciprocalPhaseHigherCoefficientMultiplier (r := r) hj))) hM

/-- The upper comparison `|M_r| ≤ (r+j)^r |M|` used before converting the
coefficient growth to exponential notation. -/
theorem abs_reciprocalPhaseHigherCoefficient_le_pow_mul
    (M : ℝ) {j r : ℕ} (hj : 1 ≤ j) :
    |reciprocalPhaseHigherCoefficient M j r| ≤
      ((r + j) ^ r : ℕ) * |M| := by
  rw [abs_reciprocalPhaseHigherCoefficient M hj]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast reciprocalPhaseHigherCoefficientMultiplier_le_pow hj)
    (abs_nonneg M)

/-- Factorized derivative form underlying the absolute-value normalization in
equation (expint1). -/
theorem iteratedDeriv_reciprocalPhase_factor
    (N M : ℝ) (j r : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv r (reciprocalPhase N M j) t =
      (-1 : ℝ) ^ r * (r.factorial : ℝ) * t ^ (-(r : ℤ)) *
        (N / t + reciprocalPhaseHigherCoefficient M j r / t ^ j) := by
  rw [iteratedDeriv_reciprocalPhase_signedFactorial N M j r ht]
  unfold reciprocalPhaseHigherCoefficient
  have ht0 : t ≠ 0 := ht.ne'
  have hpowOne : t ^ ((-1 : ℤ) - r) = (t ^ (r + 1))⁻¹ := by
    rw [show (-1 : ℤ) - r = -((r + 1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast]
  have hpowJ : t ^ (-(j : ℤ) - r) = (t ^ (j + r))⁻¹ := by
    rw [show -(j : ℤ) - r = -((j + r : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast]
  have hpowR : t ^ (-(r : ℤ)) = (t ^ r)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hpowOne, hpowJ, hpowR]
  simp only [div_eq_mul_inv]
  field_simp [ht0, Nat.factorial_ne_zero]
  ring

/-- Equation (expint1), with the source's `M_r` represented by its exact
ascending-factorial quotient. -/
theorem normalized_abs_iteratedDeriv_reciprocalPhase
    (N M : ℝ) (j r : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ r / (r.factorial : ℝ) *
        |iteratedDeriv r (reciprocalPhase N M j) t| =
      |N / t + reciprocalPhaseHigherCoefficient M j r / t ^ j| := by
  rw [iteratedDeriv_reciprocalPhase_factor N M j r ht]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_of_pos (by positivity : (0 : ℝ) < r.factorial),
    abs_of_pos (zpow_pos ht _)]
  have hpowR : t ^ (-(r : ℤ)) = (t ^ r)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hpowR]
  field_simp [ht.ne', Nat.factorial_ne_zero]

/-- The direct upper half of the derivative-size comparison in the source,
with the elementary polynomial bound on `M_r` made explicit. -/
theorem normalized_abs_iteratedDeriv_reciprocalPhase_le
    (N M : ℝ) {j r : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : 0 < t) :
    t ^ r / (r.factorial : ℝ) *
        |iteratedDeriv r (reciprocalPhase N M j) t| ≤
      |N| / t + (((r + j) ^ r : ℕ) : ℝ) * |M| / t ^ j := by
  rw [normalized_abs_iteratedDeriv_reciprocalPhase N M j r ht]
  calc
    |N / t + reciprocalPhaseHigherCoefficient M j r / t ^ j| ≤
        |N / t| + |reciprocalPhaseHigherCoefficient M j r / t ^ j| :=
      abs_add_le _ _
    _ = |N| / t + |reciprocalPhaseHigherCoefficient M j r| / t ^ j := by
      rw [abs_div, abs_div, abs_of_pos ht, abs_of_pos (pow_pos ht j)]
    _ ≤ |N| / t + (((r + j) ^ r : ℕ) : ℝ) * |M| / t ^ j := by
      exact add_le_add le_rfl <|
        div_le_div_of_nonneg_right
          (abs_reciprocalPhaseHigherCoefficient_le_pow_mul M hj)
          (pow_pos ht j).le

/-- Uniform source-scale upper bound on `[X,∞)`: the normalized derivative is
at most `(r+j)^r F`. -/
theorem normalized_abs_iteratedDeriv_reciprocalPhase_le_multiplier_scale
    (N M : ℝ) {j r : ℕ} (hj : 1 ≤ j) {X t : ℝ}
    (hX : 0 < X) (hXt : X ≤ t) :
    t ^ r / (r.factorial : ℝ) *
        |iteratedDeriv r (reciprocalPhase N M j) t| ≤
      (((r + j) ^ r : ℕ) : ℝ) * reciprocalPhaseScale N M j X := by
  have ht : 0 < t := hX.trans_le hXt
  let B : ℝ := (((r + j) ^ r : ℕ) : ℝ)
  have hB : 1 ≤ B := by
    dsimp [B]
    have hbase : r + j = (r + j - 1) + 1 := by omega
    rw [hbase]
    exact_mod_cast Nat.one_le_pow' r (r + j - 1)
  have hN : |N| / t ≤ |N| / X :=
    div_le_div_of_nonneg_left (abs_nonneg N) hX hXt
  have hpow : X ^ j ≤ t ^ j := pow_le_pow_left₀ hX.le hXt j
  have hM : B * |M| / t ^ j ≤ B * |M| / X ^ j :=
    div_le_div_of_nonneg_left
      (mul_nonneg ((show (0 : ℝ) ≤ 1 by norm_num).trans hB) (abs_nonneg M))
      (pow_pos hX j) hpow
  calc
    t ^ r / (r.factorial : ℝ) *
        |iteratedDeriv r (reciprocalPhase N M j) t| ≤
      |N| / t + B * |M| / t ^ j := by
        simpa [B] using
          normalized_abs_iteratedDeriv_reciprocalPhase_le N M hj ht
    _ ≤ |N| / X + B * |M| / X ^ j := add_le_add hN hM
    _ ≤ B * (|N| / X + |M| / X ^ j) := by
      have hN0 : 0 ≤ |N| / X := div_nonneg (abs_nonneg N) hX.le
      have hNB : |N| / X ≤ B * (|N| / X) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hB) hN0]
      calc
        |N| / X + B * |M| / X ^ j ≤
            B * (|N| / X) + B * |M| / X ^ j :=
          add_le_add hNB le_rfl
        _ = B * (|N| / X + |M| / X ^ j) := by ring
    _ = B * reciprocalPhaseScale N M j X := by
      rw [reciprocalPhaseScale]

/-- In the source's large-`M_r` case, the phase scale is controlled by the
`M_r` term with the explicit harmless constant five. -/
theorem reciprocalPhaseScale_le_five_mul_higherCoefficient
    (N M : ℝ) {j r : ℕ} (hj : 1 ≤ j) {X : ℝ} (hX : 0 < X)
    (hlarge : |N| * X ^ (j - 1) ≤
      4 * |reciprocalPhaseHigherCoefficient M j r|) :
    reciprocalPhaseScale N M j X ≤
      5 * (|reciprocalPhaseHigherCoefficient M j r| / X ^ j) := by
  have hjpow : X ^ j = X ^ (j - 1) * X := by
    calc
      X ^ j = X ^ ((j - 1) + 1) := by congr 1; omega
      _ = X ^ (j - 1) * X := by rw [pow_succ]
  have hlargeX := mul_le_mul_of_nonneg_right hlarge hX.le
  have hN : |N| / X ≤
      4 * |reciprocalPhaseHigherCoefficient M j r| / X ^ j := by
    rw [div_le_div_iff₀ hX (pow_pos hX j)]
    rw [hjpow]
    nlinarith
  have hM : |M| / X ^ j ≤
      |reciprocalPhaseHigherCoefficient M j r| / X ^ j :=
    div_le_div_of_nonneg_right
      (abs_le_abs_reciprocalPhaseHigherCoefficient M hj) (pow_pos hX j).le
  rw [reciprocalPhaseScale]
  calc
    |N| / X + |M| / X ^ j ≤
        4 * (|reciprocalPhaseHigherCoefficient M j r| / X ^ j) +
          |reciprocalPhaseHigherCoefficient M j r| / X ^ j := by
      exact add_le_add (by simpa [mul_div_assoc] using hN) hM
    _ = 5 * (|reciprocalPhaseHigherCoefficient M j r| / X ^ j) := by ring

/-- Reverse-triangle lower bound for the normalized derivative.  This is the
algebraic inequality used to separate the non-cancellation regime from the
single critical interval in the source proof. -/
theorem normalized_abs_iteratedDeriv_reciprocalPhase_lower
    (N M : ℝ) (j r : ℕ) {t : ℝ} (ht : 0 < t) :
    |N| / t - |reciprocalPhaseHigherCoefficient M j r| / t ^ j ≤
      t ^ r / (r.factorial : ℝ) *
        |iteratedDeriv r (reciprocalPhase N M j) t| := by
  rw [normalized_abs_iteratedDeriv_reciprocalPhase N M j r ht]
  simpa [abs_div, abs_of_pos ht, abs_of_pos (pow_pos ht j)] using
    abs_sub_abs_le_abs_add (N / t)
      (reciprocalPhaseHigherCoefficient M j r / t ^ j)

/-- In the regime where the higher-order term is at most half the reciprocal
linear term, the normalized derivative is bounded below by half that term. -/
theorem normalized_abs_iteratedDeriv_reciprocalPhase_ge_half_of_dominates
    (N M : ℝ) (j r : ℕ) {t : ℝ} (ht : 0 < t)
    (hdom : 2 * (|reciprocalPhaseHigherCoefficient M j r| / t ^ j) ≤
      |N| / t) :
    (1 / 2 : ℝ) * (|N| / t) ≤
      t ^ r / (r.factorial : ℝ) *
        |iteratedDeriv r (reciprocalPhase N M j) t| := by
  have hlower :=
    normalized_abs_iteratedDeriv_reciprocalPhase_lower N M j r ht
  linarith

/-- In the source's small-`M_r` branch there is no critical interval: on
`[X,2X]` the normalized derivative is uniformly at least `F/10`. -/
theorem normalized_abs_iteratedDeriv_reciprocalPhase_ge_scale_div_ten_of_small
    (N M : ℝ) {j r : ℕ} (hj : 1 ≤ j) {X t : ℝ}
    (hX : 0 < X) (hXt : X ≤ t) (htop : t ≤ 2 * X)
    (hsmall : 4 * |reciprocalPhaseHigherCoefficient M j r| ≤
      |N| * X ^ (j - 1)) :
    reciprocalPhaseScale N M j X / 10 ≤
      t ^ r / (r.factorial : ℝ) *
        |iteratedDeriv r (reciprocalPhase N M j) t| := by
  let Cabs := |reciprocalPhaseHigherCoefficient M j r|
  have ht : 0 < t := hX.trans_le hXt
  have hjpow : X ^ j = X ^ (j - 1) * X := by
    calc
      X ^ j = X ^ ((j - 1) + 1) := by congr 1; omega
      _ = X ^ (j - 1) * X := by rw [pow_succ]
  have hsmallX := mul_le_mul_of_nonneg_right hsmall hX.le
  have hCX : Cabs / X ^ j ≤ |N| / (4 * X) := by
    rw [div_le_div_iff₀ (pow_pos hX j) (mul_pos (by norm_num) hX)]
    rw [hjpow]
    nlinarith
  have hpow : X ^ j ≤ t ^ j := pow_le_pow_left₀ hX.le hXt j
  have hCt : Cabs / t ^ j ≤ |N| / (4 * X) :=
    (div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hX j) hpow).trans hCX
  have hNt : |N| / (2 * X) ≤ |N| / t :=
    div_le_div_of_nonneg_left (abs_nonneg N) ht htop
  have hM : |M| / X ^ j ≤ Cabs / X ^ j :=
    div_le_div_of_nonneg_right
      (abs_le_abs_reciprocalPhaseHigherCoefficient M hj) (pow_pos hX j).le
  have hF : reciprocalPhaseScale N M j X ≤ 5 * |N| / (4 * X) := by
    rw [reciprocalPhaseScale]
    calc
      |N| / X + |M| / X ^ j ≤ |N| / X + Cabs / X ^ j :=
        add_le_add le_rfl hM
      _ ≤ |N| / X + |N| / (4 * X) := add_le_add le_rfl hCX
      _ = 5 * |N| / (4 * X) := by field_simp [hX.ne']; ring
  have hlower :=
    normalized_abs_iteratedDeriv_reciprocalPhase_lower N M j r ht
  have hFten : reciprocalPhaseScale N M j X / 10 ≤ |N| / (8 * X) := by
    calc
      reciprocalPhaseScale N M j X / 10 ≤
          (5 * |N| / (4 * X)) / 10 :=
        div_le_div_of_nonneg_right hF (by norm_num)
      _ = |N| / (8 * X) := by field_simp [hX.ne']; ring
  have hNcompare : |N| / (8 * X) ≤ |N| / (4 * X) := by
    exact div_le_div_of_nonneg_left (abs_nonneg N)
      (mul_pos (by norm_num) hX) (by nlinarith [hX])
  have hdiff : |N| / (4 * X) ≤
      |N| / t - |reciprocalPhaseHigherCoefficient M j r| / t ^ j := by
    dsimp [Cabs] at hCt
    have hhalf : |N| / (2 * X) = 2 * (|N| / (4 * X)) := by
      field_simp [hX.ne']
      ring
    rw [hhalf] at hNt
    nlinarith
  exact hFten.trans (hNcompare.trans (hdiff.trans hlower))


end

end Tao2026
