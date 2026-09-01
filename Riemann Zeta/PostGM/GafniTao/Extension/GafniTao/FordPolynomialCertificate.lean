import GafniTao.FordExpCertificate
import Mathlib.RingTheory.Polynomial.Bernstein

/-!
# Exact polynomial certificates for Ford's normalized cubic integral

This file contains the purely algebraic certificate language used for the
tight numerical inequality in Ford's Lemma 7.3.  Coefficients are rational;
all evaluation in `ℝ` is through explicit ring homomorphisms.
-/

open Finset Set

namespace GafniTao

noncomputable section

abbrev FordBiPolynomial := Polynomial (Polynomial ℚ)

def fordRatPolynomialEvalHom (y : ℝ) : Polynomial ℚ →+* ℝ :=
  Polynomial.eval₂RingHom (Rat.castHom ℝ) y

def fordBiPolynomialEval (p : FordBiPolynomial) (y v : ℝ) : ℝ :=
  Polynomial.eval₂ (fordRatPolynomialEvalHom y) v p

def fordBiY : FordBiPolynomial := Polynomial.C Polynomial.X

def fordBiV : FordBiPolynomial := Polynomial.X

def fordBiRat (q : ℚ) : FordBiPolynomial :=
  Polynomial.C (Polynomial.C q)

def fordScaledTaylorPolynomial (m n : ℕ) (z : FordBiPolynomial) : FordBiPolynomial :=
  ((∑ k ∈ Finset.range n,
      (fordBiRat (-1 / (m : ℚ)) * z) ^ k *
        fordBiRat (1 / (k.factorial : ℚ))) +
      (fordBiRat (1 / (m : ℚ)) * z) ^ n *
        fordBiRat ((n.succ : ℚ) / ((n.factorial : ℚ) * n))) ^ m

@[simp] theorem fordBiPolynomialEval_rat (q : ℚ) (y v : ℝ) :
    fordBiPolynomialEval (fordBiRat q) y v = (q : ℝ) := by
  simp [fordBiPolynomialEval, fordBiRat, fordRatPolynomialEvalHom]

@[simp] theorem fordBiPolynomialEval_y (y v : ℝ) :
    fordBiPolynomialEval fordBiY y v = y := by
  simp [fordBiPolynomialEval, fordBiY, fordRatPolynomialEvalHom]

@[simp] theorem fordBiPolynomialEval_v (y v : ℝ) :
    fordBiPolynomialEval fordBiV y v = v := by
  simp [fordBiPolynomialEval, fordBiV, fordRatPolynomialEvalHom]

@[simp] theorem fordBiPolynomialEval_add
    (p q : FordBiPolynomial) (y v : ℝ) :
    fordBiPolynomialEval (p + q) y v =
      fordBiPolynomialEval p y v + fordBiPolynomialEval q y v := by
  exact map_add (Polynomial.eval₂RingHom (fordRatPolynomialEvalHom y) v) p q

@[simp] theorem fordBiPolynomialEval_sub
    (p q : FordBiPolynomial) (y v : ℝ) :
    fordBiPolynomialEval (p - q) y v =
      fordBiPolynomialEval p y v - fordBiPolynomialEval q y v := by
  exact map_sub (Polynomial.eval₂RingHom (fordRatPolynomialEvalHom y) v) p q

@[simp] theorem fordBiPolynomialEval_mul
    (p q : FordBiPolynomial) (y v : ℝ) :
    fordBiPolynomialEval (p * q) y v =
      fordBiPolynomialEval p y v * fordBiPolynomialEval q y v := by
  exact map_mul (Polynomial.eval₂RingHom (fordRatPolynomialEvalHom y) v) p q

@[simp] theorem fordBiPolynomialEval_pow
    (p : FordBiPolynomial) (n : ℕ) (y v : ℝ) :
    fordBiPolynomialEval (p ^ n) y v = fordBiPolynomialEval p y v ^ n := by
  exact map_pow (Polynomial.eval₂RingHom (fordRatPolynomialEvalHom y) v) p n

@[simp] theorem fordBiPolynomialEval_sum
    {ι : Type*} (s : Finset ι) (p : ι → FordBiPolynomial) (y v : ℝ) :
    fordBiPolynomialEval (∑ i ∈ s, p i) y v =
      ∑ i ∈ s, fordBiPolynomialEval (p i) y v := by
  exact map_sum (Polynomial.eval₂RingHom (fordRatPolynomialEvalHom y) v) _ _

theorem fordBiPolynomialEval_scaledTaylor
    {m n : ℕ} (hm : 0 < m) (p : FordBiPolynomial) (y v : ℝ)
    (hp : 0 ≤ fordBiPolynomialEval p y v) :
    fordBiPolynomialEval (fordScaledTaylorPolynomial m n p) y v =
      fordExpTaylorUpper n
        (-fordBiPolynomialEval p y v / (m : ℝ)) ^ m := by
  have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [fordScaledTaylorPolynomial, fordBiPolynomialEval_pow,
    fordBiPolynomialEval_add, fordBiPolynomialEval_sum,
    fordBiPolynomialEval_mul, fordBiPolynomialEval_rat]
  unfold fordExpTaylorUpper
  rw [abs_div, abs_neg, abs_of_nonneg hp,
    abs_of_pos (Nat.cast_pos.mpr hm)]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    congr 1
    push_cast
    field_simp
    simpa only [one_div] using
      (Rat.cast_inv (α := ℝ) (k.factorial : ℚ))
  · congr 1
    · push_cast
      field_simp
    · push_cast
      norm_cast

theorem real_exp_neg_le_fordScaledTaylorPolynomial
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p : FordBiPolynomial) (y v : ℝ)
    (hp0 : 0 ≤ fordBiPolynomialEval p y v)
    (hpm : fordBiPolynomialEval p y v ≤ m) :
    Real.exp (-fordBiPolynomialEval p y v) ≤
      fordBiPolynomialEval (fordScaledTaylorPolynomial m n p) y v := by
  rw [fordBiPolynomialEval_scaledTaylor hm p y v hp0]
  exact real_exp_neg_le_scaledTaylor hp0 hm hn hpm

/-- The value of the coefficientwise antiderivative of a bivariate
polynomial, with respect to its second variable. -/
def fordBiPrimitiveValue (p : FordBiPolynomial) (y v : ℝ) : ℝ :=
  p.sum fun n a =>
    fordRatPolynomialEvalHom y a * v ^ (n + 1) / (n + 1 : ℝ)

@[simp] theorem fordBiPrimitiveValue_zero (p : FordBiPolynomial) (y : ℝ) :
    fordBiPrimitiveValue p y 0 = 0 := by
  unfold fordBiPrimitiveValue
  rw [Polynomial.sum_def]
  simp

/-- Coefficientwise antiderivative in the outer (second) variable. -/
def fordBiIntegralPolynomial (p : FordBiPolynomial) : FordBiPolynomial :=
  p.sum fun n a =>
    Polynomial.C (Polynomial.C (1 / (n + 1 : ℚ)) * a) *
      Polynomial.X ^ (n + 1)

@[simp] theorem fordBiIntegralPolynomial_coeff_zero (p : FordBiPolynomial) :
    (fordBiIntegralPolynomial p).coeff 0 = 0 := by
  unfold fordBiIntegralPolynomial
  rw [Polynomial.sum_def]
  simp

theorem derivative_fordBiIntegralPolynomial (p : FordBiPolynomial) :
    Polynomial.derivative (fordBiIntegralPolynomial p) = p := by
  unfold fordBiIntegralPolynomial
  rw [Polynomial.sum_def, Polynomial.derivative_sum]
  conv_rhs =>
    rw [← Polynomial.sum_C_mul_X_pow_eq p, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
  simp only [Nat.add_sub_cancel]
  change Polynomial.C
      (Polynomial.C (1 / ((n : ℚ) + 1)) * p.coeff n) *
        (Polynomial.C ((n + 1 : ℕ) : Polynomial ℚ) * Polynomial.X ^ n) =
      Polynomial.C (p.coeff n) * Polynomial.X ^ n
  rw [map_mul]
  have hscalar :
      Polynomial.C (Polynomial.C (1 / ((n : ℚ) + 1))) *
          Polynomial.C ((n + 1 : ℕ) : Polynomial ℚ) = 1 := by
    rw [show ((n + 1 : ℕ) : Polynomial ℚ) =
      Polynomial.C ((n : ℚ) + 1) by norm_num,
      ← Polynomial.C_mul, ← Polynomial.C_mul]
    field_simp
    simp
  calc
    Polynomial.C (Polynomial.C (1 / ((n : ℚ) + 1))) *
          Polynomial.C (p.coeff n) *
          (Polynomial.C ((n + 1 : ℕ) : Polynomial ℚ) * Polynomial.X ^ n) =
        (Polynomial.C (Polynomial.C (1 / ((n : ℚ) + 1))) *
            Polynomial.C ((n + 1 : ℕ) : Polynomial ℚ)) *
          Polynomial.C (p.coeff n) * Polynomial.X ^ n := by ring
    _ = Polynomial.C (p.coeff n) * Polynomial.X ^ n := by rw [hscalar]; simp

theorem polynomial_eq_of_derivative_eq_of_coeff_zero_eq
    {p q : FordBiPolynomial}
    (hderiv : Polynomial.derivative p = Polynomial.derivative q)
    (hzero : p.coeff 0 = q.coeff 0) :
    p = q := by
  apply Polynomial.ext
  intro n
  cases n with
  | zero => exact hzero
  | succ n =>
      have hcoeff := congrArg (fun r : FordBiPolynomial => r.coeff n) hderiv
      simp only [Polynomial.coeff_derivative] at hcoeff
      apply mul_right_cancel₀ _ hcoeff
      intro h
      have hconst : (n : ℚ) + 1 = 0 := Polynomial.C_injective (by simpa using h)
      have hpos : (0 : ℚ) < n + 1 := by positivity
      exact hpos.ne' hconst

/-- Substitute the inner variable for the outer variable. -/
def fordBiDiagonal (p : FordBiPolynomial) : Polynomial ℚ :=
  p.eval Polynomial.X

/-- Substitute a rational constant for the outer variable. -/
def fordBiEvalV (p : FordBiPolynomial) (v : ℚ) : Polynomial ℚ :=
  p.eval (Polynomial.C v)

theorem fordBiIntegralPolynomial_eval
    (p : FordBiPolynomial) (y v : ℝ) :
    fordBiPolynomialEval (fordBiIntegralPolynomial p) y v =
      fordBiPrimitiveValue p y v := by
  unfold fordBiIntegralPolynomial fordBiPrimitiveValue fordBiPolynomialEval
  rw [Polynomial.eval₂_sum, Polynomial.sum_def, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n hn
  simp [fordRatPolynomialEvalHom, div_eq_mul_inv]
  ring

theorem fordBiDiagonal_eval (p : FordBiPolynomial) (y : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) y (fordBiDiagonal p) =
      fordBiPolynomialEval p y y := by
  unfold fordBiDiagonal fordBiPolynomialEval
  rw [Polynomial.eval_eq_sum, Polynomial.eval₂_sum, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  simp [fordRatPolynomialEvalHom]

theorem fordBiEvalV_eval (p : FordBiPolynomial) (v : ℚ) (y : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) y (fordBiEvalV p v) =
      fordBiPolynomialEval p y (v : ℝ) := by
  unfold fordBiEvalV fordBiPolynomialEval
  rw [Polynomial.eval_eq_sum, Polynomial.eval₂_sum,
    Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C]
  simp [fordRatPolynomialEvalHom]

theorem hasDerivAt_fordBiPrimitiveValue
    (p : FordBiPolynomial) (y v : ℝ) :
    HasDerivAt (fordBiPrimitiveValue p y)
      (fordBiPolynomialEval p y v) v := by
  unfold fordBiPrimitiveValue
  change HasDerivAt
    (fun x => ∑ n ∈ p.support,
      fordRatPolynomialEvalHom y (p.coeff n) * x ^ (n + 1) / (n + 1 : ℝ))
    (fordBiPolynomialEval p y v) v
  have hderiv := HasDerivAt.fun_sum
    (u := p.support)
    (A := fun n x =>
      fordRatPolynomialEvalHom y (p.coeff n) * x ^ (n + 1) / (n + 1 : ℝ))
    (A' := fun n => fordRatPolynomialEvalHom y (p.coeff n) * v ^ n)
    (x := v)
    (fun n hn => by
      convert (((hasDerivAt_pow (n + 1) v).const_mul
        (fordRatPolynomialEvalHom y (p.coeff n))).div_const (n + 1 : ℝ)) using 1
      · rw [Nat.add_sub_cancel]
        push_cast
        field_simp)
  rw [fordBiPolynomialEval, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  exact hderiv

theorem continuous_fordBiPolynomialEval (p : FordBiPolynomial) (y : ℝ) :
    Continuous (fordBiPolynomialEval p y) := by
  unfold fordBiPolynomialEval
  rw [show (fun v => Polynomial.eval₂ (fordRatPolynomialEvalHom y) v p) =
      (fun v => Polynomial.eval v (p.map (fordRatPolynomialEvalHom y))) by
    funext v
    exact Polynomial.eval₂_eq_eval_map
      (p := p) (f := fordRatPolynomialEvalHom y) (x := v)]
  exact Polynomial.continuous _

theorem intervalIntegral_fordBiPolynomialEval
    (p : FordBiPolynomial) (y a b : ℝ) :
    (∫ v in a..b, fordBiPolynomialEval p y v) =
      fordBiPrimitiveValue p y b - fordBiPrimitiveValue p y a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro v hv
    exact hasDerivAt_fordBiPrimitiveValue p y v
  · exact (continuous_fordBiPolynomialEval p y).intervalIntegrable _ _

#print axioms real_exp_neg_le_fordScaledTaylorPolynomial
#print axioms fordBiIntegralPolynomial_eval
#print axioms hasDerivAt_fordBiPrimitiveValue
#print axioms intervalIntegral_fordBiPolynomialEval

end

end GafniTao
