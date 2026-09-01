import GafniTao.FordLogTaylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Ford's logarithmic phase replacement

This is the pointwise analytic step between equations (5.1) and (5.2): the
oscillation with phase `-t log(1+x)` is replaced by its degree-`k` Taylor
phase, with the exact source error.  It is kept separately so the subsequent
finite averaging and Hölder arguments cannot hide a phase-normalization loss.
-/

open Complex
open Finset

namespace GafniTao

noncomputable section

def fordLogOscillation (t x : ℝ) : ℂ :=
  Complex.exp (I * (-(t * Real.log (1 + x)) : ℝ))

def fordTaylorOscillation (k : ℕ) (t x : ℝ) : ℂ :=
  Complex.exp (I * (-(t * fordLogTaylor k x) : ℝ))

/-- The exact pointwise perturbation obtained from Ford (5.1) and
`|exp(iy)-1| ≤ |y|`. -/
theorem ford_taylor_phase_difference
    {k : ℕ} {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖fordLogOscillation t x - fordTaylorOscillation k t x‖ ≤
      t * (x ^ (k + 1) / (k + 1)) := by
  let A : ℝ := -(t * Real.log (1 + x))
  let B : ℝ := -(t * fordLogTaylor k x)
  have hfactor :
      Complex.exp (I * (A : ℂ)) - Complex.exp (I * (B : ℂ)) =
        Complex.exp (I * (B : ℂ)) *
          (Complex.exp (I * ((A - B : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  change ‖Complex.exp (I * (A : ℂ)) - Complex.exp (I * (B : ℂ))‖ ≤ _
  rw [hfactor, norm_mul, Complex.norm_exp]
  simp only [mul_re, I_re, ofReal_re, I_im, ofReal_im, zero_mul, one_mul,
    sub_self, Real.exp_zero, one_mul]
  calc
    ‖Complex.exp (I * ((A - B : ℝ) : ℂ)) - 1‖ ≤ ‖A - B‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = t * |Real.log (1 + x) - fordLogTaylor k x| := by
      rw [Real.norm_eq_abs]
      dsimp [A, B]
      rw [show -(t * Real.log (1 + x)) - -(t * fordLogTaylor k x) =
          -t * (Real.log (1 + x) - fordLogTaylor k x) by ring,
        abs_mul, abs_neg, abs_of_nonneg ht]
    _ ≤ t * (x ^ (k + 1) / (k + 1)) := by
      exact mul_le_mul_of_nonneg_left (ford_equation_5_1 hx) ht

/-- Ford's coefficient `γ_j = (-1)^j t / (2π j z^j)`, indexed in Lean by
`j = 0, ..., k-1`, so the source degree is `j+1`. -/
def fordTaylorGamma (t z : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ (j + 1) * t /
    (2 * Real.pi * (j + 1) * z ^ (j + 1))

/-- The real polynomial `Σ γ_j y^j` in Ford's definition of `U`. -/
def fordTaylorPolynomialPhase (k : ℕ) (t z y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, fordTaylorGamma t z j * y ^ (j + 1)

/-- The additive character convention `e(x) = exp(2π i x)`. -/
def fordAdditiveCharacter (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

/-- Exact verification of Ford's `γ_j` normalization after equation (5.2). -/
theorem ford_taylor_gamma_normalization
    {k : ℕ} {t z y : ℝ} (hz : z ≠ 0) :
    -(t * fordLogTaylor k (y / z)) =
      2 * Real.pi * fordTaylorPolynomialPhase k t z y := by
  unfold fordLogTaylor fordTaylorPolynomialPhase
  have hneg : -(t * (∑ j ∈ range k,
      (-1 : ℝ) ^ j * (y / z) ^ (j + 1) / (j + 1))) =
      (-t) * (∑ j ∈ range k,
        (-1 : ℝ) ^ j * (y / z) ^ (j + 1) / (j + 1)) := by ring
  rw [hneg]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold fordTaylorGamma
  rw [div_pow, pow_succ]
  have hj1 : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hzpow : z ^ (j + 1) ≠ 0 := pow_ne_zero _ hz
  field_simp [Real.pi_ne_zero, hj1, hzpow]
  ring

theorem fordTaylorOscillation_eq_additiveCharacter
    {k : ℕ} {t z y : ℝ} (hz : z ≠ 0) :
    fordTaylorOscillation k t (y / z) =
      fordAdditiveCharacter (fordTaylorPolynomialPhase k t z y) := by
  unfold fordTaylorOscillation fordAdditiveCharacter
  rw [ford_taylor_gamma_normalization hz]
  congr 1
  push_cast
  ring

/-- The finite-sum form of the Taylor replacement used in Ford (5.2).  The
right side retains every individual remainder, before Ford inserts the
uniform bound `ab/z ≤ M₁M₂/N`. -/
theorem ford_taylor_phase_double_sum_difference
    {α β : Type*} (A : Finset α) (B : Finset β)
    (k : ℕ) {t : ℝ} (x : α → β → ℝ) (ht : 0 ≤ t)
    (hx : ∀ a ∈ A, ∀ b ∈ B, x a b ∈ Set.Icc (0 : ℝ) 1) :
    ‖(∑ a ∈ A, ∑ b ∈ B, fordLogOscillation t (x a b)) -
        ∑ a ∈ A, ∑ b ∈ B, fordTaylorOscillation k t (x a b)‖ ≤
      ∑ a ∈ A, ∑ b ∈ B, t * (x a b ^ (k + 1) / (k + 1)) := by
  simp only [← Finset.sum_sub_distrib]
  refine norm_sum_le_of_le A fun a ha => ?_
  exact norm_sum_le_of_le B fun b hb =>
    ford_taylor_phase_difference ht (hx a ha b hb)

theorem ford_taylor_phase_double_sum_uniform
    {α β : Type*} (A : Finset α) (B : Finset β)
    (k : ℕ) {t E : ℝ} (x : α → β → ℝ) (ht : 0 ≤ t)
    (hx : ∀ a ∈ A, ∀ b ∈ B, x a b ∈ Set.Icc (0 : ℝ) 1)
    (hE : ∀ a ∈ A, ∀ b ∈ B, x a b ^ (k + 1) ≤ E) :
    ‖(∑ a ∈ A, ∑ b ∈ B, fordLogOscillation t (x a b)) -
        ∑ a ∈ A, ∑ b ∈ B, fordTaylorOscillation k t (x a b)‖ ≤
      (A.card : ℝ) * B.card * (t * (E / (k + 1))) := by
  calc
    ‖(∑ a ∈ A, ∑ b ∈ B, fordLogOscillation t (x a b)) -
        ∑ a ∈ A, ∑ b ∈ B, fordTaylorOscillation k t (x a b)‖ ≤
        ∑ a ∈ A, ∑ b ∈ B,
          t * (x a b ^ (k + 1) / (k + 1)) :=
      ford_taylor_phase_double_sum_difference A B k x ht hx
    _ ≤ ∑ _a ∈ A, ∑ _b ∈ B, t * (E / (k + 1)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      gcongr
      exact hE a ha b hb
    _ = (A.card : ℝ) * B.card * (t * (E / (k + 1))) := by simp; ring

#print axioms ford_taylor_phase_difference
#print axioms ford_taylor_gamma_normalization
#print axioms fordTaylorOscillation_eq_additiveCharacter
#print axioms ford_taylor_phase_double_sum_difference
#print axioms ford_taylor_phase_double_sum_uniform

end

end GafniTao
