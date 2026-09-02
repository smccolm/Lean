import GafniTao.FordSingleZeroDetector
import GafniTao.FordTrigonometric
import GafniTao.FordKSourceSeries

/-!
# Euler positivity for Ford's five logarithmic derivatives

The logarithmic derivatives below are the literal absolutely convergent
von Mangoldt series on `Re s > 1`.  Ford's nonnegative trigonometric
polynomial can therefore be applied term by term.  This is the positivity
input used by the qualitative Vinogradov--Korobov contradiction.
-/

open Complex
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The real logarithmic-derivative value `-Re (zeta'/zeta)` on a vertical
line in the Euler half-plane. -/
noncomputable def fordRealLogDerivative (sigma t : ℝ) : ℝ :=
  (-(deriv riemannZeta ((sigma : ℂ) + I * t) /
    riemannZeta ((sigma : ℂ) + I * t))).re

/-- One literal real von Mangoldt term in `fordRealLogDerivative`. -/
noncomputable def fordRealLogDerivativeTerm
    (sigma t : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    Real.exp (-sigma * Real.log n) * Real.cos (t * Real.log n)

theorem re_ford_vonMangoldt_exp_term
    (sigma t : ℝ) (n : ℕ) :
    ((ArithmeticFunction.vonMangoldt n : ℂ) *
      Complex.exp (-((sigma : ℂ) + I * t) * (Real.log n : ℂ))).re =
      fordRealLogDerivativeTerm sigma t n := by
  unfold fordRealLogDerivativeTerm
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [Complex.exp_re]
  simp only [neg_re, mul_re, mul_im, add_re, ofReal_re, I_re, zero_mul,
    add_im, ofReal_im, I_im, one_mul, neg_im]
  ring_nf
  rw [Real.cos_neg]

theorem summable_fordRealLogDerivativeTerm
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    Summable (fordRealLogDerivativeTerm sigma t) := by
  have hs : 1 < (((sigma : ℂ) + I * t)).re := by simpa using hsigma
  have hcomplex := summable_ford_vonMangoldt_exp_term hs
  have hreal := (Complex.hasSum_re hcomplex.hasSum).summable
  apply hreal.congr
  intro n
  exact re_ford_vonMangoldt_exp_term sigma t n

theorem fordRealLogDerivative_eq_tsum
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    fordRealLogDerivative sigma t =
      ∑' n : ℕ, fordRealLogDerivativeTerm sigma t n := by
  have hs : 1 < (((sigma : ℂ) + I * t)).re := by simpa using hsigma
  have hseries := tsum_ford_vonMangoldt_exp_term hs
  have hre := congrArg Complex.re hseries
  rw [Complex.re_tsum (summable_ford_vonMangoldt_exp_term hs)] at hre
  calc
    fordRealLogDerivative sigma t =
        ∑' n : ℕ,
          (((ArithmeticFunction.vonMangoldt n : ℂ) *
            Complex.exp (-((sigma : ℂ) + I * t) *
              (Real.log n : ℂ))).re) := by
      simpa only [fordRealLogDerivative, neg_div] using hre.symm
    _ = ∑' n : ℕ, fordRealLogDerivativeTerm sigma t n := by
      apply tsum_congr
      exact re_ford_vonMangoldt_exp_term sigma t

/-- Ford's exact five-frequency Euler positivity. -/
theorem ford_logDerivative_trigonometric_nonneg
    {sigma : ℝ} (hsigma : 1 < sigma) (a₁ a₂ t : ℝ) :
    0 ≤
      fordTrigB0 a₁ a₂ * fordRealLogDerivative sigma 0 +
      fordTrigB1 a₁ a₂ * fordRealLogDerivative sigma t +
      fordTrigB2 a₁ a₂ * fordRealLogDerivative sigma (2 * t) +
      fordTrigB3 a₁ a₂ * fordRealLogDerivative sigma (3 * t) +
      fordTrigB4 * fordRealLogDerivative sigma (4 * t) := by
  have s0 : Summable (fordRealLogDerivativeTerm sigma 0) :=
    summable_fordRealLogDerivativeTerm hsigma
  have s1 : Summable (fordRealLogDerivativeTerm sigma t) :=
    summable_fordRealLogDerivativeTerm hsigma
  have s2 : Summable (fordRealLogDerivativeTerm sigma (2 * t)) :=
    summable_fordRealLogDerivativeTerm hsigma
  have s3 : Summable (fordRealLogDerivativeTerm sigma (3 * t)) :=
    summable_fordRealLogDerivativeTerm hsigma
  have s4 : Summable (fordRealLogDerivativeTerm sigma (4 * t)) :=
    summable_fordRealLogDerivativeTerm hsigma
  have h0 := s0.mul_left (fordTrigB0 a₁ a₂)
  have h1 := s1.mul_left (fordTrigB1 a₁ a₂)
  have h2 := s2.mul_left (fordTrigB2 a₁ a₂)
  have h3 := s3.mul_left (fordTrigB3 a₁ a₂)
  have h4 := s4.mul_left fordTrigB4
  rw [fordRealLogDerivative_eq_tsum hsigma,
    fordRealLogDerivative_eq_tsum hsigma,
    fordRealLogDerivative_eq_tsum hsigma,
    fordRealLogDerivative_eq_tsum hsigma,
    fordRealLogDerivative_eq_tsum hsigma]
  rw [← s0.tsum_mul_left, ← s1.tsum_mul_left,
    ← s2.tsum_mul_left, ← s3.tsum_mul_left,
    ← s4.tsum_mul_left,
    ← h0.tsum_add h1, ← (h0.add h1).tsum_add h2,
    ← ((h0.add h1).add h2).tsum_add h3,
    ← (((h0.add h1).add h2).add h3).tsum_add h4]
  apply tsum_nonneg
  intro n
  unfold fordRealLogDerivativeTerm
  have hLambda : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hExp : 0 ≤ Real.exp (-sigma * Real.log n) := (Real.exp_pos _).le
  have hTrig := ford_trigonometric_nonneg a₁ a₂ (t * Real.log n)
  have hEq :
      fordTrigB0 a₁ a₂ *
          (ArithmeticFunction.vonMangoldt n *
            Real.exp (-sigma * Real.log n) * Real.cos 0) +
        fordTrigB1 a₁ a₂ *
          (ArithmeticFunction.vonMangoldt n *
            Real.exp (-sigma * Real.log n) * Real.cos (t * Real.log n)) +
        fordTrigB2 a₁ a₂ *
          (ArithmeticFunction.vonMangoldt n *
            Real.exp (-sigma * Real.log n) * Real.cos (2 * t * Real.log n)) +
        fordTrigB3 a₁ a₂ *
          (ArithmeticFunction.vonMangoldt n *
            Real.exp (-sigma * Real.log n) * Real.cos (3 * t * Real.log n)) +
        fordTrigB4 *
          (ArithmeticFunction.vonMangoldt n *
            Real.exp (-sigma * Real.log n) * Real.cos (4 * t * Real.log n)) =
        (ArithmeticFunction.vonMangoldt n *
          Real.exp (-sigma * Real.log n)) *
          fordTrigSum a₁ a₂ (t * Real.log n) := by
    simp only [fordTrigSum, fordTrigB4, Real.cos_zero]
    ring_nf
  simp only [zero_mul]
  rw [hEq]
  exact mul_nonneg (mul_nonneg hLambda hExp) hTrig

theorem fordRealLogDerivative_zero_lt_inv
    {sigma : ℝ} (hsigma : 1 < sigma) :
    fordRealLogDerivative sigma 0 < 1 / (sigma - 1) := by
  have h := ford_zeta_basic_logDerivative (sigma := sigma) (t := 0) hsigma
  exact (Complex.re_le_norm
    (-(deriv riemannZeta ((sigma : ℂ) + I * (0 : ℝ)) /
      riemannZeta ((sigma : ℂ) + I * (0 : ℝ))))).trans_lt
      (by simpa [fordRealLogDerivative] using h)

/-- Every auxiliary frequency is bounded above by the zero-frequency Euler
series.  This is the termwise inequality `cos ≤ 1`; absolute convergence
justifies passing it through the infinite sum. -/
theorem fordRealLogDerivative_le_zero
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    fordRealLogDerivative sigma t ≤ fordRealLogDerivative sigma 0 := by
  rw [fordRealLogDerivative_eq_tsum hsigma,
    fordRealLogDerivative_eq_tsum hsigma]
  apply tsum_le_tsum
  · intro n
    unfold fordRealLogDerivativeTerm
    have hcoeff : 0 ≤ ArithmeticFunction.vonMangoldt n *
        Real.exp (-sigma * Real.log n) := by positivity
    have hcos : Real.cos (t * Real.log n) ≤ 1 := Real.cos_le_one _
    simpa using mul_le_mul_of_nonneg_left hcos hcoeff
  · exact summable_fordRealLogDerivativeTerm hsigma
  · exact summable_fordRealLogDerivativeTerm hsigma

#print axioms ford_logDerivative_trigonometric_nonneg
#print axioms fordRealLogDerivative_zero_lt_inv
#print axioms fordRealLogDerivative_le_zero

end

end GafniTao
