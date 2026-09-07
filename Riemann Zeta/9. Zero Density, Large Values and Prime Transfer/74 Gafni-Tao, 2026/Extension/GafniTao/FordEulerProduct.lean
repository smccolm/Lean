import GafniTao.FordFourierKernel
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Euler-product logarithm used by Ford

This file exposes the exact absolutely convergent prime Euler logarithm in
the half-plane `re s > 1` and identifies its real part with
`log |ζ(s)|`.  It is the first analytic input to Ford's Lemma 5.1.
-/

namespace GafniTao

noncomputable def fordEulerZetaLog (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))

theorem summable_fordEulerZetaLog {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes =>
      -Complex.log (1 - (p : ℂ) ^ (-s))) := by
  have hpBound (p : Nat.Primes) :
      ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s).re := by
    simp only [Complex.norm_natCast_cpow_of_re_ne_zero _
      (Complex.re_neg_ne_zero_of_one_lt_re hs)]
    exact le_rfl
  refine (Nat.Primes.summable_rpow.mpr ?_).of_nonneg_of_le
      (fun _ => norm_nonneg _) hpBound |>.of_norm.clog_one_sub.neg
  rw [Complex.neg_re]
  linarith

theorem exp_fordEulerZetaLog_eq {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (fordEulerZetaLog s) = riemannZeta s := by
  exact riemannZeta_eulerProduct_exp_log hs

/-- The branch-free logarithmic identity Ford needs: only the real part of
the Euler logarithm appears, so equality follows directly from the norm of
the complex exponential. -/
theorem log_norm_riemannZeta_eq_re_fordEulerZetaLog
    {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖riemannZeta s‖ = (fordEulerZetaLog s).re := by
  rw [← exp_fordEulerZetaLog_eq hs, Complex.norm_exp, Real.log_exp]

theorem re_fordEulerZetaLog_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    (fordEulerZetaLog s).re =
      ∑' p : Nat.Primes,
        (-Complex.log (1 - (p : ℂ) ^ (-s))).re := by
  exact Complex.re_tsum (summable_fordEulerZetaLog hs)

theorem ford_prime_log_hasSum {s : ℂ} (hs : 1 < s.re)
    (p : Nat.Primes) :
    HasSum (fun m : ℕ => ((p : ℂ) ^ (-s)) ^ m / m)
      (-Complex.log (1 - (p : ℂ) ^ (-s))) := by
  apply Complex.hasSum_taylorSeries_neg_log
  rw [Complex.norm_natCast_cpow_of_re_ne_zero _
    (Complex.re_neg_ne_zero_of_one_lt_re hs)]
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  rw [Complex.neg_re]
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p)]
  exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp (by linarith))

theorem re_ford_prime_log_eq_tsum {s : ℂ} (hs : 1 < s.re)
    (p : Nat.Primes) :
    (-Complex.log (1 - (p : ℂ) ^ (-s))).re =
      ∑' m : ℕ, ((((p : ℂ) ^ (-s)) ^ m / m).re) := by
  exact (Complex.hasSum_re (ford_prime_log_hasSum hs p)).tsum_eq.symm

/-- Exact iterated prime/power form of `log |ζ(s)|`.  The `m=0` term is
definitionally zero, matching Ford's `m≥1` convention. -/
theorem log_norm_riemannZeta_eq_prime_power_series
    {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖riemannZeta s‖ =
      ∑' p : Nat.Primes, ∑' m : ℕ,
        ((((p : ℂ) ^ (-s)) ^ m / m).re) := by
  rw [log_norm_riemannZeta_eq_re_fordEulerZetaLog hs,
    re_fordEulerZetaLog_eq_tsum hs]
  apply tsum_congr
  intro p
  exact re_ford_prime_log_eq_tsum hs p

noncomputable def fordZetaLine (eta t : ℝ) : ℂ :=
  (1 + eta : ℝ) + Complex.I * t

@[simp] theorem fordZetaLine_re (eta t : ℝ) :
    (fordZetaLine eta t).re = 1 + eta := by
  simp [fordZetaLine]

@[simp] theorem fordZetaLine_im (eta t : ℝ) :
    (fordZetaLine eta t).im = t := by
  simp [fordZetaLine]

/-- Literal real part of one prime-power Euler term on Ford's vertical
line. -/
theorem ford_prime_power_term_re (eta t : ℝ) (p : Nat.Primes) (m : ℕ) :
    (((((p : ℂ) ^ (-fordZetaLine eta t)) ^ m) / m).re) =
      (p : ℝ) ^ (-(m : ℝ) * (1 + eta)) *
        Real.cos ((m : ℝ) * t * Real.log p) / m := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hpc : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  rw [Complex.cpow_def_of_ne_zero hpc, ← Complex.exp_nat_mul]
  simp only [Complex.div_natCast_re, Complex.exp_re]
  have hpCast : (p : ℂ) = ((p : ℝ) : ℂ) := by norm_cast
  rw [hpCast]
  rw [← Complex.ofReal_log hp.le]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    fordZetaLine_re, fordZetaLine_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im]
  simp only [zero_mul, sub_zero, add_zero]
  rw [show Real.exp ((m : ℝ) *
      (Real.log p * -(1 + eta))) =
      (p : ℝ) ^ (-(m : ℝ) * (1 + eta)) by
    rw [Real.rpow_def_of_pos hp]
    congr 1
    ring]
  rw [show (m : ℝ) * (Real.log p * -t) =
      -((m : ℝ) * t * Real.log p) by ring, Real.cos_neg]

theorem log_norm_riemannZeta_fordLine_eq_prime_power_series
    {eta : ℝ} (heta : 0 < eta) (t : ℝ) :
    Real.log ‖riemannZeta (fordZetaLine eta t)‖ =
      ∑' p : Nat.Primes, ∑' m : ℕ,
        (p : ℝ) ^ (-(m : ℝ) * (1 + eta)) *
          Real.cos ((m : ℝ) * t * Real.log p) / m := by
  have hs : 1 < (fordZetaLine eta t).re := by
    simp only [fordZetaLine_re]
    linarith
  rw [log_norm_riemannZeta_eq_prime_power_series hs]
  apply tsum_congr
  intro p
  apply tsum_congr
  intro m
  exact ford_prime_power_term_re eta t p m

end GafniTao
