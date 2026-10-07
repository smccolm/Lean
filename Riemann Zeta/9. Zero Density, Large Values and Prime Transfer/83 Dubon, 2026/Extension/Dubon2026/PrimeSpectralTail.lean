import Dubon2026.SpectralEulerTail
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! # The actual higher-prime-power spectral remainder is holomorphic on Re(s)>1/2 -/

namespace Dubon2026

open Filter ArithmeticFunction
open scoped Topology

noncomputable section

/-- The higher-order logarithmic derivative contribution at a genuine prime. -/
def primeSpectralTailTerm {d : ℕ} (w : Nat.Primes → Fin d → ℂ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  (Real.log (p : ℕ) : ℂ) * ∑ i : Fin d, spectralEulerTail (w p i) (((p : ℕ) : ℂ) ^ (-s))

/-- The actual sum of higher-prime-power logarithmic Euler contributions. -/
def primeSpectralTail {d : ℕ} (w : Nat.Primes → Fin d → ℂ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, primeSpectralTailTerm w p s

/-- The genuine prime logarithmic majorant is summable for every exponent greater than one. -/
theorem summable_prime_log_rpow {b : ℝ} (hb : 1 < b) :
    Summable (fun p : Nat.Primes => Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-b)) := by
  have he := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (b : ℂ)) (by simpa using hb)).norm.comp_injective
    (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p : ℕ)))
  apply he.congr
  intro p
  dsimp only [Function.comp_apply]
  rw [LSeries.term_def, if_neg p.property.ne_zero, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (vonMangoldt_nonneg (n := (p : ℕ))),
    vonMangoldt_apply_prime p.property, Complex.norm_natCast_cpow_of_pos p.property.pos,
    Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg (p : ℕ))]
  exact div_eq_mul_inv _ _

/-- The exact local tail has a uniformly summable quadratic prime majorant on each smaller right half-plane. -/
theorem norm_primeSpectralTailTerm_le {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) (p : Nat.Primes) {a : ℝ} (ha : 0 < a)
    {s : ℂ} (hs : a ≤ s.re) :
    ‖primeSpectralTailTerm w p s‖ ≤
      ((d : ℝ) / (1 - (2 : ℝ) ^ (-a))) *
        (Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(2 * a))) := by
  have hz := norm_primeDirichletCoordinate_le p ha hs
  have hp : 0 ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (p : ℕ) := Real.log_nonneg (by exact_mod_cast p.property.one_le)
  have hcoord : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-a) := by
    rw [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_le) (neg_le_neg hs)
  have hpow : (((p : ℕ) : ℝ) ^ (-a)) ^ 2 = ((p : ℕ) : ℝ) ^ (-(2 * a)) := by
    rw [← Real.rpow_mul_natCast hp]
    congr 1
    push_cast
    ring
  have hlocal (i : Fin d) : ‖spectralEulerTail (w p i) (((p : ℕ) : ℂ) ^ (-s))‖ ≤
      ((p : ℕ) : ℝ) ^ (-(2 * a)) / (1 - (2 : ℝ) ^ (-a)) := by
    have hsq : ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 ≤ (((p : ℕ) : ℝ) ^ (-a)) ^ 2 := by
      nlinarith [norm_nonneg (((p : ℕ) : ℂ) ^ (-s)), Real.rpow_nonneg hp (-a)]
    rw [hpow] at hsq
    exact (norm_spectralEulerTail_le (hw p i) hz.1 hz.2).trans
      (div_le_div_of_nonneg_right hsq (sub_nonneg.mpr hz.2.le))
  simp only [primeSpectralTailTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog]
  calc
    _ ≤ Real.log (p : ℕ) * ∑ i : Fin d, ‖spectralEulerTail (w p i) (((p : ℕ) : ℂ) ^ (-s))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hlog
    _ ≤ Real.log (p : ℕ) * ∑ _i : Fin d,
        ((p : ℕ) : ℝ) ^ (-(2 * a)) / (1 - (2 : ℝ) ^ (-a)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hlocal i)) hlog
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Absolute convergence of the actual higher-prime-power remainder holds throughout Re(s)>1/2. -/
theorem summable_norm_primeSpectralTailTerm {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun p : Nat.Primes => ‖primeSpectralTailTerm w p s‖) := by
  have hu := (summable_prime_log_rpow (b := 2 * s.re) (by linarith)).mul_left
    ((d : ℝ) / (1 - (2 : ℝ) ^ (-s.re)))
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => norm_primeSpectralTailTerm_le hw p (by linarith) le_rfl)

/-- Each actual finite local spectral tail is differentiable on Re(s)>0. -/
theorem primeSpectralTailTerm_differentiableAt {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (primeSpectralTailTerm w p) s := by
  exact (DifferentiableAt.fun_sum (fun i _ => spectralEulerTail_prime_differentiableAt p (hw p i) hs)).const_mul _

/-- The uniformly summable prime majorant proves actual holomorphy of the full higher-prime-power remainder. -/
theorem primeSpectralTail_differentiableAt {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (primeSpectralTail w) s := by
  let a : ℝ := (s.re + 1 / 2) / 2
  let U : Set ℂ := {t | a < t.re}
  have ha : 1 / 2 < a := by dsimp [a]; linarith
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := by dsimp [U,a]; linarith
  have hu := (summable_prime_log_rpow (b := 2 * a) (by linarith)).mul_left
    ((d : ℝ) / (1 - (2 : ℝ) ^ (-a)))
  have hf (p : Nat.Primes) : DifferentiableOn ℂ (primeSpectralTailTerm w p) U := by
    intro t ht
    exact (primeSpectralTailTerm_differentiableAt hw p (by dsimp [U] at ht; linarith)).differentiableWithinAt
  exact (Complex.differentiableOn_tsum_of_summable_norm hu hf hU
    (fun p t ht => norm_primeSpectralTailTerm_le hw p (by linarith) ht.le)).differentiableAt (hU.mem_nhds hsU)

/-- The genuine prime spectral remainder is holomorphic on its full half-plane of quadratic convergence. -/
theorem primeSpectralTail_analyticOnNhd {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) :
    AnalyticOnNhd ℂ (primeSpectralTail w) {s : ℂ | 1 / 2 < s.re} := by
  have hh : DifferentiableOn ℂ (primeSpectralTail w) {s : ℂ | 1 / 2 < s.re} :=
    fun s hs => (primeSpectralTail_differentiableAt hw hs).differentiableWithinAt
  exact hh.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end
end Dubon2026
