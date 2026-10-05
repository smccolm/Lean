import DongWangWangZhang2026.MeanValueMaximum
import DongWangWangZhang2026.CoefficientMean
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Euler-product control of the actual prime distance

The branch-free logarithmic entry adapts the short proof in node 74's
`GafniTao/FordEulerProduct.lean` to the installed Mathlib graph. Its unrelated
Fourier-kernel import chain is not needed here. Prime-power positivity then
gives a distance bound without discarding a coefficient of the distance.
-/

namespace DongWangWangZhang2026

open Complex Filter MeasureTheory
open scoped Topology

noncomputable section

theorem summable_primeEulerLog {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => -Complex.log (1 - (p : ℂ) ^ (-s))) := by
  have hpBound (p : Nat.Primes) : ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s).re := by
    rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (Complex.re_neg_ne_zero_of_one_lt_re hs)]
  refine (Nat.Primes.summable_rpow.mpr ?_).of_nonneg_of_le
    (fun _ => norm_nonneg _) hpBound |>.of_norm.clog_one_sub.neg
  rw [Complex.neg_re]
  linarith

/-- Real logarithms avoid any branch choice for the logarithm of zeta. -/
theorem log_norm_zeta_eq_prime_logs {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖riemannZeta s‖ =
      ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-s))).re := by
  rw [← riemannZeta_eulerProduct_exp_log hs, Complex.norm_exp, Real.log_exp,
    Complex.re_tsum (summable_primeEulerLog hs)]

/-- Every prime-power term of the logarithmic norm deficit is nonnegative;
retaining the first term preserves its exact coefficient. -/
theorem norm_sub_re_le_log_distance {z : ℂ} (hz : ‖z‖ < 1) :
    ‖z‖ - z.re ≤ -(Complex.log (1 - (‖z‖ : ℂ))).re + (Complex.log (1 - z)).re := by
  have hq : ‖(‖z‖ : ℂ)‖ < 1 := by simpa using hz
  have hsum := Complex.hasSum_re
    ((Complex.hasSum_taylorSeries_neg_log hq).sub (Complex.hasSum_taylorSeries_neg_log hz))
  have hnonneg (m : ℕ) : 0 ≤ (((‖z‖ : ℂ) ^ m / m - z ^ m / m).re) := by
    rw [Complex.sub_re, Complex.div_natCast_re, Complex.div_natCast_re]
    have h := Complex.re_le_norm (z ^ m)
    rw [norm_pow] at h
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using
      sub_nonneg.mpr (div_le_div_of_nonneg_right h (Nat.cast_nonneg m))
  have h := le_hasSum hsum 1 (fun m _ => hnonneg m)
  simpa only [pow_one, Nat.cast_one, div_one, Complex.sub_re, Complex.ofReal_re,
    Complex.neg_re, sub_neg_eq_add] using h

theorem norm_primeZetaPower {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (Complex.re_neg_ne_zero_of_one_lt_re hs),
    Complex.neg_re]

theorem summable_primeZetaPower {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => (p : ℂ) ^ (-s)) := by
  apply Summable.of_norm
  simp_rw [norm_primeZetaPower hs]
  exact Nat.Primes.summable_rpow.mpr (by linarith)

/-- The absolutely convergent prime distance on an abscissa strictly above one. -/
def dampedPrimeDistance (s : ℂ) : ℝ :=
  ∑' p : Nat.Primes, ((p : ℝ) ^ (-s.re) - ((p : ℂ) ^ (-s)).re)

theorem summable_dampedPrimeDistance {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s.re) - ((p : ℂ) ^ (-s)).re) :=
  (Nat.Primes.summable_rpow.mpr (by linarith : -s.re < -1)).sub
    (Complex.hasSum_re (summable_primeZetaPower hs).hasSum).summable

theorem dampedPrimeDistance_nonneg {s : ℂ} (hs : 1 < s.re) : 0 ≤ dampedPrimeDistance s := by
  apply tsum_nonneg
  intro p
  have h := Complex.re_le_norm ((p : ℂ) ^ (-s))
  rw [norm_primeZetaPower hs p] at h
  exact sub_nonneg.mpr h

/-- The prime-power Euler terms all have the correct sign, so the first-prime
distance has coefficient one and no uncontrolled analytic remainder. -/
theorem dampedPrimeDistance_le_log_norm_sub {s : ℂ} (hs : 1 < s.re) :
    dampedPrimeDistance s ≤ Real.log ‖riemannZeta (s.re : ℂ)‖ - Real.log ‖riemannZeta s‖ := by
  have hsR : 1 < (s.re : ℂ).re := hs
  have hlogsR := (Complex.hasSum_re (summable_primeEulerLog hsR).hasSum).summable
  have hlogs := (Complex.hasSum_re (summable_primeEulerLog hs).hasSum).summable
  rw [log_norm_zeta_eq_prime_logs hsR, log_norm_zeta_eq_prime_logs hs, ← hlogsR.tsum_sub hlogs]
  apply (summable_dampedPrimeDistance hs).tsum_le_tsum _ (hlogsR.sub hlogs)
  intro p
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hz : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_primeZetaPower hs p, Real.rpow_neg (by positivity : (0 : ℝ) ≤ p)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp (by linarith))
  have h := norm_sub_re_le_log_distance hz
  rw [norm_primeZetaPower hs p] at h
  have heq : (((p : ℝ) ^ (-s.re) : ℝ) : ℂ) = (p : ℂ) ^ (-(s.re : ℂ)) := by
    rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ p), Complex.ofReal_neg]
    rfl
  rw [heq] at h
  simpa only [Complex.neg_re, sub_neg_eq_add] using h

/-- Exponential suppression of the actual zeta value by its convergent prime
distance. No prime-number-theorem or mean-value premise is required. -/
theorem norm_zeta_le_exp_neg_dampedPrimeDistance {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ * Real.exp (-dampedPrimeDistance s) := by
  have hsR : 1 < (s.re : ℂ).re := hs
  have hz := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs)
  have hzR := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hsR)
  have h := Real.exp_le_exp.mpr (show Real.log ‖riemannZeta s‖ ≤
      Real.log ‖riemannZeta (s.re : ℂ)‖ - dampedPrimeDistance s by
    linarith [dampedPrimeDistance_le_log_norm_sub hs])
  rwa [Real.exp_sub, Real.exp_log hz, Real.exp_log hzR, div_eq_mul_inv, ← Real.exp_neg] at h

theorem primeZetaPower_re_deficit (σ τ : ℝ) (hσ : 1 < σ) (p : Nat.Primes) :
    (p : ℝ) ^ (-σ) - (((p : ℂ) ^ (-((σ : ℂ) - (τ : ℂ) * I))).re) =
      (p : ℝ) ^ (-σ) * (1 - (zetaTerm τ p).re) := by
  have hcoeff : zetaPhaseCoeff σ τ p = (p : ℂ) ^ (-((σ : ℂ) - (τ : ℂ) * I)) := by
    rw [zetaPhaseCoeff, zetaTerm_div_cpow τ (by simpa using hσ), one_div, Complex.cpow_neg]
  have hcast : (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ p), Complex.ofReal_neg]
    rfl
  rw [← hcoeff, zetaPhaseCoeff, div_eq_mul_inv, ← Complex.cpow_neg, hcast]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- Every finite portion of the source's damped prime sum is bounded by the
convergent Euler distance; the subtype conversion preserves the prime cutoff. -/
theorem sum_damped_prime_phase_le (σ τ x : ℝ) (hσ : 1 < σ) :
    (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      (p : ℝ) ^ (-σ) * (1 - (zetaTerm τ p).re)) ≤
        dampedPrimeDistance ((σ : ℂ) - (τ : ℂ) * I) := by
  have hs : 1 < ((σ : ℂ) - (τ : ℂ) * I).re := by simpa using hσ
  have heq (p : Nat.Primes) :
      (p : ℝ) ^ (-((σ : ℂ) - (τ : ℂ) * I).re) -
          (((p : ℂ) ^ (-((σ : ℂ) - (τ : ℂ) * I))).re) =
        (p : ℝ) ^ (-σ) * (1 - (zetaTerm τ p).re) := by
    simpa using primeZetaPower_re_deficit σ τ hσ p
  have hsum := (summable_dampedPrimeDistance hs).hasSum
  change HasSum _ (dampedPrimeDistance ((σ : ℂ) - (τ : ℂ) * I)) at hsum
  simp_rw [heq] at hsum
  rw [← Finset.sum_subtype_of_mem
    (fun p : ℕ => (p : ℝ) ^ (-σ) * (1 - (zetaTerm τ p).re))
    (fun p hp => (Finset.mem_filter.mp hp).2)]
  apply sum_le_hasSum _ _ hsum
  intro p _
  have hre := Complex.re_le_norm (zetaTerm τ p)
  rw [norm_zetaTerm τ p.prop.pos] at hre
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sub_nonneg.mpr hre)

/-- The needed logarithmic reciprocal prime bound follows from the already
proved Abel adapter and Mathlib's Chebyshev estimate, without a PNT assumption. -/
theorem sum_prime_log_div_le {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log p / p) ≤
      (Real.log 4 + 4) * (1 + Real.log x) := by
  have hmean (u : ℝ) (hu : u ∈ Set.Icc 1 x) :
      (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, ArithmeticFunction.vonMangoldt n) ≤ (Real.log 4 + 4) * u := by
    have hI : Finset.Icc 0 ⌊u⌋₊ = insert 0 (Finset.Ioc 0 ⌊u⌋₊) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
      omega
    rw [hI, Finset.sum_insert (by simp)]
    simpa only [ArithmeticFunction.map_zero, zero_add, Chebyshev.psi] using
      Chebyshev.psi_le_const_mul_self (zero_le_one.trans hu.1)
  have h := reciprocal_tail_le_of_mean_bound ArithmeticFunction.vonMangoldt
    (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (a := 1) (b := x) (by norm_num) hx hmean
  simp only [Nat.floor_one, div_one] at h
  apply le_trans _ h
  calc
    _ = ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ArithmeticFunction.vonMangoldt p / p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
    _ ≤ _ := ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_Ioc.mpr ⟨hp'.2.one_lt, (Finset.mem_Icc.mp hp'.1).2⟩
  · intro p _ _
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg p)

theorem prime_phase_damping_error_le (τ δ : ℝ) (hδ : 0 ≤ δ) {p : ℕ} (hp : p.Prime) :
    (1 - (zetaTerm τ p).re) / p -
      (p : ℝ) ^ (-(1 + δ)) * (1 - (zetaTerm τ p).re) ≤
        2 * δ * Real.log p / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hre := Complex.re_le_norm (zetaTerm τ p)
  rw [norm_zetaTerm τ hp.pos] at hre
  have hreNeg := Complex.re_le_norm (-zetaTerm τ p)
  rw [Complex.neg_re, norm_neg, norm_zetaTerm τ hp.pos] at hreNeg
  have hD0 : 0 ≤ 1 - (zetaTerm τ p).re := by linarith
  have hD2 : 1 - (zetaTerm τ p).re ≤ 2 := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hcut : 1 - (p : ℝ) ^ (-δ) ≤ δ * Real.log p := by
    rw [Real.rpow_def_of_pos hp0]
    have h := Real.add_one_le_exp (Real.log p * (-δ))
    nlinarith
  have hq : (p : ℝ) ^ (-(1 + δ)) = (p : ℝ)⁻¹ * (p : ℝ) ^ (-δ) := by
    rw [show -(1 + δ) = (-1 : ℝ) + -δ by ring, Real.rpow_add hp0, Real.rpow_neg_one]
  calc
    _ = ((1 - (zetaTerm τ p).re) * (1 - (p : ℝ) ^ (-δ))) / p := by rw [hq]; ring
    _ ≤ (2 * (δ * Real.log p)) / p := div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hcut hD0).trans
        (mul_le_mul_of_nonneg_right hD2 (mul_nonneg hδ hlog))) hp0.le
    _ = _ := by ring

theorem primePhaseDistance_le_damped (τ δ x : ℝ) (hδ : 0 < δ) (hx : 1 ≤ x) :
    primePhaseDistance x τ ≤ dampedPrimeDistance (((1 + δ : ℝ) : ℂ) - (τ : ℂ) * I) +
      2 * δ * ((Real.log 4 + 4) * (1 + Real.log x)) := by
  let P := (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime
  have hsum := Finset.sum_le_sum (s := P) (fun p hp =>
    prime_phase_damping_error_le τ δ hδ.le (Finset.mem_filter.mp hp).2)
  rw [Finset.sum_sub_distrib] at hsum
  have hscale : (∑ p ∈ P, 2 * δ * Real.log p / p) =
      2 * δ * ∑ p ∈ P, Real.log p / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hscale] at hsum
  have hprime := mul_le_mul_of_nonneg_left (sum_prime_log_div_le hx)
    (show 0 ≤ 2 * δ by positivity)
  have hfull := sum_damped_prime_phase_le (1 + δ) τ x (by linarith)
  change (∑ p ∈ P, (1 - (zetaTerm τ p).re) / p) ≤ _
  dsimp only [P] at hsum
  linarith

/-- The paper's finite prime distance controls the actual zeta series at its
source abscissa. The loss is absolute and independent of both height and cutoff. -/
theorem norm_zeta_shift_le_primePhaseDistance (x τ : ℝ) (hx : 1 < x)
    (hxlog : 1 ≤ Real.log x) :
    ‖riemannZeta ((((1 + 1 / Real.log x : ℝ) : ℂ)) - (τ : ℂ) * I)‖ ≤
      (1 + Real.log x) * Real.exp (4 * (Real.log 4 + 4) - primePhaseDistance x τ) := by
  let σ : ℝ := 1 + 1 / Real.log x
  let s : ℂ := (σ : ℂ) - (τ : ℂ) * I
  have hlog := Real.log_pos hx
  have hσ : 1 < σ := by dsimp [σ]; linarith [one_div_pos.mpr hlog]
  have hs : 1 < s.re := by simpa [s] using hσ
  have hD := primePhaseDistance_le_damped τ (1 / Real.log x) x (one_div_pos.mpr hlog) hx.le
  have hC : 0 ≤ Real.log 4 + 4 := by positivity
  have herr : 2 * (1 / Real.log x) * ((Real.log 4 + 4) * (1 + Real.log x)) ≤
      4 * (Real.log 4 + 4) := by
    have hrec : 1 / Real.log x ≤ 1 := (div_le_one hlog).mpr hxlog
    have heq : 2 * (1 / Real.log x) * ((Real.log 4 + 4) * (1 + Real.log x)) =
        2 * (Real.log 4 + 4) * (1 + 1 / Real.log x) := by field_simp; ring
    rw [heq]
    nlinarith
  have hbase : ‖riemannZeta (σ : ℂ)‖ ≤ 1 + Real.log x := by
    have h := (norm_tsum_logFrequency_le (zetaPhaseCoeff σ 0)
      (summable_norm_zetaPhaseCoeff σ 0 hσ) 0).trans (tsum_norm_zetaPhaseCoeff_le σ 0 hσ)
    rw [tsum_zetaPhaseCoeff_phase σ 0 0 hσ] at h
    simpa [σ] using h
  have hexp : Real.exp (-dampedPrimeDistance s) ≤
      Real.exp (4 * (Real.log 4 + 4) - primePhaseDistance x τ) := by
    apply Real.exp_le_exp.mpr
    change primePhaseDistance x τ ≤ dampedPrimeDistance s + _ at hD
    linarith
  have h := norm_zeta_le_exp_neg_dampedPrimeDistance hs
  simp only [s, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] at h
  exact h.trans (mul_le_mul hbase hexp (Real.exp_pos _).le (by positivity))

/-- The source's actual maximizing-function interface, at any candidate twist.
In particular it applies to the attained maximum without another hypothesis. -/
theorem norm_twistZeta_le_primePhaseDistance (x t u : ℝ) (hx : 1 < x)
    (hxlog : 1 ≤ Real.log x) :
    ‖riemannZeta (twistZetaPoint x t u)‖ ≤
      (1 + Real.log x) * Real.exp (4 * (Real.log 4 + 4) - primePhaseDistance x (t - u)) := by
  have h := norm_zeta_shift_le_primePhaseDistance x (t - u) hx hxlog
  have heq : (((1 + 1 / Real.log x : ℝ) : ℂ)) - ((t - u : ℝ) : ℂ) * I =
      twistZetaPoint x t u := by
    unfold twistZetaPoint
    push_cast
    ring
  rwa [heq] at h

theorem tsum_prime_rpow_le_log_norm_zeta (σ : ℝ) (hσ : 1 < σ) :
    (∑' p : Nat.Primes, (p : ℝ) ^ (-σ)) ≤ Real.log ‖riemannZeta (σ : ℂ)‖ := by
  have hs : 1 < (σ : ℂ).re := hσ
  rw [log_norm_zeta_eq_prime_logs hs]
  apply (Nat.Primes.summable_rpow.mpr (by linarith : -σ < -1)).tsum_le_tsum _
    (Complex.hasSum_re (summable_primeEulerLog hs).hasSum).summable
  intro p
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hq : (p : ℝ) ^ (-σ) < 1 := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp (by linarith))
  have hcast : (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ p), Complex.ofReal_neg]
    rfl
  rw [hcast, Complex.neg_re, Complex.log_re,
    show (1 : ℂ) - (((p : ℝ) ^ (-σ) : ℝ) : ℂ) = ((1 - (p : ℝ) ^ (-σ) : ℝ) : ℂ) by
      push_cast; rfl,
    Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - (p : ℝ) ^ (-σ))
  linarith

theorem sum_prime_rpow_le_log_norm_zeta (σ x : ℝ) (hσ : 1 < σ) :
    (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (p : ℝ) ^ (-σ)) ≤
      Real.log ‖riemannZeta (σ : ℂ)‖ := by
  have hsum : HasSum (fun p : Nat.Primes => (p : ℝ) ^ (-σ))
      (∑' p : Nat.Primes, (p : ℝ) ^ (-σ)) :=
    (Nat.Primes.summable_rpow.mpr (by linarith : -σ < -1)).hasSum
  apply le_trans _ (tsum_prime_rpow_le_log_norm_zeta σ hσ)
  rw [← Finset.sum_subtype_of_mem (fun p : ℕ => (p : ℝ) ^ (-σ))
    (fun p hp => (Finset.mem_filter.mp hp).2)]
  apply sum_le_hasSum _ _ hsum
  intro p _
  exact Real.rpow_nonneg (Nat.cast_nonneg p.val) _

theorem prime_reciprocal_damping_error_le (δ : ℝ) {p : ℕ} (hp : p.Prime) :
    1 / (p : ℝ) - (p : ℝ) ^ (-(1 + δ)) ≤ δ * Real.log p / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcut : 1 - (p : ℝ) ^ (-δ) ≤ δ * Real.log p := by
    rw [Real.rpow_def_of_pos hp0]
    have h := Real.add_one_le_exp (Real.log p * (-δ))
    nlinarith
  have hq : (p : ℝ) ^ (-(1 + δ)) = (p : ℝ)⁻¹ * (p : ℝ) ^ (-δ) := by
    rw [show -(1 + δ) = (-1 : ℝ) + -δ by ring, Real.rpow_add hp0, Real.rpow_neg_one]
  calc
    _ = (1 - (p : ℝ) ^ (-δ)) / p := by rw [hq]; ring
    _ ≤ _ := div_le_div_of_nonneg_right hcut hp0.le

/-- A reciprocal-prime upper bound with coefficient one on the logarithmic
term, obtained from the convergent Euler product and the Chebyshev adapter. -/
theorem sum_prime_reciprocal_le {x : ℝ} (hx : 1 < x) (hxlog : 1 ≤ Real.log x) :
    (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p) ≤
      Real.log (1 + Real.log x) + 2 * (Real.log 4 + 4) := by
  let δ : ℝ := 1 / Real.log x
  let P := (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime
  have hlog := Real.log_pos hx
  have hδ : 0 < δ := one_div_pos.mpr hlog
  have hsum := Finset.sum_le_sum (s := P) (fun p hp =>
    prime_reciprocal_damping_error_le δ (Finset.mem_filter.mp hp).2)
  rw [Finset.sum_sub_distrib] at hsum
  have hscale : (∑ p ∈ P, δ * Real.log p / p) = δ * ∑ p ∈ P, Real.log p / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hscale] at hsum
  have hprime := mul_le_mul_of_nonneg_left (sum_prime_log_div_le hx.le) hδ.le
  have hfull := sum_prime_rpow_le_log_norm_zeta (1 + δ) x (by linarith)
  have hbase : ‖riemannZeta ((1 + δ : ℝ) : ℂ)‖ ≤ 1 + Real.log x := by
    have hσ : 1 < 1 + δ := by linarith
    have h := (norm_tsum_logFrequency_le (zetaPhaseCoeff (1 + δ) 0)
      (summable_norm_zetaPhaseCoeff (1 + δ) 0 hσ) 0).trans
        (tsum_norm_zetaPhaseCoeff_le (1 + δ) 0 hσ)
    rw [tsum_zetaPhaseCoeff_phase (1 + δ) 0 0 hσ] at h
    simpa [δ] using h
  have hz := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re
    (show 1 < (((1 + δ : ℝ) : ℂ)).re by simpa using (show 1 < 1 + δ by linarith)))
  have hlogBase := Real.log_le_log hz hbase
  have herr : δ * ((Real.log 4 + 4) * (1 + Real.log x)) ≤ 2 * (Real.log 4 + 4) := by
    have hrec : 1 / Real.log x ≤ 1 := (div_le_one hlog).mpr hxlog
    have hC : 0 ≤ Real.log 4 + 4 := by positivity
    have heq : δ * ((Real.log 4 + 4) * (1 + Real.log x)) =
        (Real.log 4 + 4) * (1 + 1 / Real.log x) := by dsimp [δ]; field_simp; ring
    rw [heq]
    nlinarith
  dsimp only [P] at hsum
  linarith

theorem prime_phase_deviation_le_log_bound (x τ : ℝ) (hx : 1 < x)
    (hxlog : 1 ≤ Real.log x) :
    (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - zetaTerm τ p‖ / p) ≤
      Real.sqrt (2 * primePhaseDistance x τ *
        (Real.log (1 + Real.log x) + 2 * (Real.log 4 + 4))) := by
  apply (prime_phase_deviation_le x τ).trans
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left (sum_prime_reciprocal_le hx hxlog)
    (mul_nonneg (by norm_num) (primePhaseDistance_nonneg x τ))

/-- The source comparison now depends only on the actual prime distance and
the logarithmic cutoff, with the auxiliary reciprocal-prime sum discharged. -/
theorem norm_normalized_mean_comparison_le_distance (t t₀ x : ℝ)
    (hx : 1 < x) (hxlog : 1 ≤ Real.log x) :
    ‖zetaSum x t / (x : ℂ) -
      ((x : ℂ) ^ ((t₀ : ℂ) * I) / ((t₀ : ℂ) * I + 1)) *
        (zetaSum x (t - t₀) / (x : ℂ))‖ ≤
      (42 * (2 * (Real.log 4 + 4) + 1) * Real.exp 8) *
        Real.log (Real.exp 1 + |t₀|) / Real.log x *
          Real.exp (Real.sqrt (2 * primePhaseDistance x (t - t₀) *
            (Real.log (1 + Real.log x) + 2 * (Real.log 4 + 4)))) := by
  apply (norm_normalized_mean_comparison_le t t₀ hx).trans
  apply mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (prime_phase_deviation_le_log_bound x (t - t₀) hx hxlog))
  have hlog : 0 ≤ Real.log (Real.exp 1 + |t₀|) :=
    Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ), abs_nonneg t₀])
  have hxlog0 := Real.log_pos hx
  positivity

end
end DongWangWangZhang2026
