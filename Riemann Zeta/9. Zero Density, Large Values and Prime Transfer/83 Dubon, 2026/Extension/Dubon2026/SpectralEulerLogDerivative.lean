import Dubon2026.SpectralEulerProduct
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

/-! # The logarithmic derivative of the genuine global spectral Euler product -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- Each actual prime linear denominator has its exact logarithmic derivative, with the original prime logarithm. -/
theorem logDeriv_spectral_linear_factor (p : Nat.Primes) (w s : ℂ) :
    logDeriv (fun t : ℂ => 1 - w * (((p : ℕ) : ℂ) ^ (-t))) s =
      ((Real.log (p : ℕ) : ℂ) * w * (((p : ℕ) : ℂ) ^ (-s))) /
        (1 - w * (((p : ℕ) : ℂ) ^ (-s))) := by
  have hd := ((primeDirichletCoordinate_hasDerivAt p s).const_mul w).const_sub 1
  rw [logDeriv_apply, hd.deriv]
  ring

/-- The genuine logarithmic derivative has the summable first-power prime majorant throughout Re(s)>1. -/
theorem norm_logDeriv_spectral_linear_le (p : Nat.Primes) {w s : ℂ}
    (hw : ‖w‖ ≤ 1) (hs : 0 < s.re) :
    ‖logDeriv (fun t : ℂ => 1 - w * (((p : ℕ) : ℂ) ^ (-t))) s‖ ≤
      (1 / (1 - (2 : ℝ) ^ (-s.re))) * (Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-s.re)) := by
  have hz := norm_primeDirichletCoordinate_le p hs le_rfl
  have hlog : 0 ≤ Real.log (p : ℕ) := Real.log_nonneg (by exact_mod_cast p.property.one_le)
  have hm : ‖w * (((p : ℕ) : ℂ) ^ (-s))‖ ≤ ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg (((p : ℕ) : ℂ) ^ (-s)))
  have hd : 1 - (2 : ℝ) ^ (-s.re) ≤ ‖1 - w * (((p : ℕ) : ℂ) ^ (-s))‖ := by
    have he := norm_sub_norm_le (1 : ℂ) (w * (((p : ℕ) : ℂ) ^ (-s)))
    simp only [norm_one] at he
    linarith
  rw [logDeriv_spectral_linear_factor, norm_div]
  have hn : ‖(Real.log (p : ℕ) : ℂ) * w * (((p : ℕ) : ℂ) ^ (-s))‖ ≤
      Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-s.re) := by
    rw [mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    have he := mul_le_mul_of_nonneg_left hm hlog
    simpa only [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re] using he
  calc
    _ ≤ (Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-s.re)) /
        ‖1 - w * (((p : ℕ) : ℂ) ^ (-s))‖ := div_le_div_of_nonneg_right hn (norm_nonneg _)
    _ ≤ (Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-s.re)) / (1 - (2 : ℝ) ^ (-s.re)) :=
      div_le_div_of_nonneg_left (mul_nonneg hlog (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (sub_pos.mpr hz.2) hd
    _ = _ := by ring

/-- The actual spectral logarithmic derivatives are absolutely summable over all primes and the finite rank. -/
theorem summable_norm_spectral_linear_logDeriv {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : Nat.Primes × Fin d =>
      ‖logDeriv (fun t : ℂ => 1 - w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-t))) s‖) := by
  have hp := summable_prime_log_rpow hs
  have hf : Summable (fun v : Fin d × Nat.Primes =>
      Real.log (v.2 : ℕ) * ((v.2 : ℕ) : ℝ) ^ (-s.re)) :=
    (summable_prod_of_nonneg (fun v : Fin d × Nat.Primes => mul_nonneg
      (Real.log_nonneg (by exact_mod_cast v.2.property.one_le))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))).mpr ⟨fun _ => hp, Summable.of_finite⟩
  apply (hf.prod_symm.mul_left (1 / (1 - (2 : ℝ) ^ (-s.re)))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro v
  exact norm_logDeriv_spectral_linear_le v.1 (hw _ _) (by linarith)

/-- Locally uniform convergence and nonvanishing justify the logarithmic derivative of the actual global Euler product. -/
theorem spectralGlobalLSeries_logDeriv {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (spectralGlobalLSeries w) s = ∑' v : Nat.Primes × Fin d,
      logDeriv (fun t : ℂ => 1 - w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-t))) s := by
  let a : ℝ := (1 + s.re) / 2
  have ha : 1 < a := by dsimp [a]; linarith
  have hsa : a < s.re := by dsimp [a]; linarith
  have hU : IsOpen {t : ℂ | a < t.re} := isOpen_lt continuous_const Complex.continuous_re
  have hn (v : Nat.Primes × Fin d) : 1 - w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
    have hz := norm_primeDirichletCoordinate_le v.1 (by linarith : 0 < s.re) le_rfl
    exact spectralEulerDenominator_ne_zero (hw _ _) (hz.1.trans_lt hz.2)
  have hd (v : Nat.Primes × Fin d) :
      DifferentiableOn ℂ (fun t : ℂ => 1 - w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-t))) {t : ℂ | a < t.re} :=
    (((primeDirichletCoordinate_differentiable v.1).const_mul (w v.1 v.2)).const_sub 1).differentiableOn
  have hp := logDeriv_tprod_eq_tsum hU hsa hn hd
    (summable_norm_spectral_linear_logDeriv hw hs).of_norm
    (spectralGlobalDenominator_multipliableLocallyUniformlyOn hw ha)
    (spectralGlobalDenominator_ne_zero hw hs)
  have hi := logDeriv_fun_zpow (spectralGlobalDenominator_differentiableAt hw hs) (-1 : ℤ)
  simp only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul] at hi
  change -logDeriv (fun t => (spectralGlobalDenominator w t)⁻¹) s = _
  rw [hi, neg_neg]
  exact hp

/-- The global Euler logarithmic derivative is precisely the sum of the actual local finite-rank Euler logarithmic derivatives. -/
theorem spectralGlobalLSeries_logDeriv_eq_local {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (spectralGlobalLSeries w) s =
      ∑' p : Nat.Primes, -logDeriv (primeSpectralEulerFactor w p) s := by
  rw [spectralGlobalLSeries_logDeriv hw hs,
    (summable_norm_spectral_linear_logDeriv hw hs).of_norm.tsum_prod]
  apply tsum_congr
  intro p
  rw [tsum_fintype]
  have hn (i : Fin d) : 1 - w p i * (((p : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
    have hz := norm_primeDirichletCoordinate_le p (by linarith : 0 < s.re) le_rfl
    exact spectralEulerDenominator_ne_zero (hw _ _) (hz.1.trans_lt hz.2)
  have hd (i : Fin d) : DifferentiableAt ℂ (fun t : ℂ => 1 - w p i * (((p : ℕ) : ℂ) ^ (-t))) s :=
    ((primeDirichletCoordinate_differentiable p).differentiableAt.const_mul (w p i)).const_sub 1
  have hp := logDeriv_prod (s := Finset.univ)
    (f := fun i : Fin d => fun t : ℂ => 1 - w p i * (((p : ℕ) : ℂ) ^ (-t)))
    (fun i _ => hn i) (fun i _ => hd i)
  have hi := logDeriv_fun_zpow
    (DifferentiableAt.fun_finsetProd (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hd i)) (-1 : ℤ)
  simp only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul] at hi
  change _ = -logDeriv (fun t : ℂ => (∏ i : Fin d, (1 - w p i * (((p : ℕ) : ℂ) ^ (-t))))⁻¹) s
  rw [hi, neg_neg, hp]

end
end Dubon2026
