import Dubon2026.PrimeSpectralTail
import Mathlib.Analysis.Calculus.LogDeriv

/-! # Exact logarithmic derivative of the actual local spectral Euler product -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The actual finite-rank local spectral Euler factor at a genuine prime. -/
def primeSpectralEulerFactor {d : ℕ} (w : Nat.Primes → Fin d → ℂ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  (∏ i : Fin d, (1 - w p i * (((p : ℕ) : ℂ) ^ (-s))))⁻¹

/-- The original first-prime contribution of the actual spectral roots. -/
def primeSpectralFirstTerm {d : ℕ} (w : Nat.Primes → Fin d → ℂ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  (Real.log (p : ℕ) : ℂ) * (∑ i : Fin d, w p i) * (((p : ℕ) : ℂ) ^ (-s))

/-- The actual prime Dirichlet coordinate has its exact logarithmic derivative factor. -/
theorem primeDirichletCoordinate_hasDerivAt (p : Nat.Primes) (s : ℂ) :
    HasDerivAt (fun t : ℂ => ((p : ℕ) : ℂ) ^ (-t))
      (-((Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s))) s := by
  have he := (hasDerivAt_id s).neg.const_cpow (c := ((p : ℕ) : ℂ))
    (.inl (by exact_mod_cast p.property.ne_zero))
  simp only [Pi.neg_apply, id_eq] at he
  convert he using 1
  rw [← Complex.ofReal_natCast, Complex.ofReal_log (by exact_mod_cast p.property.pos.le)]
  ring

/-- Every genuine local spectral Euler factor is nonzero on Re(s)>0 under the displayed local root bound. -/
theorem primeSpectralEulerFactor_ne_zero {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    primeSpectralEulerFactor w p s ≠ 0 := by
  apply inv_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have hz := norm_primeDirichletCoordinate_le p hs le_rfl
  exact spectralEulerDenominator_ne_zero (hw p i) (hz.1.trans_lt hz.2)

/-- The true finite Euler factor is differentiable throughout its right half-plane of nonvanishing. -/
theorem primeSpectralEulerFactor_differentiableAt {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (primeSpectralEulerFactor w p) s := by
  have hd : DifferentiableAt ℂ (fun t => ∏ i : Fin d,
      (1 - w p i * (((p : ℕ) : ℂ) ^ (-t)))) s :=
    DifferentiableAt.fun_finsetProd (fun i _ =>
      ((primeDirichletCoordinate_differentiable p).differentiableAt.const_mul (w p i)).const_sub 1)
  apply hd.inv
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have hz := norm_primeDirichletCoordinate_le p hs le_rfl
  exact spectralEulerDenominator_ne_zero (hw p i) (hz.1.trans_lt hz.2)

/-- The genuine local logarithmic Euler derivative splits exactly into the first-prime term and the complete higher-prime-power remainder. -/
theorem primeSpectralEulerFactor_logDeriv {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    -logDeriv (primeSpectralEulerFactor w p) s =
      primeSpectralFirstTerm w p s + primeSpectralTailTerm w p s := by
  let z : ℂ := ((p : ℕ) : ℂ) ^ (-s)
  have hz := norm_primeDirichletCoordinate_le p hs le_rfl
  have hn (i : Fin d) : 1 - w p i * z ≠ 0 :=
    spectralEulerDenominator_ne_zero (hw p i) (hz.1.trans_lt hz.2)
  have hd (i : Fin d) : HasDerivAt (fun t : ℂ => 1 - w p i * (((p : ℕ) : ℂ) ^ (-t)))
      ((Real.log (p : ℕ) : ℂ) * w p i * z) s := by
    convert ((primeDirichletCoordinate_hasDerivAt p s).const_mul (w p i)).const_sub 1 using 1
    dsimp only [z]
    ring
  have hp := logDeriv_prod (s := Finset.univ)
    (f := fun i : Fin d => fun t : ℂ => 1 - w p i * (((p : ℕ) : ℂ) ^ (-t)))
    (fun i _ => hn i) (fun i _ => (hd i).differentiableAt)
  have hi := logDeriv_fun_zpow
    (DifferentiableAt.fun_finsetProd (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      (hd i).differentiableAt)) (-1 : ℤ)
  simp only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul] at hi
  change -logDeriv (fun t : ℂ => (∏ i : Fin d, (1 - w p i * (((p : ℕ) : ℂ) ^ (-t))))⁻¹) s = _
  rw [hi, neg_neg, hp]
  calc
    _ = ∑ i : Fin d, (Real.log (p : ℕ) : ℂ) * (w p i * z + spectralEulerTail (w p i) z) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [logDeriv_apply, (hd i).deriv]
      change ((Real.log (p : ℕ) : ℂ) * w p i * z) / (1 - w p i * z) = _
      rw [← spectralEulerTail_identity (hn i)]
      ring
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, primeSpectralFirstTerm,
        primeSpectralTailTerm, z]
      rw [← Finset.sum_mul]
      ring

end
end Dubon2026
