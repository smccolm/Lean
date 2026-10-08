import Dubon2026.SpectralEulerProduct

/-! # Prime-indexed convergence of the actual finite-rank spectral Euler product -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- Grouping a genuinely convergent double Euler product into its finite prime factors preserves its value. -/
theorem spectralGlobalDenominator_hasProd_of_multipliable {d : ℕ}
    {w : Nat.Primes → Fin d → ℂ} {s : ℂ}
    (hprod : Multipliable (fun v : Nat.Primes × Fin d =>
      1 - w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s)))) :
    HasProd (fun p : Nat.Primes => ∏ i : Fin d, (1 - w p i * (((p : ℕ) : ℂ) ^ (-s))))
      (spectralGlobalDenominator w s) :=
  hprod.hasProd.prod_fiberwise (fun _ => hasProd_fintype _)

/-- Inversion of a nonzero convergent spectral product gives its actual prime-indexed reciprocal Euler product. -/
theorem spectralGlobalLSeries_hasProd_of_multipliable {d : ℕ}
    {w : Nat.Primes → Fin d → ℂ} {s : ℂ}
    (hprod : Multipliable (fun v : Nat.Primes × Fin d =>
      1 - w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))
    (hne : spectralGlobalDenominator w s ≠ 0) :
    HasProd (fun p : Nat.Primes => primeSpectralEulerFactor w p s) (spectralGlobalLSeries w s) := by
  have he := spectralGlobalDenominator_hasProd_of_multipliable hprod
  change Tendsto (fun t : Finset Nat.Primes => ∏ p ∈ t,
    ∏ i : Fin d, (1 - w p i * (((p : ℕ) : ℂ) ^ (-s)))) atTop (𝓝 (spectralGlobalDenominator w s)) at he
  have hi := he.inv₀ hne
  change Tendsto (fun t : Finset Nat.Primes => ∏ p ∈ t,
    (∏ i : Fin d, (1 - w p i * (((p : ℕ) : ℂ) ^ (-s))))⁻¹) atTop (𝓝 ((spectralGlobalDenominator w s)⁻¹))
  simpa only [Finset.prod_inv_distrib] using hi

/-- The genuine linear spectral factors form a convergent product over both primes and spectral index. -/
theorem multipliable_spectral_linear_factors {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun v : Nat.Primes × Fin d => 1 - w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))) := by
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
    (summable_norm_spectral_prime_perturbation hw hs)

/-- Grouping the actual convergent spectral product into its finite local factors preserves its literal value. -/
theorem spectralGlobalDenominator_hasProd {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => ∏ i : Fin d, (1 - w p i * (((p : ℕ) : ℂ) ^ (-s))))
      (spectralGlobalDenominator w s) := by
  have he := multipliable_spectral_linear_factors hw hs
  exact he.hasProd.prod_fiberwise (fun _ => hasProd_fintype _)

/-- Inverting the nonzero limit proves the genuine prime-indexed Euler product of the local reciprocal factors. -/
theorem spectralGlobalLSeries_hasProd {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => primeSpectralEulerFactor w p s) (spectralGlobalLSeries w s) := by
  have he := spectralGlobalDenominator_hasProd hw hs
  change Tendsto (fun t : Finset Nat.Primes => ∏ p ∈ t,
    ∏ i : Fin d, (1 - w p i * (((p : ℕ) : ℂ) ^ (-s)))) atTop (𝓝 (spectralGlobalDenominator w s)) at he
  have hi := he.inv₀ (spectralGlobalDenominator_ne_zero hw hs)
  change Tendsto (fun t : Finset Nat.Primes => ∏ p ∈ t,
    (∏ i : Fin d, (1 - w p i * (((p : ℕ) : ℂ) ^ (-s))))⁻¹) atTop (𝓝 ((spectralGlobalDenominator w s)⁻¹))
  simpa only [Finset.prod_inv_distrib] using hi

end
end Dubon2026
