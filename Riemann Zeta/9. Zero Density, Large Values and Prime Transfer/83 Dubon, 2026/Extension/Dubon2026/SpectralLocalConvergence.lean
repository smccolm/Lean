import Dubon2026.SpectralDirichletCoefficients
import Dubon2026.SpectralDenominatorConvergence

/-! # Actual global Dirichlet convergence bounds each literal local root -/

namespace Dubon2026

noncomputable section

/-- Restricting the genuine global Dirichlet series to prime powers gives its actual local
formal Euler series, with an injective indexing map. -/
theorem spectral_local_summable_of_LSeriesSummable {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) {s : ℂ}
    (hs : LSeriesSummable (spectralDirichletCoefficient w) s) (p : Nat.Primes) :
    Summable (fun n : ℕ => PowerSeries.coeff n (spectralFormalEuler Finset.univ (w p)) *
      ((((p : ℕ) : ℂ) ^ (-s)) ^ n)) := by
  have hh := hs.comp_injective (Nat.pow_right_injective p.property.two_le)
  apply hh.congr
  intro n
  dsimp only [Function.comp_apply]
  have hzero : spectralDirichletCoefficient w 0 = 0 := assembledEulerCoefficient_zero _
  rw [LSeries.term_def₀ hzero,
    spectralDirichletCoefficient_prime_pow, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-- Absolute convergence of the actual global spectral Dirichlet series bounds every genuine
local root by p^Re(s); the numerator-one identity excludes local cancellation. -/
theorem spectral_root_norm_lt_of_LSeriesSummable {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) {s : ℂ}
    (hs : LSeriesSummable (spectralDirichletCoefficient w) s) (p : Nat.Primes) (i : ι) :
    ‖w p i‖ < ((p : ℕ) : ℝ) ^ s.re := by
  have hh := spectral_root_norm_lt_one_of_summable Finset.univ (w p)
    (((p : ℕ) : ℂ) ^ (-s)) (spectral_local_summable_of_LSeriesSummable w hs p) (Finset.mem_univ i)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re,
    Real.rpow_neg (Nat.cast_nonneg _), ← div_eq_mul_inv,
    div_lt_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast p.property.pos) _), one_mul] at hh
  exact hh

end
end Dubon2026
