import Dubon2026.SpectralEulerHasProd

/-! # Exact spectral shifts and genuine Euler convergence under polynomial prime bounds -/

namespace Dubon2026

noncomputable section

/-- Rescale actual spectral roots by the exact positive-prime complex power. -/
def spectralShiftRoots {d : ℕ} (w : Nat.Primes → Fin d → ℂ) (A : ℝ)
    (p : Nat.Primes) (i : Fin d) : ℂ := w p i * (((p : ℕ) : ℂ) ^ (-(A : ℂ)))

/-- The genuine spectral coordinate is unchanged by the simultaneous root and argument shift. -/
theorem spectralShiftRoots_coordinate {d : ℕ} (w : Nat.Primes → Fin d → ℂ) (A : ℝ)
    (p : Nat.Primes) (i : Fin d) (s : ℂ) :
    spectralShiftRoots w A p i * (((p : ℕ) : ℂ) ^ (-(s - (A : ℂ)))) =
      w p i * (((p : ℕ) : ℂ) ^ (-s)) := by
  rw [spectralShiftRoots, mul_assoc, ← Complex.cpow_add _ _ (by exact_mod_cast p.property.ne_zero)]
  congr 2
  ring

/-- A polynomial prime bound becomes an actual unit bound after the exact spectral shift. -/
theorem norm_spectralShiftRoots_le_one {d : ℕ} {w : Nat.Primes → Fin d → ℂ} {A : ℝ}
    (hw : ∀ p i, ‖w p i‖ ≤ ((p : ℕ) : ℝ) ^ A) (p : Nat.Primes) (i : Fin d) :
    ‖spectralShiftRoots w A p i‖ ≤ 1 := by
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  rw [spectralShiftRoots, norm_mul, Complex.norm_natCast_cpow_of_pos p.property.pos,
    Complex.neg_re, Complex.ofReal_re]
  calc
    _ ≤ ((p : ℕ) : ℝ) ^ A * ((p : ℕ) : ℝ) ^ (-A) := mul_le_mul_of_nonneg_right (hw p i) (by positivity)
    _ = 1 := by rw [← Real.rpow_add hp0, add_neg_cancel, Real.rpow_zero]

/-- The literal infinite spectral denominator is invariant under the exact shift. -/
theorem spectralGlobalDenominator_shift {d : ℕ} (w : Nat.Primes → Fin d → ℂ) (A : ℝ) (s : ℂ) :
    spectralGlobalDenominator w s = spectralGlobalDenominator (spectralShiftRoots w A) (s - (A : ℂ)) := by
  unfold spectralGlobalDenominator
  congr 1
  funext v
  rw [spectralShiftRoots_coordinate]

/-- The actual reciprocal spectral Euler function has the same exact shift identity. -/
theorem spectralGlobalLSeries_shift {d : ℕ} (w : Nat.Primes → Fin d → ℂ) (A : ℝ) (s : ℂ) :
    spectralGlobalLSeries w s = spectralGlobalLSeries (spectralShiftRoots w A) (s - (A : ℂ)) := by
  rw [spectralGlobalLSeries, spectralGlobalLSeries, spectralGlobalDenominator_shift w A]

/-- Every genuine prime Euler factor obeys the exact spectral shift. -/
theorem primeSpectralEulerFactor_shift {d : ℕ} (w : Nat.Primes → Fin d → ℂ) (A : ℝ)
    (p : Nat.Primes) (s : ℂ) :
    primeSpectralEulerFactor w p s = primeSpectralEulerFactor (spectralShiftRoots w A) p (s - (A : ℂ)) := by
  simp only [primeSpectralEulerFactor, spectralShiftRoots_coordinate]

/-- The genuine unscaled spectral function is nonzero in the far Euler half-plane under a proved polynomial prime bound. -/
theorem spectralGlobalLSeries_ne_zero_of_prime_bound {d : ℕ} {w : Nat.Primes → Fin d → ℂ} {A : ℝ}
    (hw : ∀ p i, ‖w p i‖ ≤ ((p : ℕ) : ℝ) ^ A) {s : ℂ} (hs : A + 1 < s.re) :
    spectralGlobalLSeries w s ≠ 0 := by
  rw [spectralGlobalLSeries_shift w A]
  apply spectralGlobalLSeries_ne_zero (norm_spectralShiftRoots_le_one hw)
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

/-- The original spectral Euler product genuinely converges over primes in its far half-plane. -/
theorem spectralGlobalLSeries_hasProd_of_prime_bound {d : ℕ} {w : Nat.Primes → Fin d → ℂ} {A : ℝ}
    (hw : ∀ p i, ‖w p i‖ ≤ ((p : ℕ) : ℝ) ^ A) {s : ℂ} (hs : A + 1 < s.re) :
    HasProd (fun p : Nat.Primes => primeSpectralEulerFactor w p s) (spectralGlobalLSeries w s) := by
  rw [spectralGlobalLSeries_shift w A]
  have hh := spectralGlobalLSeries_hasProd (norm_spectralShiftRoots_le_one hw)
    (s := s - (A : ℂ)) (by simp only [Complex.sub_re, Complex.ofReal_re]; linarith)
  simpa only [← primeSpectralEulerFactor_shift] using hh

/-- The original spectral Euler function is holomorphic in the same genuine far half-plane. -/
theorem spectralGlobalLSeries_differentiableAt_of_prime_bound {d : ℕ}
    {w : Nat.Primes → Fin d → ℂ} {A : ℝ}
    (hw : ∀ p i, ‖w p i‖ ≤ ((p : ℕ) : ℝ) ^ A) {s : ℂ} (hs : A + 1 < s.re) :
    DifferentiableAt ℂ (spectralGlobalLSeries w) s := by
  have hs' : 1 < (s - (A : ℂ)).re := by simp only [Complex.sub_re, Complex.ofReal_re]; linarith
  have hd : DifferentiableAt ℂ (spectralGlobalLSeries (spectralShiftRoots w A)) (s - (A : ℂ)) :=
    (spectralGlobalDenominator_differentiableAt (norm_spectralShiftRoots_le_one hw) hs').inv
      (spectralGlobalDenominator_ne_zero (norm_spectralShiftRoots_le_one hw) hs')
  have he : spectralGlobalLSeries w = fun z => spectralGlobalLSeries (spectralShiftRoots w A) (z - (A : ℂ)) :=
    funext (spectralGlobalLSeries_shift w A)
  rw [he]
  exact DifferentiableAt.comp (f := fun z : ℂ => z - (A : ℂ))
    (g := spectralGlobalLSeries (spectralShiftRoots w A)) s hd
    (differentiableAt_id.sub_const (A : ℂ))

end
end Dubon2026
