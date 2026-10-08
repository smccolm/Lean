import Dubon2026.RankinSpectralEuler
import Dubon2026.FiniteSpectralPositivity

/-! # The genuine Rankin Euler product satisfies the three-four-one inequality -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The actual prime coordinate on a vertical line splits into its real radius and its unit phase. -/
theorem prime_cpow_vertical_split (p : Nat.Primes) (σ y : ℝ) :
    (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + Complex.I * y))) =
      ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-(Complex.I * y))) := by
  rw [neg_add, Complex.cpow_add _ _ (by exact_mod_cast p.property.ne_zero),
    Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ))]
  simp only [Complex.ofReal_neg, Complex.ofReal_natCast]

/-- The actual imaginary prime coordinate has unit norm. -/
theorem norm_prime_cpow_imaginary (p : Nat.Primes) (y : ℝ) :
    ‖(((p : ℕ) : ℂ) ^ (-(Complex.I * y)))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.property.pos]
  simp

/-- The genuine Rankin spectral coordinate lies inside the unit disk on Re(s)>3/5. -/
theorem norm_primitiveRankinSpectral_coordinate_lt_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) (i : Fin 4)
    {s : ℂ} (hs : 3 / 5 < s.re) :
    ‖primitiveRankinSpectralRoots f p i * (((p : ℕ) : ℂ) ^ (-s))‖ < 1 := by
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
  calc
    _ ≤ ((p : ℕ) : ℝ) ^ (3 / 5 : ℝ) * ((p : ℕ) : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (primitiveRankinSpectral_norm_le_three_fifths f hk p i)
        (Real.rpow_nonneg hp0.le _)
    _ = ((p : ℕ) : ℝ) ^ (3 / 5 - s.re) := by rw [← Real.rpow_add hp0, sub_eq_add_neg]
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt) (by linarith)

/-- Each genuine Rankin local Euler factor satisfies the exact three-four-one norm inequality. -/
theorem primitive_rankin_local_three_four_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    1 ≤ ‖primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p σ ^ 3 *
      primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p ((σ : ℂ) + Complex.I * y) ^ 4 *
        primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p ((σ : ℂ) + 2 * Complex.I * y)‖ := by
  let a : ℝ := ((p : ℕ) : ℝ) ^ (-σ)
  let z : ℂ := ((p : ℕ) : ℂ) ^ (-(Complex.I * y))
  have ha : (a : ℂ) = (((p : ℕ) : ℂ) ^ (-(σ : ℂ))) := by
    dsimp only [a]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ))]
    simp only [Complex.ofReal_neg, Complex.ofReal_natCast]
  have hz : ‖z‖ = 1 := norm_prime_cpow_imaginary p y
  have h2 : (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * Complex.I * y))) = (a : ℂ) * z ^ 2 := by
    have he := prime_cpow_vertical_split p σ (2 * y)
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at he
    rw [show Complex.I * (2 * (y : ℂ)) = 2 * Complex.I * y by ring] at he
    rw [he]
    congr 1
    dsimp only [z]
    rw [← Complex.cpow_nat_mul]
    congr 1
    ring
  have hh := finiteSpectralEuler_three_four_one (primitiveRankinSpectralRoots f p)
    (a := a) (by dsimp [a]; positivity) (fun i => by
      rw [ha]
      exact norm_primitiveRankinSpectral_coordinate_lt_one f hk p i (by simpa using (show (3 / 5 : ℝ) < σ by linarith)))
    (primitiveRankinSpectral_trace_nonneg f p) hz
  simpa only [primeSpectralEulerFactor, ← ha, prime_cpow_vertical_split p σ y, h2] using hh

/-- Taking the actual convergent prime products preserves the three-four-one inequality for the original Rankin convolution. -/
theorem primitive_rankin_global_three_four_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖rankinConvolutionGlobalContinuation f.toCuspForm (1 + x) ^ 3 *
      rankinConvolutionGlobalContinuation f.toCuspForm (1 + x + Complex.I * y) ^ 4 *
        rankinConvolutionGlobalContinuation f.toCuspForm (1 + x + 2 * Complex.I * y)‖ := by
  have h0 : 1 < (1 + (x : ℂ)).re := by simp; exact hx
  have h1 : 1 < (1 + (x : ℂ) + Complex.I * y).re := by simpa using h0
  have h2 : 1 < (1 + (x : ℂ) + 2 * Complex.I * y).re := by simpa using h0
  have hp0 := primitive_rankin_spectral_hasProd f (by omega) h0
  have hp1 := primitive_rankin_spectral_hasProd f (by omega) h1
  have hp2 := primitive_rankin_spectral_hasProd f (by omega) h2
  change Tendsto _ atTop _ at hp0 hp1 hp2
  have hlim := ((hp0.pow 3).mul (hp1.pow 4)).mul hp2
  apply ge_of_tendsto hlim.norm
  apply Filter.Eventually.of_forall
  intro t
  rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    norm_prod]
  apply Finset.one_le_prod
  intro p _
  simpa only [Complex.ofReal_add, Complex.ofReal_one] using
    primitive_rankin_local_three_four_one f hk p (by linarith : 1 < 1 + x) y

end
end Dubon2026
