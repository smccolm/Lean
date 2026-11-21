import Dubon2026.RankinBoundaryNonvanishing
import Dubon2026.SatoTatePrimeBlocks
import Dubon2026.SpectralEulerShift
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace Dubon2026
open Filter Set Polynomial
open scoped Topology
noncomputable section

theorem primitive_second_character_at_good {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : p.Prime) (hgood : ¬p ∣ Q) :
    primitivePrimeCharacter f 2 p = ‖normalizedCuspCoefficients f.toCuspForm p‖^2 - 1 := by
  rw [norm_eq_abs_re_of_im_zero (primitiveCuspForm_normalizedCoefficient_im f p
    (hp.coprime_iff_not_dvd.mpr hgood)), sq_abs]
  simp [primitivePrimeCharacter, hgood, primitiveCuspForm_normalized_primePower_re f hp hgood, Chebyshev.S_two]

theorem primitive_second_prime_series_summable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (primeLogCoefficients (primitivePrimeCharacter f 2) n : ℂ)) s := by
  classical
  let a := normalizedCuspCoefficients f.toCuspForm
  let u := fun n : ℕ => if n.Prime then (primitivePrimeCharacter f 2 n : ℂ) else 0
  let t : ℝ := (1+s.re)/2
  have ht : 1 < t := by dsimp [t]; linarith
  have hs0 := normalized_cusp_square_lseries_summable f.toCuspForm (by omega : 0 ≤ k)
    (s := (t : ℂ)) (by simpa using ht)
  have hz := LSeriesSummable_of_bounded_of_one_lt_re (f := fun _ => (1 : ℂ))
    (m := 1) (fun _ _ => by simp) (s := (t : ℂ)) (by simpa using ht)
  have hu : LSeriesSummable u (t : ℂ) := by
    apply Summable.of_norm
    apply ((hs0.add hz).norm).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    apply LSeries.norm_term_le
    change ‖u n‖ ≤ ‖((‖a n‖^2 : ℝ) : ℂ) + 1‖
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ ‖a n‖^2 + 1)]
    by_cases hp : n.Prime
    · by_cases hq : n ∣ Q
      · simp [u, hp, primitivePrimeCharacter, hq]; positivity
      · rw [show u n = ((‖a n‖^2 - 1 : ℝ) : ℂ) by simp [u, hp, primitive_second_character_at_good f hp hq, a],
          Complex.norm_real, Real.norm_eq_abs]
        apply abs_le.mpr
        constructor <;> nlinarith [sq_nonneg ‖a n‖]
    · simp [u, hp]; positivity
  have hl : LSeries.abscissaOfAbsConv u < s.re :=
    hu.abscissaOfAbsConv_le.trans_lt (by
      exact_mod_cast (show t < s.re by dsimp [t]; linarith))
  have hlog := LSeriesSummable_logMul_of_lt_re hl
  have he : (fun n => (primeLogCoefficients (primitivePrimeCharacter f 2) n : ℂ)) = LSeries.logMul u := by
    funext n
    by_cases hp : n.Prime
    · simp [primeLogCoefficients, hp, LSeries.logMul, u, Complex.ofReal_log (Nat.cast_nonneg n), mul_comm]
    · simp [primeLogCoefficients, hp, LSeries.logMul, u]
  rwa [he]

theorem primitive_second_logDeriv_far {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (hg : ∀ p i, ‖primitiveSymmetricSpectralRoots f 2 p i‖ ≤ ((p : ℕ) : ℝ)^(3/5 : ℝ))
    {s : ℂ} (hs : 2 < s.re) :
    -logDeriv (primitiveSymmetricLFunction f 2) s =
      LSeries (fun n => (primeLogCoefficients (primitivePrimeCharacter f 2) n : ℂ)) s +
      primeSpectralTail (primitiveSymmetricSpectralRoots f 2) s := by
  let w := primitiveSymmetricSpectralRoots f 2
  let A : ℝ := 3/5
  let v := spectralShiftRoots w A
  have hv := norm_spectralShiftRoots_le_one hg
  have ht : 1 < (s - (A : ℂ)).re := by simp only [Complex.sub_re, Complex.ofReal_re, A]; linarith
  have hfun : primitiveSymmetricLFunction f 2 = fun z => spectralGlobalLSeries v (z - (A : ℂ)) :=
    funext (spectralGlobalLSeries_shift w A)
  have hlog : -logDeriv (primitiveSymmetricLFunction f 2) s = -logDeriv (spectralGlobalLSeries v) (s-A) := by
    rw [hfun]; simp only [logDeriv_apply, deriv_comp_sub_const]
  have h1 (p : Nat.Primes) : primeSpectralFirstTerm v p (s-A) = primeSpectralFirstTerm w p s := by
    simp only [primeSpectralFirstTerm, mul_assoc, Finset.sum_mul, v, spectralShiftRoots_coordinate]
  have h2 (p : Nat.Primes) : primeSpectralTailTerm v p (s-A) = primeSpectralTailTerm w p s := by
    simp only [primeSpectralTailTerm, spectralEulerTail, v, spectralShiftRoots_coordinate]
  have hfirst : Summable (fun p : Nat.Primes => primeSpectralFirstTerm w p s) := by
    have h := (primitive_second_prime_series_summable f hk (by linarith : 1 < s.re)).comp_injective
      (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p : ℕ)))
    exact h.congr fun p => (primitiveSymmetricSpectralFirstTerm_lseries f 2 p s).symm
  have htail := (summable_norm_primeSpectralTailTerm hv (show 1/2 < (s-(A:ℂ)).re by linarith)).of_norm
  rw [hlog, spectralGlobalLSeries_logDeriv_eq_local hv ht]
  simp_rw [primeSpectralEulerFactor_logDeriv hv _ (show 0 < (s-(A:ℂ)).re by linarith)]
  change (∑' p : Nat.Primes, (primeSpectralFirstTerm v p (s-A) + primeSpectralTailTerm v p (s-A))) = _
  simp_rw [h1, h2]
  rw [hfirst.tsum_add (htail.congr h2), tsum_primitiveSymmetricSpectralFirstTerm]
  rfl

end
end Dubon2026
