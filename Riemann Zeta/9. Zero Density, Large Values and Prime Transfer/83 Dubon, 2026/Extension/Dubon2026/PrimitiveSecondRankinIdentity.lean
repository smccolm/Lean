import Dubon2026.PrimitiveSquareIncompleteProduct
import Dubon2026.PrimitiveSecondSymmetricL

/-! # Exact global symmetric-square and Rankin Euler normalization -/

namespace Dubon2026

noncomputable section

/-- The exact cubic recurrence numerator gives the matching quadratic-principal Euler identity. -/
theorem square_euler_factor_identity {D u z : ℂ}
    (hDu : D * u = 1 + z) (hD : D ≠ 0) (hz : 1 - z ≠ 0) (hz2 : 1 - z ^ 2 ≠ 0) :
    D⁻¹ * (1 - z)⁻¹ = u * (1 - z ^ 2)⁻¹ := by
  field_simp [hD, hz, hz2]
  linear_combination -(1 - z) * hDu

/-- The original prime coordinate at 2s is exactly the square of the coordinate at s. -/
theorem primeDirichletCoordinate_two (p : Nat.Primes) (s : ℂ) :
    (((p : ℕ) : ℂ) ^ (-(2 * s))) = ((((p : ℕ) : ℂ) ^ (-s))) ^ 2 := by
  rw [← Complex.cpow_nat_mul]
  congr 1
  ring

/-- The exact genuine good-prime Rankin local identity includes precisely the principal factors at s and 2s. -/
theorem primitive_second_rankin_local_identity {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) (p : Nat.Primes) (hpQ : ¬(p : ℕ) ∣ Q)
    {s : ℂ} (hs : 1 < s.re) :
    primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 2) p s *
      (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹ =
    (∑' r : ℕ, primitiveSquareLocalTerm f p s r) *
      (1 - (((p : ℕ) : ℂ) ^ (-(2 * s))))⁻¹ := by
  rw [primitiveSymmetricSpectralEulerFactor_good f 2 p hpQ, primeDirichletCoordinate_two]
  have hn := norm_primeDirichletCoordinate_le p (by linarith : 0 < s.re) le_rfl
  have hz : 1 - (((p : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
    simpa only [one_mul] using spectralEulerDenominator_ne_zero
      (w := (1 : ℂ)) (by simp) (hn.1.trans_lt hn.2)
  have hnorm2 : ‖((((p : ℕ) : ℂ) ^ (-s))) ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (hn.1.trans_lt hn.2) (by omega)
  have hz2 : 1 - ((((p : ℕ) : ℂ) ^ (-s))) ^ 2 ≠ 0 := by
    simpa only [one_mul] using spectralEulerDenominator_ne_zero (w := (1 : ℂ)) (by simp) hnorm2
  exact square_euler_factor_identity (primitive_good_square_euler_identity f hk p.property hpQ hs)
    (primitive_second_euler_polynomial_ne_zero f hk p hpQ hs) hz hz2

/-- The actual second symmetric-power Euler function and actual Rankin square series satisfy the exact global principal-character identity, including the literal finite ramified correction. -/
theorem primitive_second_rankin_global_identity {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    primitiveSymmetricLFunction f 2 s * DirichletCharacter.LFunctionTrivChar Q s =
      cuspRankinSeries f.toCuspForm s * primitiveRankinBadCorrection f s *
        DirichletCharacter.LFunctionTrivChar Q (2 * s) := by
  have hs2 : 1 < (2 * s).re := by
    norm_num [Complex.mul_re]
    linarith
  have hl := (primitive_second_symmetric_hasProd f hk hs).mul (principal_incomplete_euler_hasProd Q hs)
  have hr := (primitive_unramified_square_euler_hasProd f hk hs).mul (principal_incomplete_euler_hasProd Q hs2)
  have he : (fun p : Nat.Primes =>
      primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 2) p s *
        (if (p : ℕ) ∣ Q then 1 else (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹)) =
      (fun p : Nat.Primes => (if (p : ℕ) ∣ Q then 1 else ∑' r : ℕ, primitiveSquareLocalTerm f p s r) *
        (if (p : ℕ) ∣ Q then 1 else (1 - (((p : ℕ) : ℂ) ^ (-(2 * s))))⁻¹)) := by
    funext p
    by_cases hpQ : (p : ℕ) ∣ Q
    · simp only [if_pos hpQ, primitiveSymmetricSpectralEulerFactor_bad f 2 p hpQ]
    · simp only [if_neg hpQ]
      exact primitive_second_rankin_local_identity f hk p hpQ hs
  change HasProd (fun p : Nat.Primes =>
      primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 2) p s *
        (if (p : ℕ) ∣ Q then 1 else (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹)) _ at hl
  rw [he] at hl
  exact hl.unique hr

end
end Dubon2026
