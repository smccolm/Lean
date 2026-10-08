import Dubon2026.PrimitiveSquareEulerProduct
import Dubon2026.Gamma0PrincipalFactor

/-! # Exact finite ramified removal from the actual Rankin square Euler product -/

namespace Dubon2026

noncomputable section

/-- The literal finite ramified correction for the actual normalized coefficient square series. -/
def primitiveRankinBadCorrection {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (s : ℂ) : ℂ :=
  ∏ p ∈ ramifiedPrimeSet Q,
    (1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s)))

/-- The finite Rankin correction has exactly the original ramified square-coefficient Euler denominators. -/
theorem primitive_rankin_bad_correction_hasProd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (s : ℂ) :
    HasProd (fun p : Nat.Primes => if (p : ℕ) ∣ Q then
      (1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s))) else 1)
      (primitiveRankinBadCorrection f s) := by
  have he : HasProd (fun p : Nat.Primes => if (p : ℕ) ∣ Q then
      (1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s))) else 1)
      (∏ p ∈ ramifiedPrimeSet Q, if (p : ℕ) ∣ Q then
        (1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s))) else 1) := by
    apply hasProd_prod_of_ne_finset_one
    intro p hp
    rw [if_neg (fun h => hp ((mem_ramifiedPrimeSet (Nat.pos_of_neZero Q) p).mpr h))]
  convert he using 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [if_pos ((mem_ramifiedPrimeSet (Nat.pos_of_neZero Q) p).mp hp)]

/-- Multiplying the genuine square Euler product by its finite ramified correction removes exactly those local factors. -/
theorem primitive_unramified_square_euler_hasProd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => if (p : ℕ) ∣ Q then 1 else
      ∑' r : ℕ, primitiveSquareLocalTerm f p s r)
      (cuspRankinSeries f.toCuspForm s * primitiveRankinBadCorrection f s) := by
  have he := (primitive_square_lseries_euler_hasProd f hk hs).mul
    (primitive_rankin_bad_correction_hasProd f s)
  have hid : (fun p : Nat.Primes => (∑' r : ℕ, primitiveSquareLocalTerm f p s r) *
      (if (p : ℕ) ∣ Q then
        1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s)) else 1)) =
      (fun p : Nat.Primes => if (p : ℕ) ∣ Q then 1 else ∑' r : ℕ, primitiveSquareLocalTerm f p s r) := by
    funext p
    by_cases hpQ : (p : ℕ) ∣ Q
    · rw [if_pos hpQ, if_pos hpQ, primitive_bad_square_euler_series f hk p.property hpQ hs,
        inv_mul_cancel₀ (primitive_bad_square_denominator_ne_zero f hk p.property hpQ hs)]
    · rw [if_neg hpQ, if_neg hpQ, mul_one]
  change HasProd (fun p : Nat.Primes => (∑' r : ℕ, primitiveSquareLocalTerm f p s r) *
      (if (p : ℕ) ∣ Q then
        1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s)) else 1)) _ at he
  rwa [hid] at he

/-- The actual principal-character L-function has precisely the Euler factors at primes not dividing its modulus. -/
theorem principal_incomplete_euler_hasProd (Q : ℕ) [NeZero Q] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => if (p : ℕ) ∣ Q then 1 else
      (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹) (DirichletCharacter.LFunctionTrivChar Q s) := by
  have he := DirichletCharacter.LSeries_eulerProduct_hasProd (1 : DirichletCharacter ℂ Q) hs
  rw [← DirichletCharacter.LFunction_eq_LSeries _ hs] at he
  convert he using 1
  funext p
  rw [principalCharacter_nat_indicator]
  by_cases hpQ : (p : ℕ) ∣ Q <;> simp [p.property.coprime_iff_not_dvd, hpQ]

/-- Every actual finite Rankin ramified correction is entire. -/
theorem primitiveRankinBadCorrection_differentiable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) : Differentiable ℂ (primitiveRankinBadCorrection f) := by
  intro s
  apply DifferentiableAt.fun_finsetProd
  intro p _
  exact ((primeDirichletCoordinate_differentiable p).differentiableAt.const_mul
    ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ)).const_sub 1

end
end Dubon2026
