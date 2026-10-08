import Dubon2026.PrimitiveAugmentedTensor
import Dubon2026.EulerCoefficientAssembly

/-! # Genuine nonnegative augmented Rankin Dirichlet coefficients -/

namespace Dubon2026

noncomputable section
open scoped ComplexOrder

/-- The actual positive-order augmented tensor power traces satisfy a coarse geometric prime bound. -/
theorem norm_primitiveAugmentedTensor_trace_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) (r : ℕ) (hr : 0 < r) :
    ‖∑ i : Fin 3 × Fin 3, primitiveAugmentedTensorRoots f p i ^ r‖ ≤
      (((p : ℕ) : ℝ) ^ 6) ^ r := by
  have hp2 : 2 ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.property.two_le
  have h9 : (9 : ℝ) ≤ ((p : ℕ) : ℝ) ^ 4 := by
    calc
      9 ≤ (2 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hp2 4
  have hA : 9 * ((p : ℕ) : ℝ) ^ 2 ≤ ((p : ℕ) : ℝ) ^ 6 := by
    calc
      _ ≤ ((p : ℕ) : ℝ) ^ 4 * ((p : ℕ) : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h9 (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∑ i : Fin 3 × Fin 3, ‖primitiveAugmentedTensorRoots f p i ^ r‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3 × Fin 3, (((p : ℕ) : ℝ) ^ 2) ^ r := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (primitiveAugmentedTensor_norm_le_prime_sq f hk p i) r
    _ = 9 * (((p : ℕ) : ℝ) ^ 2) ^ r := by simp
    _ ≤ 9 ^ r * (((p : ℕ) : ℝ) ^ 2) ^ r :=
      mul_le_mul_of_nonneg_right (le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 9) (ne_of_gt hr)) (by positivity)
    _ = (9 * ((p : ℕ) : ℝ) ^ 2) ^ r := by rw [mul_pow]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hA r

/-- The genuine local augmented coefficients have an elementary polynomial prime-power bound. -/
theorem primitiveAugmentedLocalCoeff_norm_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) (r : ℕ) :
    ‖primitiveAugmentedLocalCoeff f p r‖ ≤ (((p : ℕ) : ℝ) ^ r) ^ 6 := by
  have hh := norm_spectralFormalEuler_coeff_le Finset.univ (primitiveAugmentedTensorRoots f p)
    (by positivity : 0 ≤ ((p : ℕ) : ℝ) ^ 6) (norm_primitiveAugmentedTensor_trace_le f hk p) r
  simpa only [primitiveAugmentedLocalCoeff, ← pow_mul, Nat.mul_comm 6 r] using hh

/-- Extend the actual local coefficients to natural indices; nonprime indices have the unit
formal series and never enter a prime factorization. -/
def primitiveAugmentedNatLocalCoeff {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p r : ℕ) : ℂ :=
  if hp : Nat.Prime p then primitiveAugmentedLocalCoeff f ⟨p, hp⟩ r else if r = 0 then 1 else 0

/-- Actual global augmented Rankin coefficients, constructed from the literal finite Euler products. -/
def primitiveAugmentedCoefficient {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) : ℕ → ℂ := assembledEulerCoefficient (primitiveAugmentedNatLocalCoeff f)

/-- Every local constant coefficient used by the actual prime factorization is one. -/
theorem primitiveAugmentedNatLocalCoeff_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : ℕ) : primitiveAugmentedNatLocalCoeff f p 0 = 1 := by
  by_cases hp : Nat.Prime p <;> simp [primitiveAugmentedNatLocalCoeff, hp, primitiveAugmentedLocalCoeff_zero]

/-- Every constructed genuine global augmented coefficient is nonnegative real. -/
theorem primitiveAugmentedCoefficient_nonneg {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (n : ℕ) : 0 ≤ primitiveAugmentedCoefficient f n := by
  apply assembledEulerCoefficient_nonneg
  intro p r
  by_cases hp : Nat.Prime p
  · simpa only [primitiveAugmentedNatLocalCoeff, dif_pos hp] using primitiveAugmentedLocalCoeff_nonneg f ⟨p, hp⟩ r
  · simp only [primitiveAugmentedNatLocalCoeff, dif_neg hp]
    split_ifs
    · exact zero_le_one
    · exact le_rfl

/-- The actual global coefficient at one is exactly one. -/
theorem primitiveAugmentedCoefficient_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) : primitiveAugmentedCoefficient f 1 = 1 := assembledEulerCoefficient_one _

/-- The actual augmented Dirichlet series converges absolutely on Re(s)>7. -/
theorem primitiveAugmentedCoefficient_abscissa_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    LSeries.abscissaOfAbsConv (primitiveAugmentedCoefficient f) ≤ (7 : ℝ) := by
  have hh := assembledEulerCoefficient_abscissa_le (primitiveAugmentedNatLocalCoeff f) 6
    (fun p hp r => by
      simpa only [primitiveAugmentedNatLocalCoeff, dif_pos hp] using primitiveAugmentedLocalCoeff_norm_le f hk ⟨p, hp⟩ r)
  convert hh using 1
  rw [← EReal.coe_one, ← EReal.coe_add]
  norm_num

/-- The genuine global augmented Dirichlet series has exactly its actual finite spectral Euler factors. -/
theorem primitiveAugmentedCoefficient_hasProd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {s : ℂ} (hs : 7 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' r : ℕ,
      primitiveAugmentedLocalCoeff f p r * ((((p : ℕ) : ℂ) ^ (-s)) ^ r))
      (LSeries (primitiveAugmentedCoefficient f) s) := by
  have hsum : LSeriesSummable (primitiveAugmentedCoefficient f) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((primitiveAugmentedCoefficient_abscissa_le f hk).trans_lt (by exact_mod_cast hs))
  have hh := assembledEulerCoefficient_hasProd (primitiveAugmentedNatLocalCoeff f)
    (primitiveAugmentedNatLocalCoeff_zero f) hsum
  convert hh using 1
  funext p
  congr 1
  funext r
  rw [primitiveAugmentedNatLocalCoeff, dif_pos p.property]
  rfl

end
end Dubon2026
