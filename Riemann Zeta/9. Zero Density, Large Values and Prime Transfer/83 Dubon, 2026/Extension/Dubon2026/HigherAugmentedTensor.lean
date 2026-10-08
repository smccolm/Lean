import Dubon2026.PrimitiveHigherTensorEuler

/-! # Actual augmented tensor squares for arbitrary symmetric Hecke powers -/

namespace Dubon2026

noncomputable section
open scoped ComplexOrder

/-- Augment the genuine unramified symmetric roots by the trivial root; omit exactly the ramified factors. -/
def primitiveHigherAugmentedRoots {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (i : Option (Fin (r + 1))) : ℂ :=
  if (p : ℕ) ∣ Q then 0 else i.elim 1 (primitiveSymmetricSpectralRoots f r p)

/-- The literal tensor-square roots of the actual augmented symmetric system. -/
def primitiveHigherAugmentedTensorRoots {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes)
    (i : Option (Fin (r + 1)) × Option (Fin (r + 1))) : ℂ :=
  primitiveHigherAugmentedRoots f r p i.1 * primitiveHigherAugmentedRoots f r p i.2

/-- Every genuine augmented symmetric power trace is real. -/
theorem primitiveHigherAugmented_trace_real {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (m : ℕ) :
    (∑ i : Option (Fin (r + 1)), primitiveHigherAugmentedRoots f r p i ^ m).im = 0 := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · cases m <;> simp [primitiveHigherAugmentedRoots, hpQ]
  · simpa only [primitiveHigherAugmentedRoots, if_neg hpQ, Fintype.sum_option,
      Option.elim_none, Option.elim_some, one_pow, Complex.add_im, Complex.one_im, zero_add] using
      primitiveSymmetricSpectral_power_trace_real f r p m

/-- Every power trace of the actual augmented higher tensor is nonnegative real. -/
theorem primitiveHigherAugmentedTensor_trace_nonneg {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (m : ℕ) :
    0 ≤ ∑ i : Option (Fin (r + 1)) × Option (Fin (r + 1)),
      primitiveHigherAugmentedTensorRoots f r p i ^ m := by
  have he : (∑ i : Option (Fin (r + 1)) × Option (Fin (r + 1)),
      primitiveHigherAugmentedTensorRoots f r p i ^ m) =
      (∑ i : Option (Fin (r + 1)), primitiveHigherAugmentedRoots f r p i ^ m) ^ 2 := by
    simp only [primitiveHigherAugmentedTensorRoots, Fintype.sum_prod_type, mul_pow,
      ← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  rw [he, Complex.sq_nonneg_iff]
  exact primitiveHigherAugmented_trace_real f r p m

/-- The actual augmented roots satisfy a proved elementary polynomial prime bound. -/
theorem primitiveHigherAugmented_norm_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) (p : Nat.Primes)
    (i : Option (Fin (r + 1))) : ‖primitiveHigherAugmentedRoots f r p i‖ ≤ ((p : ℕ) : ℝ) ^ r := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp only [primitiveHigherAugmentedRoots, if_pos hpQ, norm_zero]
    positivity
  · rw [primitiveHigherAugmentedRoots, if_neg hpQ]
    cases i with
    | none =>
      simpa using one_le_pow₀ (n := r) (by exact_mod_cast p.property.one_le : (1 : ℝ) ≤ (p : ℕ))
    | some i => exact primitiveSymmetricSpectralRoots_norm_le_prime_pow f hk r p i

/-- The actual augmented tensor roots satisfy the square of the proved prime bound. -/
theorem primitiveHigherAugmentedTensor_norm_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) (p : Nat.Primes)
    (i : Option (Fin (r + 1)) × Option (Fin (r + 1))) :
    ‖primitiveHigherAugmentedTensorRoots f r p i‖ ≤ ((p : ℕ) : ℝ) ^ (2 * r) := by
  rw [primitiveHigherAugmentedTensorRoots, norm_mul, two_mul, pow_add]
  exact mul_le_mul (primitiveHigherAugmented_norm_le f hk r p i.1)
    (primitiveHigherAugmented_norm_le f hk r p i.2) (norm_nonneg _) (by positivity)

/-- Genuine augmented tensor Dirichlet coefficients from the actual finite Euler series. -/
def primitiveHigherAugmentedCoefficient {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) : ℕ → ℂ :=
  spectralDirichletCoefficient (primitiveHigherAugmentedTensorRoots f r)

/-- Every genuine augmented higher tensor coefficient is nonnegative. -/
theorem primitiveHigherAugmentedCoefficient_nonneg {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (n : ℕ) : 0 ≤ primitiveHigherAugmentedCoefficient f r n :=
  spectralDirichletCoefficient_nonneg _ (fun p m _ => primitiveHigherAugmentedTensor_trace_nonneg f r p m) n

/-- The genuine augmented tensor coefficient at one is exactly one. -/
theorem primitiveHigherAugmentedCoefficient_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) : primitiveHigherAugmentedCoefficient f r 1 = 1 :=
  spectralDirichletCoefficient_one _

/-- A concrete finite abscissa for the genuine augmented higher tensor L-series. -/
theorem primitiveHigherAugmentedCoefficient_abscissa_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) :
    LSeries.abscissaOfAbsConv (primitiveHigherAugmentedCoefficient f r) ≤
      ((2 * r + (r + 2) ^ 2 + 1 : ℕ) : ℝ) + 1 := by
  simpa only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, ← pow_two,
    show r + 1 + 1 = r + 2 by omega] using
    spectralDirichletCoefficient_abscissa_le _ (2 * r) (primitiveHigherAugmentedTensor_norm_le f hk r)

end
end Dubon2026
