import Dubon2026.HigherAugmentedTensor
import Dubon2026.PrimitiveFirstNonvanishing

/-! # Exact augmented higher tensor Euler identities -/

namespace Dubon2026

noncomputable section

/-- Augmenting an actual finite root system by one gives the exact principal/tensor/square factorization. -/
theorem option_tensor_euler_factor {ι : Type*} [Fintype ι] (u : ι → ℂ) (z : ℂ) :
    (∏ i : Option ι × Option ι, (1 - (i.1.elim 1 u * i.2.elim 1 u) * z)⁻¹) =
      (1 - z)⁻¹ * (∏ i : ι × ι, (1 - (u i.1 * u i.2) * z)⁻¹) *
        (∏ i : ι, (1 - u i * z)⁻¹) ^ 2 := by
  simp only [Fintype.prod_prod_type, Fintype.prod_option, Option.elim_none,
    Option.elim_some, one_mul, mul_one]
  rw [Finset.prod_mul_distrib, pow_two]
  ac_rfl

/-- The genuine augmented higher tensor Euler factor equals the actual principal factor,
even symmetric factors and original symmetric factor squared at every prime. -/
theorem primitiveHigherAugmentedTensor_euler_factor {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (s : ℂ) :
    (∏ i : Option (Fin (r + 1)) × Option (Fin (r + 1)),
      (1 - primitiveHigherAugmentedTensorRoots f r p i * (((p : ℕ) : ℂ) ^ (-s)))⁻¹) =
    principalPrimeEulerFactor Q p s *
      (∏ t ∈ Finset.range (r + 1), primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f (2 * t)) p s) *
        primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f r) p s ^ 2 := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp [primitiveHigherAugmentedTensorRoots, primitiveHigherAugmentedRoots, hpQ,
      principalPrimeEulerFactor, primitiveSymmetricSpectralEulerFactor_bad f _ p hpQ]
  · have he := option_tensor_euler_factor (primitiveSymmetricSpectralRoots f r p) (((p : ℕ) : ℂ) ^ (-s))
    have hh : (∏ i : Option (Fin (r + 1)) × Option (Fin (r + 1)),
        (1 - primitiveHigherAugmentedTensorRoots f r p i * (((p : ℕ) : ℂ) ^ (-s)))⁻¹) =
        (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹ *
          (∏ i : Fin (r + 1) × Fin (r + 1),
            (1 - primitiveHigherTensorRoots f r p i * (((p : ℕ) : ℂ) ^ (-s)))⁻¹) *
          primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f r) p s ^ 2 := by
      simpa only [primitiveHigherAugmentedTensorRoots, primitiveHigherAugmentedRoots, if_neg hpQ,
        primitiveHigherTensorRoots, primeSpectralEulerFactor, Finset.prod_inv_distrib] using he
    rw [hh, primitiveHigherTensor_euler_factor, principalPrimeEulerFactor, if_neg hpQ]

/-- The zeroth actual symmetric Euler function equals the original principal-character L-function. -/
theorem primitiveSymmetric_zero_eq_principal {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    primitiveSymmetricLFunction f 0 s = DirichletCharacter.LFunctionTrivChar Q s := by
  have hh := primitive_higher_symmetric_hasProd_far f hk 0 (s := s) (by simpa using hs)
  apply hh.unique
  have he := principal_incomplete_euler_hasProd Q hs
  convert he using 1
  funext p
  by_cases hpQ : (p : ℕ) ∣ Q <;>
    simp [primeSpectralEulerFactor, primitiveSymmetricSpectralRoots, hpQ]

/-- The literal augmented higher tensor L-series equals the principal factor, all actual even
symmetric Euler functions and the original symmetric Euler function squared. -/
theorem primitiveHigherAugmentedCoefficient_LSeries {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) {s : ℂ}
    (hs : ((2 * r + (r + 2) ^ 2 + 1 : ℕ) : ℝ) + 1 < s.re) :
    LSeries (primitiveHigherAugmentedCoefficient f r) s =
      DirichletCharacter.LFunctionTrivChar Q s *
        (∏ t ∈ Finset.range (r + 1), primitiveSymmetricLFunction f (2 * t) s) *
          primitiveSymmetricLFunction f r s ^ 2 := by
  have hs1 : 1 < s.re := by
    have hn : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    push_cast at hs
    nlinarith [sq_nonneg ((r : ℝ) + 2)]
  have hs2 : (2 * r : ℕ) < s.re := by
    push_cast at hs ⊢
    nlinarith [sq_nonneg ((r : ℝ) + 2)]
  have hsr : (r : ℝ) + 1 < s.re := by
    push_cast at hs
    nlinarith [sq_nonneg ((r : ℝ) + 2), Nat.cast_nonneg (α := ℝ) r]
  have hsum : LSeriesSummable (primitiveHigherAugmentedCoefficient f r) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((primitiveHigherAugmentedCoefficient_abscissa_le f hk r).trans_lt (by exact_mod_cast hs))
  have hEven : HasProd (fun p : Nat.Primes => ∏ t ∈ Finset.range (r + 1),
      primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f (2 * t)) p s)
      (∏ t ∈ Finset.range (r + 1), primitiveSymmetricLFunction f (2 * t) s) := by
    apply hasProd_prod
    intro t ht
    apply primitive_higher_symmetric_hasProd_far f hk (2 * t)
    have ht' : t ≤ r := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ht
    have htR : (t : ℝ) ≤ r := by exact_mod_cast ht'
    push_cast at hs ⊢
    nlinarith [sq_nonneg ((r : ℝ) + 2)]
  have hh := ((principal_incomplete_euler_hasProd Q hs1).mul hEven).mul
    ((primitive_higher_symmetric_hasProd_far f hk r hsr).pow 2)
  apply (spectralDirichletCoefficient_hasProd (primitiveHigherAugmentedTensorRoots f r) hsum).unique
  convert hh using 1
  funext p
  rw [(spectralFormalEuler_evaluation Finset.univ (primitiveHigherAugmentedTensorRoots f r p)
    (((p : ℕ) : ℂ) ^ (-s)) (fun i _ => spectral_prime_coordinate_lt_one _ (2 * r)
      (primitiveHigherAugmentedTensor_norm_le f hk r) p i hs2)).2.tsum_eq]
  exact primitiveHigherAugmentedTensor_euler_factor f r p s

end
end Dubon2026
