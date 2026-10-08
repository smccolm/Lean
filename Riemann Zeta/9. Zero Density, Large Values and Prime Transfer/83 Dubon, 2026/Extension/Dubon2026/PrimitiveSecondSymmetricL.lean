import Dubon2026.PrimitiveSquareEulerFactors
import Dubon2026.PrimitiveSecondSpectralConvergence

/-! # Genuine symmetric-square Euler convergence without a Deligne hypothesis -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The genuine prime coordinate has norm below one on every positive half-plane. -/
theorem one_add_primeDirichletCoordinate_ne_zero (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    1 + (((p : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
  have hn := norm_primeDirichletCoordinate_le p hs le_rfl
  intro hz
  have he : (((p : ℕ) : ℂ) ^ (-s)) = -1 := by linear_combination hz
  have hh := hn.1.trans_lt hn.2
  rw [he, norm_neg, norm_one] at hh
  exact lt_irrefl _ hh

/-- Genuine Rankin local convergence proves that the actual good-prime symmetric-square denominator is nonzero on Re(s)>1. -/
theorem primitive_second_euler_polynomial_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) (p : Nat.Primes) (hpQ : ¬(p : ℕ) ∣ Q)
    {s : ℂ} (hs : 1 < s.re) :
    (primitiveSymmetricEulerPolynomial f p 2).eval ((((p : ℕ) : ℂ)) ^ (-s)) ≠ 0 := by
  intro hz
  have he := primitive_good_square_euler_identity f hk p.property hpQ hs
  rw [hz, zero_mul] at he
  exact one_add_primeDirichletCoordinate_ne_zero p (by linarith : 0 < s.re) he.symm

/-- Every actual local symmetric-square Euler factor is nonzero in the genuine convergence region, without purity. -/
theorem primitive_second_local_factor_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) (p : Nat.Primes)
    {s : ℂ} (hs : 1 < s.re) :
    primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 2) p s ≠ 0 := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · rw [primitiveSymmetricSpectralEulerFactor_bad f 2 p hpQ]
    exact one_ne_zero
  · rw [primitiveSymmetricSpectralEulerFactor_good f 2 p hpQ]
    exact inv_ne_zero (primitive_second_euler_polynomial_ne_zero f hk p hpQ hs)

/-- The literal actual symmetric-square infinite denominator is nonzero, using Rankin square convergence and true local factors. -/
theorem primitive_second_global_denominator_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    spectralGlobalDenominator (primitiveSymmetricSpectralRoots f 2) s ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable (f := fun v : Nat.Primes × Fin 3 =>
    -(primitiveSymmetricSpectralRoots f 2 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))
  · intro v
    have hl := primitive_second_local_factor_ne_zero f hk v.1 hs
    have hf : (∏ i : Fin 3, (1 - primitiveSymmetricSpectralRoots f 2 v.1 i *
        (((v.1 : ℕ) : ℂ) ^ (-s)))) ≠ 0 := by
      intro hz
      exact hl (by simp only [primeSpectralEulerFactor, hz, inv_zero])
    exact Finset.prod_ne_zero_iff.mp hf v.2 (Finset.mem_univ _)
  · exact summable_norm_primitive_second_spectral f hk hs

/-- The actual second symmetric-power Euler L-function is nonzero on Re(s)>1 without Deligne. -/
theorem primitive_second_symmetric_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    primitiveSymmetricLFunction f 2 s ≠ 0 :=
  inv_ne_zero (primitive_second_global_denominator_ne_zero f hk hs)

/-- The genuine symmetric-square global function is the actual prime-indexed product of its original local spectral factors. -/
theorem primitive_second_symmetric_hasProd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 2) p s)
      (primitiveSymmetricLFunction f 2 s) := by
  have hm : Multipliable (fun v : Nat.Primes × Fin 3 =>
      1 - primitiveSymmetricSpectralRoots f 2 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (summable_norm_primitive_second_spectral f hk hs)
  exact spectralGlobalLSeries_hasProd_of_multipliable hm
    (primitive_second_global_denominator_ne_zero f hk hs)

end
end Dubon2026
