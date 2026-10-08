import Dubon2026.PrimitiveSymmetricLFunction
import Dubon2026.SpectralEulerHasProd
import Dubon2026.PrimitiveFirstSpectralConvergence

/-! # The first genuine symmetric-power Euler function and the original cusp L-series -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The actual finite set of ramified primes for a positive level, represented in the genuine prime subtype. -/
def ramifiedPrimeSet (Q : ℕ) : Finset Nat.Primes :=
  ((Nat.primesLE Q).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn).filter
    (fun p => (p : ℕ) ∣ Q)

/-- For a positive level, the finite ramified-prime set consists exactly of the primes dividing that level. -/
theorem mem_ramifiedPrimeSet {Q : ℕ} (hQ : 0 < Q) (p : Nat.Primes) :
    p ∈ ramifiedPrimeSet Q ↔ (p : ℕ) ∣ Q := by
  simp only [ramifiedPrimeSet, Finset.mem_filter, Finset.mem_preimage, Nat.mem_primesLE]
  constructor
  · exact fun h => h.2
  · intro hpQ
    exact ⟨⟨Nat.le_of_dvd hQ hpQ, p.property⟩, hpQ⟩

/-- The order-one actual spectral factor is the original normalized cusp Euler factor away from the level and exactly one at omitted primes. -/
theorem primitive_first_symmetric_local_factor {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (s : ℂ) :
    primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 1) p s =
      if (p : ℕ) ∣ Q then 1 else (primitiveEulerDenominator f p s)⁻¹ := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · rw [if_pos hpQ, primitiveSymmetricSpectralEulerFactor_bad f 1 p hpQ]
  · rw [if_neg hpQ, primitiveSymmetricSpectralEulerFactor_good f 1 p hpQ,
      primitiveSymmetricEulerPolynomial, symmetricEulerPolynomial_one_eval,
      (primitiveSatake_trace_det f p).1, (primitiveSatake_trace_det f p).2, one_mul]
    rw [primitiveEulerDenominator, if_neg hpQ]

/-- The actual first-order infinite denominator cannot vanish on Re(s)>1, using cusp convergence instead of Deligne. -/
theorem primitive_first_global_denominator_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    spectralGlobalDenominator (primitiveSymmetricSpectralRoots f 1) s ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable (f := fun v : Nat.Primes × Fin 2 =>
    -(primitiveSymmetricSpectralRoots f 1 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))
  · intro v
    have hl : primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 1) v.1 s ≠ 0 := by
      rw [primitive_first_symmetric_local_factor]
      split
      · exact one_ne_zero
      · exact inv_ne_zero (primitiveEulerDenominator_ne_zero f hk v.1.property hs)
    have hf : (∏ i : Fin 2, (1 - primitiveSymmetricSpectralRoots f 1 v.1 i *
        (((v.1 : ℕ) : ℂ) ^ (-s)))) ≠ 0 := by
      intro hz
      exact hl (by simp only [primeSpectralEulerFactor, hz, inv_zero])
    exact Finset.prod_ne_zero_iff.mp hf v.2 (Finset.mem_univ _)
  · exact summable_norm_primitive_first_spectral f hk hs

/-- The genuine first symmetric-power function is nonzero in its actual convergence half-plane without any unproved local estimate. -/
theorem primitive_first_symmetric_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    primitiveSymmetricLFunction f 1 s ≠ 0 :=
  inv_ne_zero (primitive_first_global_denominator_ne_zero f hk hs)

/-- The genuine first symmetric-power function has the actual cusp Euler factors with only the finite ramified primes omitted, without Deligne. -/
theorem primitive_first_symmetric_hasProd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => if (p : ℕ) ∣ Q then 1 else (primitiveEulerDenominator f p s)⁻¹)
      (primitiveSymmetricLFunction f 1 s) := by
  have hm : Multipliable (fun v : Nat.Primes × Fin 2 =>
      1 - primitiveSymmetricSpectralRoots f 1 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (summable_norm_primitive_first_spectral f hk hs)
  have he := spectralGlobalLSeries_hasProd_of_multipliable hm
    (primitive_first_global_denominator_ne_zero f hk hs)
  simpa only [primitive_first_symmetric_local_factor, primitiveSymmetricLFunction] using he

/-- The finite correction product has precisely the original ramified Euler denominators as its factors. -/
theorem primitive_ramified_correction_hasProd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (s : ℂ) :
    HasProd (fun p : Nat.Primes => if (p : ℕ) ∣ Q then primitiveEulerDenominator f p s else 1)
      (∏ p ∈ ramifiedPrimeSet Q, primitiveEulerDenominator f p s) := by
  have he : HasProd (fun p : Nat.Primes => if (p : ℕ) ∣ Q then primitiveEulerDenominator f p s else 1)
      (∏ p ∈ ramifiedPrimeSet Q, if (p : ℕ) ∣ Q then primitiveEulerDenominator f p s else 1) := by
    apply hasProd_prod_of_ne_finset_one
    intro p hp
    rw [if_neg (fun h => hp ((mem_ramifiedPrimeSet (Nat.pos_of_neZero Q) p).mpr h))]
  convert he using 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [if_pos ((mem_ramifiedPrimeSet (Nat.pos_of_neZero Q) p).mp hp)]

/-- The genuine first symmetric-power Euler function equals the original normalized cusp L-series times exactly its finite ramified Euler denominators. -/
theorem primitive_first_symmetric_eq_cusp_lseries {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k)
    {s : ℂ} (hs : 1 < s.re) :
    primitiveSymmetricLFunction f 1 s = LSeries (normalizedCuspCoefficients f.toCuspForm) s *
      ∏ p ∈ ramifiedPrimeSet Q, primitiveEulerDenominator f p s := by
  have he := (primitive_cusp_lseries_rational_euler_hasProd f hk hs).mul
    (primitive_ramified_correction_hasProd f s)
  have hid : (fun p : Nat.Primes => (primitiveEulerDenominator f p s)⁻¹ *
      (if (p : ℕ) ∣ Q then primitiveEulerDenominator f p s else 1)) =
      (fun p : Nat.Primes => if (p : ℕ) ∣ Q then 1 else (primitiveEulerDenominator f p s)⁻¹) := by
    funext p
    by_cases hpQ : (p : ℕ) ∣ Q
    · rw [if_pos hpQ, if_pos hpQ, inv_mul_cancel₀ (primitiveEulerDenominator_ne_zero f hk p.property hs)]
    · rw [if_neg hpQ, if_neg hpQ, mul_one]
  change HasProd (fun p : Nat.Primes => (primitiveEulerDenominator f p s)⁻¹ *
      (if (p : ℕ) ∣ Q then primitiveEulerDenominator f p s else 1)) _ at he
  rw [hid] at he
  exact (primitive_first_symmetric_hasProd f hk hs).unique he

/-- The original normalized primitive cusp L-series has no zeros on Re(s)>1, proved from its actual roots and convergent Euler product without Deligne. -/
theorem primitive_cusp_lseries_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    LSeries (normalizedCuspCoefficients f.toCuspForm) s ≠ 0 := by
  have hn := primitive_first_symmetric_ne_zero f hk hs
  rw [primitive_first_symmetric_eq_cusp_lseries f hk hs] at hn
  exact (mul_ne_zero_iff.mp hn).1

/-- Each literal primitive Euler denominator is entire in the complex parameter. -/
theorem primitiveEulerDenominator_differentiable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) :
    Differentiable ℂ (primitiveEulerDenominator f p) := by
  have hz := primeDirichletCoordinate_differentiable p
  have hlin := (hz.const_mul (normalizedCuspCoefficients f.toCuspForm p)).const_sub 1
  change Differentiable ℂ (fun s => 1 - normalizedCuspCoefficients f.toCuspForm p *
    (((p : ℕ) : ℂ) ^ (-s)) + if (p : ℕ) ∣ Q then 0 else (((p : ℕ) : ℂ) ^ (-s)) ^ 2)
  by_cases hpQ : (p : ℕ) ∣ Q
  · simpa only [primitiveEulerDenominator, if_pos hpQ, add_zero] using hlin
  · simpa only [primitiveEulerDenominator, if_neg hpQ] using hlin.add (hz.pow 2)

/-- The actual first symmetric-power Euler function is holomorphic on Re(s)>1 without assuming the unproved Deligne bound. -/
theorem primitive_first_symmetric_analyticOnNhd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) :
    AnalyticOnNhd ℂ (primitiveSymmetricLFunction f 1) {s : ℂ | 1 < s.re} := by
  have hc : Differentiable ℂ (fun s : ℂ =>
      ∏ p ∈ ramifiedPrimeSet Q, primitiveEulerDenominator f p s) :=
    fun _ => DifferentiableAt.fun_finsetProd (fun p _ => primitiveEulerDenominator_differentiable f p _)
  have hac : AnalyticOnNhd ℂ (fun s : ℂ =>
      ∏ p ∈ ramifiedPrimeSet Q, primitiveEulerDenominator f p s) {s : ℂ | 1 < s.re} :=
    hc.differentiableOn.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  have hp := (normalized_cusp_lseries_analyticOnNhd f.toCuspForm hk).mul hac
  apply AnalyticOnNhd.congr (isOpen_lt continuous_const Complex.continuous_re) hp
  intro s hs
  exact (primitive_first_symmetric_eq_cusp_lseries f hk hs).symm

end
end Dubon2026
