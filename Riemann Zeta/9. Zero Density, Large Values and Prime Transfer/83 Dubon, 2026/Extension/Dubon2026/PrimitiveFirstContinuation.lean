import Dubon2026.CuspEntireLFunction
import Dubon2026.RankinSpectralTraces

/-! # The explicit entire first symmetric continuation and its genuine trivial zero -/

namespace Dubon2026

noncomputable section

/-- The actual first symmetric continuation is the original entire cusp L-function times precisely its finite ramified denominators. -/
def primitiveFirstContinuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (s : ℂ) : ℂ :=
  normalizedCuspLFunction f.toCuspForm s *
    ∏ p ∈ ramifiedPrimeSet Q, primitiveEulerDenominator f p s

/-- The explicit actual first symmetric continuation is entire. -/
theorem primitiveFirstContinuation_differentiable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) :
    Differentiable ℂ (primitiveFirstContinuation f) :=
  (normalizedCuspLFunction_differentiable f.toCuspForm hk).mul
    (fun _ => DifferentiableAt.fun_finsetProd (fun p _ => primitiveEulerDenominator_differentiable f p _))

/-- The constructed entire function agrees with the genuine first symmetric Euler product. -/
theorem primitiveFirstContinuation_eq_symmetric {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    primitiveFirstContinuation f s = primitiveSymmetricLFunction f 1 s := by
  rw [primitiveFirstContinuation, normalizedCuspLFunction_eq_series f.toCuspForm hk hs,
    primitive_first_symmetric_eq_cusp_lseries f hk hs]

/-- The original cusp Mellin normalization gives its genuine trivial zero when the Gamma argument is zero. -/
theorem normalizedCuspLFunction_trivial_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    normalizedCuspLFunction f (((1 - (k : ℝ)) / 2 : ℝ) : ℂ) = 0 := by
  have hz : (((1 - (k : ℝ)) / 2 : ℝ) : ℂ) + ((k : ℂ) - 1) / 2 = 0 := by
    push_cast
    ring
  rw [normalizedCuspLFunction, hz, Complex.Gamma_zero, inv_zero, mul_zero, zero_mul]

/-- The actual finite ramified correction preserves the true first symmetric trivial zero. -/
theorem primitiveFirstContinuation_trivial_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) :
    primitiveFirstContinuation f (((1 - (k : ℝ)) / 2 : ℝ) : ℂ) = 0 := by
  rw [primitiveFirstContinuation, normalizedCuspLFunction_trivial_zero, zero_mul]

/-- Every power trace of the actual first symmetric roots at a good prime is the real Hecke root power sum. -/
theorem primitive_first_spectral_power_trace_good {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (hpQ : ¬(p : ℕ) ∣ Q) (r : ℕ) :
    ∑ i : Fin 2, primitiveSymmetricSpectralRoots f 1 p i ^ r =
      primitiveSatakePlus f p ^ r + primitiveSatakeMinus f p ^ r := by
  rw [Fin.sum_univ_two]
  norm_num [primitiveSymmetricSpectralRoots, hpQ, add_comm]

end
end Dubon2026
