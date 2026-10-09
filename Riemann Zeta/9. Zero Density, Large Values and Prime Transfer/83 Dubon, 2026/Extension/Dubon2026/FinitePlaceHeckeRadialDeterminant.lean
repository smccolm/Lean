import Dubon2026.FinitePlaceHeckeRadialMatrices

/-! # Genuine integrality and exact determinant of every original radial Hecke matrix -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Every actual radial representative is integral in the original local integer ring. -/
theorem finitePlaceHeckeRadialMatrix_integral (N p : ℕ) [NeZero N] [NeZero p]
    (hpN : p.Coprime N) (v : HeightOneSpectrum ℤ) (n : ℕ) (x : Option (ZMod p)) :
    ∀ i j, (finitePlaceHeckeRadialMatrix N p hpN v n x).val i j ∈ v.adicCompletionIntegers ℚ := by
  intro i j
  have hnat (m : ℕ) : (m : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by simp
  cases x with
  | some a =>
    rw [finitePlaceHeckeRadialMatrix_some_val]
    fin_cases i <;> fin_cases j
    · exact hnat p
    · exact (v.adicCompletionIntegers ℚ).toSubring.neg_mem (hnat a.val)
    · simp
    · simpa only [Nat.cast_pow] using hnat (p ^ n)
  | none =>
    rw [finitePlaceHeckeRadialMatrix_none_val]
    fin_cases i <;> fin_cases j
    · exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem (by simp) (by simp)
    · simp
    · exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem (by simp)
        (by simp [← Nat.cast_pow])
    · simp [← Nat.cast_pow]

/-- Each actual original radial representative has determinant exactly the next power of the genuine original prime unit. -/
theorem finitePlaceHeckeRadialMatrix_det (N p : ℕ) [NeZero N] [NeZero p]
    (hpN : p.Coprime N) (v : HeightOneSpectrum ℤ) (n : ℕ) (x : Option (ZMod p)) :
    GeneralLinearGroup.det (finitePlaceHeckeRadialMatrix N p hpN v n x) =
      (finitePlacePrimeUnit p v) ^ (n + 1) := by
  apply Units.ext
  change (finitePlaceHeckeRadialMatrix N p hpN v n x).val.det =
    (finitePlacePrimeUnit p v : v.adicCompletion ℚ) ^ (n + 1)
  rw [finitePlacePrimeUnit_val]
  cases x with
  | some a =>
    rw [finitePlaceHeckeRadialMatrix_some_val]
    simp [Matrix.det_fin_two, pow_succ, mul_comm]
  | none =>
    rw [finitePlaceHeckeRadialMatrix_none_val]
    simp only [Matrix.det_fin_two_of]
    have hb := congrArg (Int.castRingHom (v.adicCompletion ℚ)) (heckePrime_bezout hpN)
    simp only [map_add, map_mul, map_one] at hb
    change ((p : ℤ) : v.adicCompletion ℚ) * (Int.gcdA p N : v.adicCompletion ℚ) +
      ((N : ℤ) : v.adicCompletion ℚ) * (Int.gcdB p N : v.adicCompletion ℚ) = 1 at hb
    push_cast at hb
    linear_combination (p : v.adicCompletion ℚ) ^ (n + 1) * hb

end
end Dubon2026
