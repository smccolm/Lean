import Dubon2026.HeckeGoodAdjoint

/-! # Reality of actual primitive cusp-form coefficients away from the level -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

noncomputable section

/-- Positive definiteness makes the genuine normalized primitive form have nonzero Petersson norm. -/
theorem primitiveCuspForm_petersson_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) : cuspPetersson f.toCuspForm f.toCuspForm ≠ 0 :=
  fun h => primitiveCuspForm_ne_zero f (cuspPetersson_definite f.toCuspForm h)

/-- Every actual classical Fourier coefficient at a good index is fixed by conjugation. -/
theorem primitiveCuspForm_coefficient_conj {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (n : ℕ) (hnQ : Nat.Coprime n Q) :
    starRingEnd ℂ (cuspCoefficients f.toCuspForm n) = cuspCoefficients f.toCuspForm n := by
  by_cases hn : n = 0
  · subst hn
    simp [cuspCoefficients_zero]
  · have he := primitiveCuspForm_eigenvector f (Nat.pos_of_ne_zero hn) hnQ
    have h := cuspHeckeLinear_coprime_selfAdjoint Q k n hnQ f.toCuspForm f.toCuspForm
    rw [he, cuspPetersson_conj_smul_left, cuspPetersson_smul_right] at h
    exact mul_right_cancel₀ (primitiveCuspForm_petersson_ne_zero f) h

/-- The genuine classical good-index coefficients are real. -/
theorem primitiveCuspForm_coefficient_im {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (n : ℕ) (hnQ : Nat.Coprime n Q) :
    (cuspCoefficients f.toCuspForm n).im = 0 :=
  Complex.conj_eq_iff_im.mp (primitiveCuspForm_coefficient_conj f n hnQ)

/-- The actual positive-real coefficient normalization preserves good-index reality. -/
theorem primitiveCuspForm_normalizedCoefficient_conj {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (n : ℕ) (hnQ : Nat.Coprime n Q) :
    starRingEnd ℂ (normalizedCuspCoefficients f.toCuspForm n) =
      normalizedCuspCoefficients f.toCuspForm n := by
  rw [normalizedCuspCoefficients, shiftedCoefficients,
    ← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
  rw [map_mul, primitiveCuspForm_coefficient_conj f n hnQ, Complex.conj_ofReal]

/-- The exact unramified-prime reality input is proved for the genuine primitive form. -/
theorem primitiveCuspForm_normalizedCoefficient_im {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (n : ℕ) (hnQ : Nat.Coprime n Q) :
    (normalizedCuspCoefficients f.toCuspForm n).im = 0 :=
  Complex.conj_eq_iff_im.mp (primitiveCuspForm_normalizedCoefficient_conj f n hnQ)

/-- At level one every actual normalized primitive coefficient is real. -/
theorem levelOnePrimitive_normalizedCoefficient_im {k : ℤ} (f : PrimitiveCuspForm 1 k) (n : ℕ) :
    (normalizedCuspCoefficients f.toCuspForm n).im = 0 :=
  primitiveCuspForm_normalizedCoefficient_im f n (Nat.coprime_one_right n)

end
end Dubon2026
