import Dubon2026.PrimitiveGaussTwist
import Dubon2026.PrimitiveSelfTwistCoefficients
import Dubon2026.PrincipalDivisorProjection

/-! # Character twists as finite sums of actual principal-level translations -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

/-- The actual finite Gauss-weighted translation operator on principal-level cusp forms. -/
def principalCharacterTwist (N : ℕ) (k : ℤ) {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) :
    CuspForm ((Gamma N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma N).map (mapGL ℝ)) k :=
  (gaussSum χ ZMod.stdAddChar)⁻¹ •
    ∑ a : ZMod D, χ a • principalTranslation N k (a.val * (N / D) : ℕ)

/-- The Fourier phase of an actual integral translation is the standard finite additive character. -/
theorem principalTranslation_character_phase {N D : ℕ} [NeZero N] [NeZero D]
    (hD : D ∣ N) (a : ZMod D) (n : ℕ) :
    Function.Periodic.qParam N (a.val * (N / D) : ℕ) ^ n =
      ZMod.stdAddChar ((n : ZMod D) * a) := by
  simp only [Nat.cast_mul, qParam_nat_mul_eq_pow, qParam_divisor_step hD, ← pow_mul]
  rw [← qParam_nat_mul_eq_pow]
  have hstd : ZMod.stdAddChar ((n : ZMod D) * a) =
      Complex.exp (2 * Real.pi * Complex.I * (n * a.val : ℕ) / D) := by
    calc
      _ = ZMod.stdAddChar (((n * a.val : ℕ) : ℤ) : ZMod D) := by
        rw [Int.cast_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
      _ = Complex.exp (2 * Real.pi * Complex.I * (((n * a.val : ℕ) : ℤ) : ℂ) / D) :=
        ZMod.stdAddChar_coe _
      _ = _ := by rw [Int.cast_natCast]
  rw [hstd, Function.Periodic.qParam]
  congr 1
  push_cast
  ring

/-- A primitive quadratic Gauss-weighted translation sum multiplies each genuine coefficient by χ(n). -/
theorem principalCharacterTwist_coeff {N D : ℕ} [NeZero N] [NeZero D]
    (hD : D ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (n : ℕ) :
    principalCuspCoefficients (principalCharacterTwist N k χ f) n =
      characterCoefficients χ n * principalCuspCoefficients f n := by
  let L := principalCuspCoefficientLinear N k n
  change L (principalCharacterTwist N k χ f) = _
  simp only [principalCharacterTwist, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum]
  change (gaussSum χ ZMod.stdAddChar)⁻¹ *
      (∑ a : ZMod D, χ a * principalCuspCoefficients
        (principalTranslation N k (a.val * (N / D) : ℕ) f) n) = _
  simp only [principalTranslation_coeff, Int.cast_natCast, principalTranslation_character_phase hD]
  calc
    _ = ((gaussSum χ ZMod.stdAddChar)⁻¹ *
        ∑ a : ZMod D, χ a * ZMod.stdAddChar ((n : ZMod D) * a)) *
          principalCuspCoefficients f n := by
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [primitive_quadratic_gauss_inversion χ hχ hq]; rfl

/-- Applying the genuine quadratic twist twice deletes exactly the indices not coprime to its modulus. -/
theorem principalCharacterTwist_twice_coeff {N D : ℕ} [NeZero N] [NeZero D]
    (hD : D ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (n : ℕ) :
    principalCuspCoefficients (principalCharacterTwist N k χ (principalCharacterTwist N k χ f)) n =
      if n.Coprime D then principalCuspCoefficients f n else 0 := by
  rw [principalCharacterTwist_coeff hD k χ hχ hq, principalCharacterTwist_coeff hD k χ hχ hq]
  by_cases hn : n.Coprime D
  · rw [if_pos hn, ← mul_assoc, ← pow_two, quadratic_characterCoefficients_sq χ hq hn, one_mul]
  · rw [if_neg hn, characterCoefficients_of_not_coprime χ hn, zero_mul]

end
end Dubon2026
