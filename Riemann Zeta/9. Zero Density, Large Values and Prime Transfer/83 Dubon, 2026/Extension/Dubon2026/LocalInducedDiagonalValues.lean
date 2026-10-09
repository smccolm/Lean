import Dubon2026.NormalizedLocalPrincipalSeries
import Dubon2026.GL2UnitDiagonalPair

/-! # Literal diagonal values of the original local spherical induced vector -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- The actual two-unit diagonal lies in the original lower Borel. -/
def gl2LowerDiagonalPair {F : Type*} [Field F] (a b : Fˣ) : gl2UpperZeroSubgroup F :=
  ⟨gl2UnitDiagonalPair a b, rfl⟩

/-- The first original diagonal homomorphism recovers the original first unit. -/
theorem gl2LowerDiagonalHom_pair_zero {F : Type*} [Field F] (a b : Fˣ) :
    gl2LowerDiagonalHom 0 (gl2LowerDiagonalPair a b) = a := Units.ext rfl

/-- The second original diagonal homomorphism recovers the original second unit. -/
theorem gl2LowerDiagonalHom_pair_one {F : Type*} [Field F] (a b : Fˣ) :
    gl2LowerDiagonalHom 1 (gl2LowerDiagonalPair a b) = b := Units.ext rfl

/-- A genuine lower unipotent lies in the original lower Borel. -/
def gl2LowerUnipotent {F : Type*} [Field F] (t : F) : gl2UpperZeroSubgroup F :=
  ⟨toGL (ringLowerUnipotent t), rfl⟩

/-- Both original diagonal homomorphisms are one on the genuine lower unipotent. -/
theorem gl2LowerDiagonalHom_unipotent {F : Type*} [Field F] (i : Fin 2) (t : F) :
    gl2LowerDiagonalHom i (gl2LowerUnipotent t) = 1 := by
  apply Units.ext
  fin_cases i <;> rfl

/-- Evaluation of the actual spherical section at every original lower-Borel matrix is exactly its original inducing character. -/
theorem finitePlaceInducedSpherical_lower (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (b : gl2UpperZeroSubgroup (v.adicCompletion ℚ)) :
    (finitePlaceInducedSpherical v z₁ z₂).val b.val = finitePlaceLowerCharacter v z₁ z₂ b := by
  have he := iwasawaInducedSection_mul _ _ (finitePlaceLowerCharacter v z₁ z₂)
    (finitePlaceGL2_iwasawa v) (finitePlaceGL2Gamma0_isOpen 1 v)
    (finitePlaceLowerCharacter_integral v z₁ z₂) b 1
  simpa only [Subgroup.coe_one, mul_one] using he

/-- The genuine spherical section has the exact product of its original two local character values on every original two-unit diagonal. -/
theorem finitePlaceInducedSpherical_diagonal (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (a b : (v.adicCompletion ℚ)ˣ) :
    (finitePlaceInducedSpherical v z₁ z₂).val (gl2UnitDiagonalPair a b) =
      ((finitePlaceUnramifiedCharacter v z₁ a * finitePlaceUnramifiedCharacter v z₂ b : ℂˣ) : ℂ) := by
  have he := finitePlaceInducedSpherical_lower v z₁ z₂ (gl2LowerDiagonalPair a b)
  change (finitePlaceInducedSpherical v z₁ z₂).val (gl2UnitDiagonalPair a b) =
    ((finitePlaceUnramifiedCharacter v z₁ (gl2LowerDiagonalHom 0 (gl2LowerDiagonalPair a b)) *
      finitePlaceUnramifiedCharacter v z₂ (gl2LowerDiagonalHom 1 (gl2LowerDiagonalPair a b)) : ℂˣ) : ℂ) at he
  rw [gl2LowerDiagonalHom_pair_zero, gl2LowerDiagonalHom_pair_one] at he
  exact he

/-- The actual spherical value on the original first inverse-prime diagonal is precisely the inverse first inducing parameter. -/
theorem finitePlaceInducedSpherical_first_inverse_prime (p : ℕ) [NeZero p] (hp : p.Prime)
    (z₁ z₂ : ℂˣ) :
    (finitePlaceInducedSpherical (rationalPrimePlace p hp) z₁ z₂).val
      (gl2UnitDiagonalPair (finitePlacePrimeUnit p (rationalPrimePlace p hp))⁻¹ 1) = (z₁⁻¹ : ℂˣ) := by
  rw [finitePlaceInducedSpherical_diagonal, map_inv, map_one, mul_one,
    finitePlaceUnramifiedCharacter_prime]

/-- The actual spherical value on the original second inverse-prime diagonal is precisely the inverse second inducing parameter. -/
theorem finitePlaceInducedSpherical_second_inverse_prime (p : ℕ) [NeZero p] (hp : p.Prime)
    (z₁ z₂ : ℂˣ) :
    (finitePlaceInducedSpherical (rationalPrimePlace p hp) z₁ z₂).val
      (gl2UnitDiagonalPair 1 (finitePlacePrimeUnit p (rationalPrimePlace p hp))⁻¹) = (z₂⁻¹ : ℂˣ) := by
  rw [finitePlaceInducedSpherical_diagonal, map_inv, map_one, one_mul,
    finitePlaceUnramifiedCharacter_prime]

end
end Dubon2026
