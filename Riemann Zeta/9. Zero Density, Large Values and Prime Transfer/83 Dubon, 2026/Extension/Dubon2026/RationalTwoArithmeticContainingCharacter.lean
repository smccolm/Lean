import Dubon2026.RationalTwoArithmeticContainingRestriction
import Dubon2026.EmbeddedNormalGaloisRestrictionCharacter

/-! # The same conductor-two character on the original global containing field

The actual global embedding transports the power character of the local
cyclotomic automorphism. Independence of the primitive root identifies it
with the canonical root used by the proved local principal character.
This supplies the containing-field character for DUB-17's global product.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

/-- Retain the rational module induced by the original completion algebra. -/
local instance twoPrimaryContainingCharacterPrimeModule :
    Module ℚ (rationalPrimeLocalField 2 Nat.prime_two) := Algebra.toModule

variable (a : 𝓞 ℚ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (n : ℕ) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (n + 1)))
    (σ : Gal(rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1
      (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one /
      rationalPrimeLocalField 2 Nat.prime_two))

/-- The character of the actual global restriction equals the canonical
local character used in the proved conductor-two principal identity. -/
theorem rationalTwoArithmeticContainingRestriction_autToPow :
    hζ.autToPow ℚ (rationalTwoArithmeticContainingRestriction a F n σ) =
      (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive 2 Nat.prime_two n 1 1
        (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one).autToPow
        (rationalPrimeLocalField 2 Nat.prime_two) σ := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1
    (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
  letI : Algebra K C := C.toIntermediateField.algebra'
  letI : Algebra ℚ C := (C.toIntermediateField.restrictScalars ℚ).algebra'
  let j : F →ₐ[ℚ] C := rationalTwoArithmeticContainingEmbedding a F n
  let hμ : IsPrimitiveRoot (j ζ) (2 ^ (n + 1)) := hζ.map_of_injective j.injective
  let hν := rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive
    2 Nat.prime_two n 1 1
    (show (1 : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ).val = (1 : ℕ) from
      by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
  have hfirst := embeddedNormalGaloisRestriction_autToPow ℚ K F C j (2 ^ (n + 1)) hζ σ
  have hsecond : hμ.autToPow K σ = hν.autToPow K σ :=
    (IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter _ K hμ σ).trans
      (IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter _ K hν σ).symm
  exact hfirst.trans hsecond

end
end Dubon2026
