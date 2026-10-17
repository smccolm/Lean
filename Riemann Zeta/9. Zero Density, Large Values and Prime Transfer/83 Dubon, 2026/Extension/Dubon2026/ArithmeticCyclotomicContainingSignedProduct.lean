import Dubon2026.ArithmeticCyclotomicContainingAwayRestriction
import Dubon2026.ArithmeticCyclotomicSignedAwayProduct

/-! # The actual signed away-prime product on the full containing field

Every factor comes from original unramified local reciprocity; the real
factor is the existing sign-selected cyclotomic conjugation. No global
cyclicity is imposed on the containing field. The literal restrictions
give the corresponding original cyclic-subfield factors, as required by
DUB-17's conductor-two principal-product comparison.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F]
    (S : Finset (HeightOneSpectrum ℤ))
    (hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ n) (q : ℚˣ)

include hS q

/-- Multiply the original local reciprocity factors on the actual full
cyclotomic containing field, using derived local cyclicity at each prime. -/
def arithmeticCyclotomicContainingAwayProduct : Gal(F/ℚ) := by
  letI : CommGroup Gal(F/ℚ) := rationalCyclotomicGalCommGroup n F
  exact S.attach.prod fun w => arithmeticCyclotomicContainingAwayAut a F
    (Rat.HeightOneSpectrum.natGenerator w.1) (Rat.HeightOneSpectrum.prime_natGenerator w.1)
    n (hS w.1 w.2) q

/-- The character of the literal containing-field product is the existing
explicit normalized away-prime unit product. -/
theorem arithmeticCyclotomicContainingAwayProduct_autToPow
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    hζ.autToPow ℚ (arithmeticCyclotomicContainingAwayProduct a F n S hS q) =
      arithmeticCyclotomicAwayProductUnit n S hS q := by
  letI : CommGroup Gal(F/ℚ) := rationalCyclotomicGalCommGroup n F
  rw [arithmeticCyclotomicContainingAwayProduct, map_prod]
  apply Finset.prod_congr rfl
  intro w _hw
  exact arithmeticCyclotomicContainingAwayAut_autToPow a F
    (Rat.HeightOneSpectrum.natGenerator w.1) (Rat.HeightOneSpectrum.prime_natGenerator w.1)
    n (hS w.1 w.2) q hζ

/-- Multiply the actual sign-selected conjugation and original away-prime
reciprocity factors in the same global containing field. -/
def arithmeticCyclotomicContainingSignedAwayProduct : Gal(F/ℚ) :=
  rationalCyclotomicRealSignAut n F q * arithmeticCyclotomicContainingAwayProduct a F n S hS q

/-- The containing-field signed product has exactly the explicit unit
already cancelled by the proved conductor-two principal character. -/
theorem arithmeticCyclotomicContainingSignedAwayProduct_autToPow
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    hζ.autToPow ℚ (arithmeticCyclotomicContainingSignedAwayProduct a F n S hS q) =
      arithmeticCyclotomicSignedAwayProductUnit n S hS q := by
  rw [arithmeticCyclotomicContainingSignedAwayProduct, map_mul,
    rationalCyclotomicRealSignAut_autToPow n F q hζ,
    arithmeticCyclotomicContainingAwayProduct_autToPow a F n S hS q hζ]
  rfl

variable (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField) [IsCyclic Gal(E/ℚ)]

/-- The restriction of the signed containing-field product consists of
the literal original arithmetic reciprocity factors on the cyclic subfield. -/
theorem arithmeticCyclotomicContainingSignedAwayProduct_restrict :
    letI : CommGroup Gal(E/ℚ) := IsCyclic.commGroup
    let R : Gal(F/ℚ) →* Gal(E/ℚ) :=
      embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
    R (arithmeticCyclotomicContainingSignedAwayProduct a F n S hS q) =
      R (rationalCyclotomicRealSignAut n F q) *
        S.attach.prod (fun w => rationalArithmeticFiniteLocalReciprocityAut a E
          (Rat.HeightOneSpectrum.natGenerator w.1) (Rat.HeightOneSpectrum.prime_natGenerator w.1) q) := by
  letI : CommGroup Gal(F/ℚ) := rationalCyclotomicGalCommGroup n F
  letI : CommGroup Gal(E/ℚ) := IsCyclic.commGroup
  dsimp only
  rw [arithmeticCyclotomicContainingSignedAwayProduct, map_mul,
    arithmeticCyclotomicContainingAwayProduct, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro w _hw
  exact arithmeticCyclotomicContainingAwayAut_restrict a F
    (Rat.HeightOneSpectrum.natGenerator w.1) (Rat.HeightOneSpectrum.prime_natGenerator w.1)
    n (hS w.1 w.2) q E hEF

end
end Dubon2026
