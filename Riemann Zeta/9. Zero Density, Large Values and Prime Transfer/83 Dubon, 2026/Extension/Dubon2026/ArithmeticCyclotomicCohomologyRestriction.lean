import Dubon2026.ArithmeticTraceZeroCohomologyCup
import Dubon2026.ArithmeticTraceZeroCyclotomicDuality
import Dubon2026.ContinuousAdjointRestrictionComparison

/-! # Actual prime-local cyclotomic restriction of the original arithmetic cohomology -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k] [TopologicalSpace k]
  (a : 𝓞 ℚ) (n : ℕ) [NeZero n] [CharP k n] (hna : (n : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)

/-- The actual arithmetic character representation restricts to the genuine
prime-completion character representation, using the proved original character
identity. The prime is arbitrary relative to the coefficient characteristic. -/
theorem rationalArithmeticCyclotomicRepresentation_restriction :
    (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom).ρ.comp
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom =
      (coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp n k).toMonoidHom).ρ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  change rationalArithmeticCyclotomicCoefficientCharacter a n hna k
      (rationalPrimeArithmeticRestriction a p hp g) * x =
    rationalPrimeCyclotomicCoefficientCharacter p hp n k g * x
  exact congrArg (fun t => t * x) (DFunLike.congr_fun
    (rationalArithmeticCyclotomicCoefficientCharacter_restriction a n hna p hp k) g)

variable [IsTopologicalRing k]
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι k) (hσ : Continuous σ)

/-- Restrict the original arithmetic cyclotomic adjoint H1 to the actual
prime-local cyclotomic adjoint H1. Both characters and the restricting Galois
homomorphism are the previously constructed original objects. -/
def rationalPrimeCyclotomicAdjointH1Restriction :
    let χG := rationalArithmeticCyclotomicCoefficientCharacter a n hna k
    let χP := rationalPrimeCyclotomicCoefficientCharacter p hp n k
    let j := rationalPrimeArithmeticRestriction a p hp
    ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ χG.toMonoidHom)
        (matrixTraceZeroCharacterAction_continuous σ hσ χG.toMonoidHom χG.continuous) →ₗ[k]
      ContinuousRepresentationH1
        (matrixTraceZeroCharacterRep (σ.comp j.toMonoidHom) χP.toMonoidHom)
        (matrixTraceZeroCharacterAction_continuous (σ.comp j.toMonoidHom)
          (hσ.comp j.continuous) χP.toMonoidHom χP.continuous) :=
  let χG := rationalArithmeticCyclotomicCoefficientCharacter a n hna k
  let χP := rationalPrimeCyclotomicCoefficientCharacter p hp n k
  let j := rationalPrimeArithmeticRestriction a p hp
  (continuousH1CoefficientCongr
    (rationalArithmeticTraceZeroCyclotomicTwist_restriction a n hna σ p hp)
    (restrictedCoefficientAction_continuous (matrixTraceZeroCharacterRep σ χG.toMonoidHom)
      j.toMonoidHom j.continuous
      (matrixTraceZeroCharacterAction_continuous σ hσ χG.toMonoidHom χG.continuous))
    (matrixTraceZeroCharacterAction_continuous (σ.comp j.toMonoidHom)
      (hσ.comp j.continuous) χP.toMonoidHom χP.continuous)).toLinearMap.comp
        (continuousRepresentationH1Restriction (matrixTraceZeroCharacterRep σ χG.toMonoidHom)
          (matrixTraceZeroCharacterAction_continuous σ hσ χG.toMonoidHom χG.continuous)
          j.toMonoidHom j.continuous)

/-- The arithmetic twisted H1 restriction retains the exact original restricted
cocycle, transported through the proved full prime-local action identity. -/
theorem rationalPrimeCyclotomicAdjointH1Restriction_mk
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom)) :
    rationalPrimeCyclotomicAdjointH1Restriction a n hna p hp σ hσ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk
        (continuousCocycleOneCoefficientCongr
          (rationalArithmeticTraceZeroCyclotomicTwist_restriction a n hna σ p hp)
          (continuousRepresentationCocycleOneRestriction (matrixTraceZeroCharacterRep σ
            (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom)
            (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
            (rationalPrimeArithmeticRestriction a p hp).continuous c)) := by
  exact continuousH1CoefficientCongr_mk
    (rationalArithmeticTraceZeroCyclotomicTwist_restriction a n hna σ p hp) _ _ _

/-- Restrict original arithmetic cyclotomic H2 classes to the actual prime-local
character H2, transporting the same continuous witnesses through the derived
global/local character representation identity. -/
def rationalPrimeCyclotomicH2Restriction :
    let χG := rationalArithmeticCyclotomicCoefficientCharacter a n hna k
    let χP := rationalPrimeCyclotomicCoefficientCharacter p hp n k
    ContinuousRepresentationH2 (coefficientCharacterRep χG.toMonoidHom)
        (coefficientCharacterAction_continuous χG.toMonoidHom χG.continuous) →ₗ[k]
      ContinuousRepresentationH2 (coefficientCharacterRep χP.toMonoidHom)
        (coefficientCharacterAction_continuous χP.toMonoidHom χP.continuous) :=
  let χG := rationalArithmeticCyclotomicCoefficientCharacter a n hna k
  let χP := rationalPrimeCyclotomicCoefficientCharacter p hp n k
  let j := rationalPrimeArithmeticRestriction a p hp
  (continuousH2CoefficientCongr
    (rationalArithmeticCyclotomicRepresentation_restriction a n hna p hp (k := k))
    (restrictedCoefficientAction_continuous (coefficientCharacterRep χG.toMonoidHom)
      j.toMonoidHom j.continuous
      (coefficientCharacterAction_continuous χG.toMonoidHom χG.continuous))
    (coefficientCharacterAction_continuous χP.toMonoidHom χP.continuous)).toLinearMap.comp
      (continuousRepresentationH2Restriction (coefficientCharacterRep χG.toMonoidHom)
        (coefficientCharacterAction_continuous χG.toMonoidHom χG.continuous)
        j.toMonoidHom j.continuous)

/-- The actual prime-local H2 class is represented by the same original
two-cocycle restricted in both arguments and its proved character transport. -/
theorem rationalPrimeCyclotomicH2Restriction_mk
    (c : continuousRepresentationCocyclesTwo (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom)) :
    rationalPrimeCyclotomicH2Restriction a n hna p hp (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk
        (continuousCocycleTwoCoefficientCongr
          (rationalArithmeticCyclotomicRepresentation_restriction a n hna p hp (k := k))
          (continuousRepresentationCocycleTwoRestriction (coefficientCharacterRep
            (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom)
            (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
            (rationalPrimeArithmeticRestriction a p hp).continuous c)) := by
  exact continuousH2CoefficientCongr_mk
    (rationalArithmeticCyclotomicRepresentation_restriction a n hna p hp (k := k)) _ _ _

end
end Dubon2026
