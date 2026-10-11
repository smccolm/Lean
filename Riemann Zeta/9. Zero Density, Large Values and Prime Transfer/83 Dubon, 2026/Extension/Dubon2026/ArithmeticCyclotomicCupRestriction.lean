import Dubon2026.ArithmeticCyclotomicCohomologyRestriction
import Dubon2026.ContinuousCupCoefficientCongr
import Dubon2026.ContinuousCupRestriction

/-! # Actual arithmetic cyclotomic trace cups commute with prime-local restriction -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

section Generic

variable {G H ι k : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χG : G →* k) (hχG : Continuous χG) (χP : H →* k) (hχP : Continuous χP)
  (j : H →* G) (hj : Continuous j)
  (eA : (matrixTraceZeroCharacterRep ρ χG).ρ.comp j =
    (matrixTraceZeroCharacterRep (ρ.comp j) χP).ρ)
  (eC : (coefficientCharacterRep χG).ρ.comp j = (coefficientCharacterRep χP).ρ)

/-- Cup restriction and proved coefficient identities compose before specializing
any of the original groups to arithmetic Galois groups. -/
private theorem traceCup_restriction_transport
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep ρ χG)
      (matrixTraceZeroCharacterAction_continuous ρ hρ χG hχG))
    (y : ContinuousTraceZeroAdjointH1 ρ hρ) :
    continuousH2CoefficientCongr eC
      (restrictedCoefficientAction_continuous (coefficientCharacterRep χG) j hj
        (coefficientCharacterAction_continuous χG hχG))
      (coefficientCharacterAction_continuous χP hχP)
      (continuousRepresentationH2Restriction (coefficientCharacterRep χG)
        (coefficientCharacterAction_continuous χG hχG) j hj
        (matrixTraceZeroCharacterH1Cup ρ hρ χG hχG x y)) =
      matrixTraceZeroCharacterH1Cup (ρ.comp j) (hρ.comp hj) χP hχP
        (continuousH1CoefficientCongr eA
          (restrictedCoefficientAction_continuous (matrixTraceZeroCharacterRep ρ χG) j hj
            (matrixTraceZeroCharacterAction_continuous ρ hρ χG hχG))
          (matrixTraceZeroCharacterAction_continuous (ρ.comp j) (hρ.comp hj) χP hχP)
          (continuousRepresentationH1Restriction (matrixTraceZeroCharacterRep ρ χG)
            (matrixTraceZeroCharacterAction_continuous ρ hρ χG hχG) j hj x))
        (continuousTraceZeroH1Restriction ρ hρ j hj y) := by
  change continuousH2CoefficientCongr
    eC
    (restrictedCoefficientAction_continuous (coefficientCharacterRep χG)
      j hj
      (coefficientCharacterAction_continuous χG hχG))
    (coefficientCharacterAction_continuous χP hχP)
    (continuousRepresentationH2Restriction (coefficientCharacterRep χG)
      (coefficientCharacterAction_continuous χG hχG)
      j hj
      (continuousH1Cup (matrixTraceZeroCharacterRep ρ χG)
        (matrixTraceZeroAdjointRep ρ) (coefficientCharacterRep χG)
        matrixTraceZeroTracePairing
        (matrixTraceZeroTracePairing_character_equivariant ρ χG)
        matrixTraceZeroTracePairing_continuous
        (matrixTraceZeroCharacterAction_continuous ρ hρ χG hχG)
        (matrixTraceZeroAdjointAction_continuous ρ hρ)
        (coefficientCharacterAction_continuous χG hχG) x
        (continuousTraceZeroH1GeneralEquiv ρ hρ y))) = _
  rw [continuousH1Cup_restriction
    (matrixTraceZeroCharacterRep ρ χG) (matrixTraceZeroAdjointRep ρ)
    (coefficientCharacterRep χG) matrixTraceZeroTracePairing
    (matrixTraceZeroTracePairing_character_equivariant ρ χG)
    matrixTraceZeroTracePairing_continuous
    (matrixTraceZeroCharacterAction_continuous ρ hρ χG hχG)
    (matrixTraceZeroAdjointAction_continuous ρ hρ)
    (coefficientCharacterAction_continuous χG hχG)
    j hj x (continuousTraceZeroH1GeneralEquiv ρ hρ y)]
  have he := continuousH1Cup_coefficientCongr
    eA
    (matrixTraceZeroAdjointRepresentation_comp ρ j)
    eC
    matrixTraceZeroTracePairing
    (fun g X Y => matrixTraceZeroTracePairing_character_equivariant ρ χG (j g) X Y)
    (matrixTraceZeroTracePairing_character_equivariant (ρ.comp j) χP)
    matrixTraceZeroTracePairing_continuous
    (restrictedCoefficientAction_continuous (matrixTraceZeroCharacterRep ρ χG)
      j hj
      (matrixTraceZeroCharacterAction_continuous ρ hρ χG hχG))
    (restrictedCoefficientAction_continuous (matrixTraceZeroAdjointRep ρ)
      j hj (matrixTraceZeroAdjointAction_continuous ρ hρ))
    (restrictedCoefficientAction_continuous (coefficientCharacterRep χG)
      j hj
      (coefficientCharacterAction_continuous χG hχG))
    (matrixTraceZeroCharacterAction_continuous (ρ.comp j) (hρ.comp hj)
      χP hχP)
    (matrixTraceZeroAdjointAction_continuous (ρ.comp j) (hρ.comp hj))
    (coefficientCharacterAction_continuous χP hχP)
    (continuousRepresentationH1Restriction (matrixTraceZeroCharacterRep ρ χG)
      (matrixTraceZeroCharacterAction_continuous ρ hρ χG hχG)
      j hj x)
    (continuousRepresentationH1Restriction (matrixTraceZeroAdjointRep ρ)
      (matrixTraceZeroAdjointAction_continuous ρ hρ) j hj
      (continuousTraceZeroH1GeneralEquiv ρ hρ y))
  apply he.trans
  apply congrArg (continuousH1Cup (matrixTraceZeroCharacterRep (ρ.comp j) χP)
    (matrixTraceZeroAdjointRep (ρ.comp j)) (coefficientCharacterRep χP)
    matrixTraceZeroTracePairing
    (matrixTraceZeroTracePairing_character_equivariant (ρ.comp j) χP)
    matrixTraceZeroTracePairing_continuous
    (matrixTraceZeroCharacterAction_continuous (ρ.comp j) (hρ.comp hj) χP hχP)
    (matrixTraceZeroAdjointAction_continuous (ρ.comp j) (hρ.comp hj))
    (coefficientCharacterAction_continuous χP hχP)
    (continuousH1CoefficientCongr eA
      (restrictedCoefficientAction_continuous (matrixTraceZeroCharacterRep ρ χG) j hj
        (matrixTraceZeroCharacterAction_continuous ρ hρ χG hχG))
      (matrixTraceZeroCharacterAction_continuous (ρ.comp j) (hρ.comp hj) χP hχP)
      (continuousRepresentationH1Restriction (matrixTraceZeroCharacterRep ρ χG)
        (matrixTraceZeroCharacterAction_continuous ρ hρ χG hχG) j hj x)))
  exact continuousTraceZeroH1GeneralEquiv_restriction ρ hρ j hj y


end Generic

variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace k] [IsTopologicalRing k]
  (a : 𝓞 ℚ) (n : ℕ) [NeZero n] [CharP k n] (hna : (n : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι k) (hσ : Continuous σ)
  (p : ℕ) (hp : p.Prime)

/-- The actual global arithmetic trace cup restricts to the actual prime-local
trace cup. Both cyclotomic characters, the Galois restriction, the twisted H1
map and the original trace-zero deformation restriction are the original
constructed objects. No invariant map or arithmetic perfectness is assumed. -/
theorem rationalArithmeticTraceZeroH1Cup_prime_restriction
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    let χP := rationalPrimeCyclotomicCoefficientCharacter p hp n k
    let j := rationalPrimeArithmeticRestriction a p hp
    rationalPrimeCyclotomicH2Restriction a n hna p hp
        (rationalArithmeticTraceZeroH1Cup a n hna σ hσ x y) =
      matrixTraceZeroCharacterH1Cup (σ.comp j.toMonoidHom) (hσ.comp j.continuous)
        χP.toMonoidHom χP.continuous
        (rationalPrimeCyclotomicAdjointH1Restriction a n hna p hp σ hσ x)
        (continuousTraceZeroH1Restriction σ hσ j.toMonoidHom j.continuous y) := by
  exact traceCup_restriction_transport σ hσ
    (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom
    (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).continuous
    (rationalPrimeCyclotomicCoefficientCharacter p hp n k).toMonoidHom
    (rationalPrimeCyclotomicCoefficientCharacter p hp n k).continuous
    (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    (rationalPrimeArithmeticRestriction a p hp).continuous
    (rationalArithmeticTraceZeroCyclotomicTwist_restriction a n hna σ p hp)
    (rationalArithmeticCyclotomicRepresentation_restriction a n hna p hp (k := k)) x y

end
end Dubon2026
