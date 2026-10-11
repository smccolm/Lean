import Dubon2026.TraceZeroCharacterCohomologyCup
import Dubon2026.ArithmeticCyclotomicCoefficientCharacter

/-! # The actual arithmetic cyclotomic cup on original trace-zero deformation cohomology -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace k] [IsTopologicalRing k]
  (a : 𝓞 ℚ) (n : ℕ) [NeZero n] [CharP k n] (hna : (n : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι k) (hσ : Continuous σ)

/-- Construct the arithmetic cup using the derived actual cyclotomic character
and its proved continuity, with the original trace-zero deformation H1 as input.
No arithmetic invariant map or cohomological perfectness is assumed. -/
def rationalArithmeticTraceZeroH1Cup :
    let χ := rationalArithmeticCyclotomicCoefficientCharacter a n hna k
    ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ χ.toMonoidHom)
        (matrixTraceZeroCharacterAction_continuous σ hσ χ.toMonoidHom χ.continuous) →ₗ[k]
      ContinuousTraceZeroAdjointH1 σ hσ →ₗ[k]
        ContinuousRepresentationH2 (coefficientCharacterRep χ.toMonoidHom)
          (coefficientCharacterAction_continuous χ.toMonoidHom χ.continuous) :=
  let χ := rationalArithmeticCyclotomicCoefficientCharacter a n hna k
  matrixTraceZeroCharacterH1Cup σ hσ χ.toMonoidHom χ.continuous

/-- The actual arithmetic pairing preserves the original representatives and the
literal trace cup cocycle with the genuinely constructed cyclotomic coefficient action. -/
theorem rationalArithmeticTraceZeroH1Cup_mk
    (f : continuousRepresentationCocyclesOne
      (matrixTraceZeroCharacterRep σ
        (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom))
    (u : continuousTraceZeroAdjointCocycles σ) :
    let χ := rationalArithmeticCyclotomicCoefficientCharacter a n hna k
    rationalArithmeticTraceZeroH1Cup a n hna σ hσ
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk u) =
      (Submodule.Quotient.mk
        (continuousOneCocycleCup (matrixTraceZeroCharacterRep σ χ.toMonoidHom)
          (matrixTraceZeroAdjointRep σ) (coefficientCharacterRep χ.toMonoidHom)
          matrixTraceZeroTracePairing
          (matrixTraceZeroTracePairing_character_equivariant σ χ.toMonoidHom)
          matrixTraceZeroTracePairing_continuous (matrixTraceZeroAdjointAction_continuous σ hσ)
          f (⟨u.val, u.property⟩ : continuousRepresentationCocyclesOne (matrixTraceZeroAdjointRep σ))) :
        ContinuousRepresentationH2 (coefficientCharacterRep χ.toMonoidHom)
          (coefficientCharacterAction_continuous χ.toMonoidHom χ.continuous)) := by
  exact matrixTraceZeroCharacterH1Cup_mk σ hσ
    (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom
    (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).continuous f u

end
end Dubon2026
