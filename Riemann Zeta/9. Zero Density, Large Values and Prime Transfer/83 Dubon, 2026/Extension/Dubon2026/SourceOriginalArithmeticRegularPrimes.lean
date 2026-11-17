import Dubon2026.SourceOriginalArithmeticRegularCocycle
import Dubon2026.SourceOriginalRegularPrimeAssembly
import Dubon2026.HomogeneousSymmetricContinuity

/-! DUB-17/18 -> original auxiliary-prime detection. The proper-subfield
regular element is passed to the existing generic finite-factor Chebotarev
theorem. The selected prime detects the original continuous H1 class. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix
open scoped NumberField
attribute [local instance] rationalArithmeticOriginalFiniteGalois

/-- Each nonzero original twisted class has regular detecting congruence
primes outside every finite set under the actual finite linear subfield bounds.
The original finite factor and original local Frobenius witness are retained. -/
theorem original_arithmetic_symmetric_nonzero_class_regular_primes
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p degree level : ℕ) [Fact p.Prime]
    (hpa : (p : 𝓞 ℚ) ∣ a)
    {F : Type} [Field F] [Finite F] [CharP F p]
    [TopologicalSpace F] [DiscreteTopology F] [IsTopologicalRing F]
    (j : F →+* K p)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) F)
    (hρ : Continuous ρ) (hp3 : 3 < p)
    (h : HasFiniteLinearSubfieldBounds p j ρ) (hn : 2 * degree < p - 1)
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep
      ((homogeneousSymmetricGL degree).comp ρ)
      (rationalArithmeticCyclotomicCoefficientCharacter a p hpa F).toMonoidHom))
    (hc : (Submodule.Quotient.mk c : ContinuousRepresentationH1
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL degree).comp ρ)
        (rationalArithmeticCyclotomicCoefficientCharacter a p hpa F).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous ((homogeneousSymmetricGL degree).comp ρ)
        ((homogeneousSymmetricGL_continuous degree).comp hρ)
        (rationalArithmeticCyclotomicCoefficientCharacter a p hpa F).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a p hpa F).continuous)) ≠ 0) :
    let R := (homogeneousSymmetricGL degree).comp ρ
    let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
    let ξ := rationalArithmeticCyclotomicCoefficientCharacter a p hpa F
    let A := matrixTraceZeroCharacterRep R ξ.toMonoidHom
    let hA := matrixTraceZeroCharacterAction_continuous R hR ξ.toMonoidHom ξ.continuous
    HasArithmeticRegularDetectingPrimes a p level A hA R c := by
  let R := (homogeneousSymmetricGL degree).comp ρ
  let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
  let ξ := rationalArithmeticCyclotomicCoefficientCharacter a p hpa F
  let A := matrixTraceZeroCharacterRep R ξ.toMonoidHom
  let hA := matrixTraceZeroCharacterAction_continuous R hR ξ.toMonoidHom ξ.continuous
  let Rres : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup (Fin (degree + 1)) F := ⟨R, hR⟩
  have hroot := original_arithmetic_symmetricH1_exists_regular_root_detection
    a p degree level hpa j ρ hp3 h hn hA c hc
  exact rationalArithmetic_regular_primes_of_root_detection
    a ha p level hpa A hA Rres c hroot

end
end Dubon2026.SourceDickson
