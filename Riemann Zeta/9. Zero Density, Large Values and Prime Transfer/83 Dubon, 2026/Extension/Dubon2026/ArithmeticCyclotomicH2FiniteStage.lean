import Dubon2026.FiniteCoefficientGaloisH2Stage
import Dubon2026.ArithmeticCyclotomicCohomologyRestriction
import Dubon2026.UnramifiedUnionFiniteRamification
import Mathlib.Topology.Instances.ZMod

/-! # Actual finite descent of the original arithmetic cyclotomic H2

This applies the proved finite-stage construction to the same cyclotomic H2
used by the original global trace cup. The remaining support edge is to prove
that its actual prime-local images descend to unramified local stages.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)

/-- The original arithmetic cyclotomic H2 class has a constructed finite
Galois presentation inside the original unramified arithmetic extension.
No independent finite-stage or descent premise is required. -/
theorem rationalArithmeticCyclotomicH2_exists_finite_stage
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
    let A := coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
    let hA := coefficientCharacterAction_continuous _
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous
    ∃ F : FiniteGaloisIntermediateField ℚ U,
      letI : IsGalois ℚ F := F.isGalois
      ∃ ρ : Representation (ZMod q) Gal(F/ℚ) A,
        ∃ hρ : ∀ g : Gal(U/ℚ), ∀ b : A, ρ ((AlgEquiv.restrictNormalHom F : Gal(U/ℚ) →* Gal(F/ℚ)) g) b = A.ρ g b,
          ∃ y : ContinuousRepresentationH2 (Rep.of ρ) continuous_of_discreteTopology,
            finiteCoefficientGaloisH2Inflation A hA F ρ hρ y = x := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  exact continuousFiniteCoefficientH2_exists_finite_stage _ _ x

/-- The same constructed presentation is unramified at every original finite
prime away from the actual exceptional integer. This uses the proved original
arithmetic-union ramification theorem, not an added unramifiedness assumption. -/
theorem rationalArithmeticCyclotomicH2_exists_unramified_finite_stage (ha : a ≠ 0)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
    let A := coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
    let hA := coefficientCharacterAction_continuous _
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous
    ∃ F : FiniteGaloisIntermediateField ℚ U,
      letI : IsGalois ℚ F := F.isGalois
      (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        algebraMap (𝓞 ℚ) (𝓞 F) a ∉ w.asIdeal →
          (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1) ∧
      ∃ ρ : Representation (ZMod q) Gal(F/ℚ) A,
        ∃ hρ : ∀ g : Gal(U/ℚ), ∀ b : A, ρ ((AlgEquiv.restrictNormalHom F : Gal(U/ℚ) →* Gal(F/ℚ)) g) b = A.ρ g b,
          ∃ y : ContinuousRepresentationH2 (Rep.of ρ) continuous_of_discreteTopology,
            finiteCoefficientGaloisH2Inflation A hA F ρ hρ y = x := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  apply Exists.imp ?_ (rationalArithmeticCyclotomicH2_exists_finite_stage a q hqa x)
  intro F hF
  refine ⟨?_, hF⟩
  intro w hw
  exact originalUnramifiedUnion_finite_ramification a ha F.toIntermediateField w hw

end
end Dubon2026
