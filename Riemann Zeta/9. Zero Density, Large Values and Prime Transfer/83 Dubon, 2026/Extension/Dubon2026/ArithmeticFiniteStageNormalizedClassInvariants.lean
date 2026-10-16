import Dubon2026.ArithmeticFiniteStageFullOrderClass
import Dubon2026.OriginalClassH2InvariantFromGenerator
import Dubon2026.OriginalFiniteCyclicNormalizedHom

/-! # Constructed normalized original class invariants at odd-primary cyclic stages

The full-order element is constructed, so the existing cyclic-generator
and invariant theorem applies with that input discharged. Agreement on its
generator identifies the resulting invariant with the actual original-prime
idele total. This closes the cyclic-stage invariant construction on DUB-17's
chain; arbitrary-stage transfer and inter-stage normalization remain separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticFiniteStageIdeleAddCommGroup
  arithmeticFiniteStageUpperTopology arithmeticFiniteStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- The actual odd-primary cyclic stage admits an injective original class invariant with exact degree-annihilator image and the literal full-idele total formula; its full-order generator is constructed. -/
theorem rationalArithmeticFiniteStage_exists_normalized_class_invariants
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ∃ invG : groupCohomology (originalIdeleClassRep F H) 2 →+ AddCircle (1 : ℚ),
      Function.Injective invG ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ q ^ (r + 1) • t = 0) ∧
      (∀ x : rationalArithmeticFiniteStageIdeleH2 a F H hFH,
        invG ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x) =
          rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH x) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  exact originalIdeleClass_normalized_invariant_of_witness F H (q ^ (r + 1))
    (pow_pos hq.pos (r + 1)) hdegree (rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH)
    (rationalArithmeticFiniteStage_exists_full_order_class a F H hFH q r hq hq2 hqa hcyclic hdegree)

end
end Dubon2026
