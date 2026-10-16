import Dubon2026.ArithmeticRelativeStageFullOrderClass
import Dubon2026.OriginalClassInvariantSystemFromWitness

/-! # Original cyclic class invariants at a relative arithmetic stage

Apply the existing original-object argument to an actual finite extension
which is Galois over its specified base. No normality over the rationals
is required. This is the auxiliary-stage interface needed by DUB-17's
class-generator transfer, with all local maps and scalar towers retained.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- The actual odd-primary cyclic stage admits an injective original class invariant with exact degree-annihilator image, the literal full-idele total formula and normalized actual subgroup restrictions; its full-order generator is constructed. -/
theorem rationalArithmeticRelativeStage_exists_normalized_class_system
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
      (∀ x : rationalArithmeticRelativeStageIdeleH2 a F H hFH,
        invG ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x) =
          rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x) ∧
      ∀ S : Subgroup Gal(H/F),
        ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep F H)) 2 →+ AddCircle (1 : ℚ),
          Function.Injective invS ∧
          (∀ t : AddCircle (1 : ℚ), t ∈ invS.range ↔ Nat.card S • t = 0) ∧
          ∀ x : groupCohomology (originalIdeleClassRep F H) 2,
            invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep F H))) 2).hom x) =
              S.index • invG x := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  exact originalIdeleClass_normalized_system_of_witness F H (q ^ (r + 1))
    (pow_pos hq.pos (r + 1)) hdegree (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH)
    (rationalArithmeticRelativeStage_exists_full_order_class a F H hFH q r hq hq2 hqa hcyclic hdegree)

end
end Dubon2026
