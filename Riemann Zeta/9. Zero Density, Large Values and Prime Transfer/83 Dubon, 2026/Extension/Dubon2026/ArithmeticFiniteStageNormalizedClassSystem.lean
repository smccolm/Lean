import Dubon2026.ArithmeticFiniteStageFullOrderClass
import Dubon2026.OriginalClassInvariantSystemFromWitness

/-! # Actual odd-primary cyclic class invariants and subgroup normalization

The constructed full-order original class supplies the native subgroup
generators. The prescribed global invariant remains the descended actual
idele total, and every original subgroup restriction has its index factor.
This discharges the subgroup-system input on DUB-17's finite class-invariant
chain; arbitrary-stage transfer and inter-stage/local comparisons remain.
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

/-- The actual odd-primary cyclic stage admits an injective original class invariant with exact degree-annihilator image, the literal full-idele total formula and normalized actual subgroup restrictions; its full-order generator is constructed. -/
theorem rationalArithmeticFiniteStage_exists_normalized_class_system
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
          rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH x) ∧
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
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  exact originalIdeleClass_normalized_system_of_witness F H (q ^ (r + 1))
    (pow_pos hq.pos (r + 1)) hdegree (rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH)
    (rationalArithmeticFiniteStage_exists_full_order_class a F H hFH q r hq hq2 hqa hcyclic hdegree)

end
end Dubon2026
