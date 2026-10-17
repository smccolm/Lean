import Dubon2026.ArithmeticAllPrimePowerFullOrderClass
import Dubon2026.OriginalClassInvariantSystemFromFullOrder

/-! # Construct normalized subgroup invariants on every prime-power stage

Consume the actual full-order class obtained from the constructed
auxiliary tower. The original restriction/corestriction argument gives
injective invariants with exact images and the subgroup-index formula.
Comparison with canonical local totals and between separate finite
stages is still required for DUB-17's reverse localization input.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup

/-- Every actual finite Galois prime-power arithmetic stage has a constructed full-order class and normalized injective global and subgroup invariants with exact images and the original restriction-index formula. -/
theorem rationalArithmeticRelativeAllPrimePower_exists_class_invariant_system
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ u : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf u = Module.finrank K E ∧
      ∃ invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ),
        Function.Injective invG ∧
        (∀ z : AddCircle (1 : ℚ), z ∈ invG.range ↔ Module.finrank K E • z = 0) ∧
        invG u = ↑((1 : ℚ) / Module.finrank K E) ∧
        ∀ S : Subgroup Gal(E/K),
          ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2 →+ AddCircle (1 : ℚ),
            Function.Injective invS ∧
            (∀ z : AddCircle (1 : ℚ), z ∈ invS.range ↔ Nat.card S • z = 0) ∧
            ∀ x : groupCohomology (originalIdeleClassRep K E) 2,
              invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom x) =
                S.index • invG x := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : IsGalois K E := hGalKE
  exact originalIdeleClass_invariant_system_of_full_order_witness K E
    (rationalArithmeticRelativeAllPrimePower_exists_full_order_class
      (hGalKE := hGalKE) a K E hKE q t hq hqa hdegreeKE)

end
end Dubon2026