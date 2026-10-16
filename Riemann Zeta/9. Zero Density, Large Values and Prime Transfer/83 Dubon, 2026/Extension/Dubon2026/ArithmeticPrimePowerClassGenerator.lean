import Dubon2026.ArithmeticCyclicAuxiliaryComposita
import Dubon2026.ArithmeticRelativeStageClassGenerator

/-! # Construct the original class generator for every odd-primary stage

Construct both auxiliary fields inside the fixed arithmetic union, then
consume the actual idele-witness generator transfer. The only degree
condition is on the given finite Galois stage; cyclicity of that stage
and all auxiliary field, class, normalization and vanishing hypotheses
are discharged. This advances DUB-17's normalized class-invariant input
to reverse H1 localization and arithmetic patching.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup

/-- The actual original idele-class H2 of every finite Galois odd-prime-power stage in the fixed arithmetic union has its exact extension degree and a constructed generator; no auxiliary fields or class witnesses are assumed. -/
theorem rationalArithmeticRelativePrimePower_exists_class_generator
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      Nat.card (groupCohomology (originalIdeleClassRep K E) 2) = Module.finrank K E ∧
      Submodule.span ℤ {y} = ⊤ := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  obtain ⟨D, r, s, hGalKL, hcyclicKL, hdegreeKL, hGalEM, hcyclicEM, hdegreeEM, hGalKM, hd⟩ :=
    rationalArithmetic_exists_cyclic_auxiliary_composita a K E hKE hGalKE q t hq hq2 hqa hdegreeKE
  let L := K ⊔ D.toIntermediateField
  let M := E ⊔ D.toIntermediateField
  have hKL : K ≤ L := le_sup_left
  have hEM : E ≤ M := le_sup_left
  have hLM : L ≤ M := sup_le_sup_right hKE D.toIntermediateField
  exact rationalArithmeticRelativeStage_exists_class_generator
    (hGalKE := hGalKE) (hGalKL := hGalKL) (hGalEM := hGalEM) (hGalKM := hGalKM)
    a K E L M hKE hKL hEM hLM q r s hq hq2 hqa hcyclicKL hdegreeKL hcyclicEM hdegreeEM hd

end
end Dubon2026
