import Dubon2026.ArithmeticAllPrimeAuxiliaryComposita
import Dubon2026.ArithmeticTowerInfiniteKernelClassSystem

/-! # Canonical class systems for every actual prime-power stage

The native cyclotomic auxiliary-field construction and the actual
single-prime idele transfer now yield a class invariant whose formula is
the original-prime total on the zero-infinite part. Cyclicity of the given stage, auxiliary
fields, class witnesses and compatibility certificates are all discharged.
This supplies the all-prime finite-stage total clause on DUB-17's
class-invariant dependency. Local fundamental classes and inter-stage
normalization remain separate required comparisons.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup arithmeticRelativeStageIdeleAddCommGroup

/-- Every actual finite Galois prime-power stage in the fixed arithmetic union has injective global and subgroup invariants with exact images, the literal idele-total formula on the zero-infinite part and the subgroup-index relation, with no supplied auxiliary fields or class witnesses. -/
theorem rationalArithmeticRelativeAllPrimePower_exists_infinite_kernel_class_system
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
    OriginalInfiniteKernelClassInvariantSystem K E
      (rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE) := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  obtain ⟨D, r, s, hGalKL, hcyclicKL, hdegreeKL, hGalEM, hcyclicEM, hdegreeEM, hGalKM, hd⟩ :=
    rationalArithmetic_exists_allPrime_cyclic_auxiliary_composita a K E hKE hGalKE q t hq hqa hdegreeKE
  let L := K ⊔ D.toIntermediateField
  let M := E ⊔ D.toIntermediateField
  have hKL : K ≤ L := le_sup_left
  have hEM : E ≤ M := le_sup_left
  have hLM : L ≤ M := sup_le_sup_right hKE D.toIntermediateField
  exact rationalArithmeticRelativeStage_exists_infinite_kernel_class_system
    (hGalKE := hGalKE) (hGalKL := hGalKL) (hGalEM := hGalEM) (hGalKM := hGalKM)
    a K E L M hKE hKL hEM hLM q t r s hq hqa hdegreeKE hcyclicKL hdegreeKL hcyclicEM hdegreeEM hd

end
end Dubon2026
