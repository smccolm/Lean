import Dubon2026.OriginalSinglePrimeBaseChangeInfinite
import Dubon2026.ArithmeticRelativeStageIdeleBaseChange
import Dubon2026.OriginalFullIdeleBaseChangeH2

/-! # The actual arithmetic relative-stage idele base-change map

Use the literal inclusions in the original arithmetic union. All global
scalar towers are derived from those inclusions. This supplies the map
whose total invariant must vanish in DUB-17's auxiliary-class transfer.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (K E L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]

/-- The actual arithmetic base change of a retained single-prime lift
has zero localization at every original target infinite place. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_lift_infinite_zero
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hw : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      OriginalFiniteDecompositionGroup K L w = ⊤)
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL)
    (hx : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      ∃ y : groupCohomology (originalAdicUnitRep K L w) 2,
        x = originalFullDecompositionIdeleH2Lift K L w hw y) :
    letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    ∀ v : NumberField.InfinitePlace M, originalFullIdeleInfiniteH2 E M v
      (rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) = 0 := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
  letI : Module K L := Algebra.toModule
  letI : SMul K L := ((IntermediateField.inclusion hKL).toAlgebra).toSMul
  letI : IsScalarTower ℚ K L := IsScalarTower.of_algHom (IntermediateField.inclusion hKL)
  letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
  letI : Module K M := Algebra.toModule
  letI : SMul K M := ((IntermediateField.inclusion (hKE.trans hEM)).toAlgebra).toSMul
  letI : IsScalarTower ℚ K M := IsScalarTower.of_algHom (IntermediateField.inclusion (hKE.trans hEM))
  letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  letI : Module E M := Algebra.toModule
  letI : SMul E M := ((IntermediateField.inclusion hEM).toAlgebra).toSMul
  letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom (IntermediateField.inclusion hEM)
  letI : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  letI : Module L M := Algebra.toModule
  letI : SMul L M := ((IntermediateField.inclusion hLM).toAlgebra).toSMul
  letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom (IntermediateField.inclusion hLM)
  letI : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsGalois K L := hGalKL
  obtain ⟨y, rfl⟩ := hx
  intro v
  exact originalFullDecompositionIdeleH2Lift_baseChange_infinite K E L M w hw v y

end
end Dubon2026
