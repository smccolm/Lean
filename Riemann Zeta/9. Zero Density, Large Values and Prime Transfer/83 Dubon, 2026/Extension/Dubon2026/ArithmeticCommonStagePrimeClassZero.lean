import Dubon2026.ArithmeticCommonStageSylowClass
import Dubon2026.ArithmeticCommonStageRationalTotal
import Dubon2026.ArithmeticNonNormalOddPrimaryClassZero

/-! Combine the actual common-field Sylow restriction with canonical
nonnormal total base change. This is the finite class-vanishing step
for DUB-17's source-cup obstruction, before identifying the source local sum. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

/-- Zero canonical total kills the actual prime-annihilated full-class
image at any common finite arithmetic stage. Its Sylow fixed field,
prime-power degree, odd-primary invariant system and nonnormal total
comparison are all derived, without a restriction-vanishing premise. -/
theorem arithmeticCommonStageIdele_class_zero_of_total_zero
    (a : 𝓞 ℚ) (M : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (x : groupCohomology (originalFullIdeleRep ℚ M) 2)
    (hp : p • (groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalFullClassRepHom ℚ M) x = 0)
    (hx : arithmeticCommonStageRationalIdeleTotal a M x = 0) :
    (groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalFullClassRepHom ℚ M) x = 0 := by
  let S : Sylow p Gal(M/ℚ) := Classical.choice inferInstance
  let c := (groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalFullClassRepHom ℚ M) x
  have hdetect := arithmeticCommonStageClass_eq_zero_iff_sylow a M p S c hp
  let E := arithmeticCommonStageFixedField a M (S : Subgroup Gal(M/ℚ))
  have hEM : E ≤ M.toIntermediateField := arithmeticCommonStageFixedField_le a M _
  let K : IntermediateField ℚ (rationalUnramifiedExtension a) := ⊥
  have hKE : K ≤ E := bot_le
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := Algebra.toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  letI : Module E M := Algebra.toModule
  letI : SMul E M := Algebra.toSMul
  letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom (IntermediateField.inclusion hEM)
  letI : FiniteDimensional ℚ E := FiniteDimensional.left ℚ E M
  letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
  letI : Module K M := Algebra.toModule
  letI : SMul K M := Algebra.toSMul
  letI : IsScalarTower ℚ K M := IsScalarTower.of_algHom (IntermediateField.inclusion (hKE.trans hEM))
  letI : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsGalois K M := IsGalois.tower_top_of_isGalois ℚ K M
  letI : IsGalois E M := IsGalois.tower_top_of_isGalois ℚ E M
  obtain ⟨t, ht⟩ := arithmeticCommonStageSylowFixedField_degree a M p S
  let xb := arithmeticCommonStageIdeleToBottom a M x
  have hxb : rationalArithmeticRelativeStageIdeleTotalInvariant a K M.toIntermediateField
      (hKE.trans hEM) xb = 0 := hx
  have hz := rationalArithmeticRelativeStageIdeleBaseChange_odd_primary_class_zero
    a K E M.toIntermediateField hKE hEM p t (Fact.out : p.Prime) hp2 hpa ht xb hxb
  have hclass := originalFullIdeleBaseChangeH2_class_same_upper K E M xb
  have hbottom := arithmeticCommonStageIdeleToBottom_class a M x
  have hcomp := originalIdeleClassTowerH2Restriction_comp ℚ K E M c
  apply hdetect.mpr
  exact hcomp.symm.trans
    ((congrArg (originalIdeleClassTowerH2Restriction K E M) hbottom).symm.trans
      (hclass.symm.trans hz))

end
end Dubon2026
