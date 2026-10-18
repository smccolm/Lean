import Dubon2026.ArithmeticRationalPrimeInvariant
import Dubon2026.ArithmeticRationalInvariantApply

/-! The actual canonical rational-prime coordinate equals the original
completion invariant at every upper prime and compatible closure. This
discharges the normalization input for DUB-17's rational local-cup total. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  bottomInvariantStageAlgebra bottomInvariantStageModule bottomInvariantStageSMul
  bottomInvariantStageTower bottomInvariantStageRationalGalois bottomInvariantStageGalois
  bottomInvariantStageFinite originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField

/-- The canonical rational-prime coordinate has the genuine normalized
original completion realization. All intermediate prime and closure
structures are constructed from the original completion tower. -/
theorem arithmeticCommonStageRationalPrimeInvariant_realization
    (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) :
    OriginalPrimeInvariantRealization ℚ F (arithmeticCommonStageRationalPrimeInvariant a F) := by
  intro v w hw Ω _ _ _ _ _ _ _ _ x
  let K : IntermediateField ℚ (rationalUnramifiedExtension a) := ⊥
  let u := (arithmeticOriginalBottomPrimeEquiv a).symm v
  letI : u.asIdeal.LiesOver v.asIdeal := arithmeticOriginalBottomPrimeEquiv_symm_liesOver a v
  letI : w.asIdeal.LiesOver u.asIdeal := arithmeticOriginalBottomPrimeEquiv_upper_liesOver a F v w
  letI : Algebra (v.adicCompletion ℚ) (u.adicCompletion K) :=
    (originalAdicBaseChangeMap ℚ K v u).toAlgebra
  letI : Algebra (u.adicCompletion K) (w.adicCompletion F) :=
    (originalAdicBaseChangeMap K F u w).toAlgebra
  letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion F) :=
    (originalAdicBaseChangeMap ℚ F v w).toAlgebra
  letI := originalAdicBaseChange_isScalarTower ℚ K F v u w
  letI : Algebra (u.adicCompletion K) Ω :=
    ((algebraMap (w.adicCompletion F) Ω).comp
      (originalAdicBaseChangeMap K F u w)).toAlgebra
  letI : IsScalarTower (u.adicCompletion K) (w.adicCompletion F) Ω :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (v.adicCompletion ℚ) (u.adicCompletion K) Ω :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro z
      change algebraMap (v.adicCompletion ℚ) Ω z =
        algebraMap (w.adicCompletion F) Ω
          (originalAdicBaseChangeMap K F u w (originalAdicBaseChangeMap ℚ K v u z))
      rw [originalAdicBaseChangeMap_tower]
      exact IsScalarTower.algebraMap_apply (v.adicCompletion ℚ) (w.adicCompletion F) Ω z)
  letI : IsGalois (u.adicCompletion K) Ω :=
    IsGalois.tower_top_of_isGalois (v.adicCompletion ℚ) (u.adicCompletion K) Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (u.adicCompletion K) Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (u.adicCompletion K) Ω) := ⟨rfl⟩
  have hpoint : rationalArithmeticRelativeStageIdelePrimeInvariant
      (hGal := bottomInvariantStageGalois a F) a K F.toIntermediateField bot_le u =
      originalFullIdeleCompletionInvariant K F u w Ω :=
    AddMonoidHom.ext (fun z => rationalArithmeticRelativeStage_prime_invariant_realization
      (hGal := bottomInvariantStageGalois a F) a K F.toIntermediateField bot_le u w Ω z)
  have hbase : (originalFullIdeleCompletionInvariant K F u w Ω).comp
      (arithmeticCommonStageIdeleToBottom a F) = originalFullIdeleCompletionInvariant ℚ F v w Ω :=
    AddMonoidHom.ext (fun z => arithmeticCommonStageIdeleToBottom_invariant a F v u w Ω z)
  have hmap : arithmeticCommonStageRationalPrimeInvariant a F v =
      originalFullIdeleCompletionInvariant ℚ F v w Ω :=
    (show arithmeticCommonStageRationalPrimeInvariant a F v =
      (rationalArithmeticRelativeStageIdelePrimeInvariant
        (hGal := bottomInvariantStageGalois a F) a K F.toIntermediateField bot_le u).comp
        (arithmeticCommonStageIdeleToBottom a F) from rfl).trans
      ((congrArg (fun f => f.comp (arithmeticCommonStageIdeleToBottom a F)) hpoint).trans hbase)
  exact congrArg (fun f : groupCohomology (originalFullIdeleRep ℚ F) 2 →+ AddCircle (1 : ℚ) => f x) hmap

end
end Dubon2026
