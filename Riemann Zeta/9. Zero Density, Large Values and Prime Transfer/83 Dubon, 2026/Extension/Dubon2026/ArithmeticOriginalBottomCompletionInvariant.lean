import Dubon2026.ArithmeticOriginalBottomCompletionDegree
import Dubon2026.OriginalAdicSelfBaseChange
import Dubon2026.OriginalFullIdeleInvariantBaseChange

/-! The same rational-base full-idele class has the same normalized local
invariant after its actual change to the arithmetic bottom field. The
proved local degree one removes the multiplier. This is the local square
needed by DUB-17's rational canonical total, with the original class retained. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- Retain the literal inclusion of the arithmetic bottom field. -/
local instance bottomInvariantStageAlgebra :
    Algebra (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) F :=
  (IntermediateField.inclusion (show (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) ≤
    F.toIntermediateField from bot_le)).toAlgebra

/-- Use the module structure of that literal inclusion. -/
local instance bottomInvariantStageModule :
    Module (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) F :=
  @Algebra.toModule _ _ _ _ (bottomInvariantStageAlgebra a F)

/-- Use the scalar action of that literal inclusion. -/
local instance bottomInvariantStageSMul :
    SMul (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) F :=
  @Algebra.toSMul _ _ _ _ (bottomInvariantStageAlgebra a F)

/-- The actual lower inclusion is a rational algebra map. -/
local instance bottomInvariantStageTower :
    IsScalarTower ℚ (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) F :=
  IsScalarTower.of_algHom (IntermediateField.inclusion
    (show (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) ≤ F.toIntermediateField from bot_le))

/-- The same finite arithmetic field is Galois over the rationals. -/
local instance bottomInvariantStageRationalGalois : IsGalois ℚ F := F.isGalois

/-- It remains Galois over the actual arithmetic bottom field. -/
local instance bottomInvariantStageGalois :
    IsGalois (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) F :=
  IsGalois.tower_top_of_isGalois ℚ (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) F

/-- Its actual degree over the bottom field is finite. -/
local instance bottomInvariantStageFinite :
    FiniteDimensional (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) F :=
  FiniteDimensional.right ℚ (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) F

variable (v : HeightOneSpectrum (𝓞 ℚ))
  (u : HeightOneSpectrum (𝓞 (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))))
  (w : HeightOneSpectrum (𝓞 F))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]
  (Ω : Type) [Field Ω]
  [Algebra (v.adicCompletion ℚ) Ω]
  [Algebra (u.adicCompletion (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))) Ω]
  [Algebra (w.adicCompletion F) Ω]
  [IsScalarTower (v.adicCompletion ℚ)
    (u.adicCompletion (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))) Ω]
  [IsScalarTower (v.adicCompletion ℚ) (w.adicCompletion F) Ω]
  [IsScalarTower (u.adicCompletion (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)))
    (w.adicCompletion F) Ω]
  [IsGalois (v.adicCompletion ℚ) Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion ℚ) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion ℚ) Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (u.adicCompletion (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (u.adicCompletion (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))) Ω)]

/-- The actual bottom-field image preserves the original normalized
completion invariant; the required local degree multiplier is derived. -/
theorem arithmeticCommonStageIdeleToBottom_invariant
    (x : groupCohomology (originalFullIdeleRep ℚ F) 2) :
    letI : IsGalois (u.adicCompletion (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))) Ω :=
      IsGalois.tower_top_of_isGalois (v.adicCompletion ℚ)
        (u.adicCompletion (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))) Ω
    originalFullIdeleCompletionInvariant (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) F u w Ω
      (arithmeticCommonStageIdeleToBottom a F x) =
      originalFullIdeleCompletionInvariant ℚ F v w Ω x := by
  letI : Algebra F F := Algebra.id F
  letI : Module F F := (Algebra.id F).toModule
  letI : SMul F F := (Algebra.id F).toSMul
  letI : IsGalois (u.adicCompletion (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))) Ω :=
    IsGalois.tower_top_of_isGalois (v.adicCompletion ℚ)
      (u.adicCompletion (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))) Ω
  letI : @Ideal.LiesOver (𝓞 F) _ (𝓞 F) _ (NumberField.inst_ringOfIntegersAlgebra F F)
      w.asIdeal w.asIdeal := originalAdicSelfPrimeLiesOver F w
  letI : Algebra (w.adicCompletion F) (w.adicCompletion F) :=
    (originalAdicBaseChangeMap F F w w).toAlgebra
  letI : Module (w.adicCompletion F) (w.adicCompletion F) :=
    (originalAdicBaseChangeMap F F w w).toAlgebra.toModule
  letI : SMul (w.adicCompletion F) (w.adicCompletion F) :=
    (originalAdicBaseChangeMap F F w w).toAlgebra.toSMul
  letI : IsScalarTower (w.adicCompletion F) (w.adicCompletion F) Ω :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro z
      change algebraMap (w.adicCompletion F) Ω z =
        algebraMap (w.adicCompletion F) Ω (originalAdicBaseChangeMap F F w w z)
      rw [originalAdicBaseChangeMap_self])
  have h := @originalFullIdeleCompletionInvariant_baseChange ℚ
    (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) F F
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    v u w w inferInstance inferInstance inferInstance inferInstance
    (originalAdicSelfPrimeLiesOver F w)
    Ω inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance x
  simpa only [arithmeticOriginalBottomCompletion_finrank a v u, one_nsmul] using h

end
end Dubon2026
