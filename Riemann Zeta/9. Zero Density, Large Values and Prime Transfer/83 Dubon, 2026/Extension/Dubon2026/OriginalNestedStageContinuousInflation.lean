import Dubon2026.OriginalCyclotomicContinuousH2Descent
import Dubon2026.OriginalAlgebraicContinuousInflationMap

/-! # Literal nested-stage inflation in the original arithmetic union

The cyclic field for the prime two is an actual subfield of the chosen
cyclotomic stage. Its composed inclusions give the scalar towers required
by the existing finite-to-continuous inflation comparison. This exact
embedding comparison serves DUB-17's two-primary cyclic descent.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
  AlgebraicClosure.instSMulOfIsScalarTower

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  (a : 𝓞 ℚ)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Equality of the two literal finite inflation maps into the original
common field. This records only the finite equality, not its subsequent
continuous consequence. -/
def originalNestedStageFiniteInflationEq
    (L F : FiniteGaloisIntermediateField ℚ Ω) (E : IntermediateField ℚ F) [IsGalois ℚ E]
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2)
    (y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ E) 2) : Prop :=
    let M := L.toIntermediateField ⊔ F.toIntermediateField
      let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
      let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
      let iE : E →ₐ[ℚ] M := iF.comp E.val
      letI : Algebra L M := iL.toAlgebra
      letI : Algebra E M := iE.toAlgebra
      letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
      letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom iE
      groupCohomology.map (AlgEquiv.restrictNormalHom E) (finiteGaloisUnitTowerInclusion ℚ E M) 2 y =
        groupCohomology.map (AlgEquiv.restrictNormalHom L) (finiteGaloisUnitTowerInclusion ℚ L M) 2 x

/-- Equality of actual finite inflations from a nested original subfield
implies equality of its literal continuous inflation in the original union. -/
theorem originalNestedStage_finiteInflation_eq_continuousInflation
    (L F : FiniteGaloisIntermediateField ℚ Ω) (E : IntermediateField ℚ F) [IsGalois ℚ E]
    (hL : L.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (hF : F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2)
    (y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ E) 2)
    (hxy : originalNestedStageFiniteInflationEq L F E x y) :
    let U := originalUnramifiedGaloisUnion (Ω := Ω) a
    letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
    let iEU := (IntermediateField.inclusion hF).comp E.val
    letI : Algebra L U := (IntermediateField.inclusion hL).toAlgebra
    letI : IsScalarTower ℚ L U := IsScalarTower.of_algHom (IntermediateField.inclusion hL)
    letI : Algebra E U := iEU.toAlgebra
    letI : IsScalarTower ℚ E U := IsScalarTower.of_algHom iEU
    originalAlgebraicContinuousInflation ℚ E U y =
      originalAlgebraicContinuousInflation ℚ L U x := by
  dsimp only
  let M := L.toIntermediateField ⊔ F.toIntermediateField
  let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
  let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
  let iE : E →ₐ[ℚ] M := iF.comp E.val
  letI : Algebra L M := iL.toAlgebra
  letI : Algebra E M := iE.toAlgebra
  letI : SMul E M := iE.toAlgebra.toSMul
  letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
  letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom iE
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  letI : Algebra L U := (IntermediateField.inclusion hL).toAlgebra
  letI : IsScalarTower ℚ L U := IsScalarTower.of_algHom (IntermediateField.inclusion hL)
  let iEU : E →ₐ[ℚ] U := (IntermediateField.inclusion hF).comp E.val
  letI : Algebra E U := iEU.toAlgebra
  letI : SMul E U := iEU.toAlgebra.toSMul
  letI : IsScalarTower ℚ E U := IsScalarTower.of_algHom iEU
  let iM : M →ₐ[ℚ] U := IntermediateField.inclusion (sup_le hL hF)
  letI : Algebra M U := iM.toAlgebra
  letI : IsScalarTower ℚ M U := IsScalarTower.of_algHom iM
  letI : IsScalarTower L M U := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower E M U := IsScalarTower.of_algebraMap_eq' rfl
  exact originalAlgebraicContinuousInflation_eq_of_finite ℚ E L M U y x hxy

end
end Dubon2026
