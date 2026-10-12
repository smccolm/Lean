import Dubon2026.FiniteGaloisRebasedAlgebra
import Dubon2026.GaloisUnitH2AlgebraCongruence

/-! # Original H2 classes of the same field under a rebased stage description -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (E H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H)

/-- The actual same-coefficient identification between the original
H/E continuous cohomology and its description as the rebased original stage. -/
def finiteGaloisStageRebasedH2Equiv :
    letI : Algebra E H := (IntermediateField.inclusion hEH).toAlgebra
    letI : IsScalarTower K E H := IsScalarTower.of_algHom (IntermediateField.inclusion hEH)
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
    GaloisUnitContinuousH2 (K := E) (Ω := H) ≃ₗ[ℤ]
      GaloisUnitH2FiniteStage E Ω (finiteGaloisStageExtendScalars E H hEH) := by
  let a : Algebra E H := (IntermediateField.inclusion hEH).toAlgebra
  let b : Algebra E H := inferInstanceAs
    (Algebra E (finiteGaloisStageExtendScalars E H hEH))
  exact galoisUnitH2AlgebraCongruence a b
    (finiteGaloisStageExtendScalars_algebra_eq E H hEH) _ _

/-- The rebased original-stage identification is bijective on the
actual continuous H2 classes of the same original field. -/
theorem finiteGaloisStageRebasedH2Equiv_bijective :
    letI : Algebra E H := (IntermediateField.inclusion hEH).toAlgebra
    letI : IsScalarTower K E H := IsScalarTower.of_algHom (IntermediateField.inclusion hEH)
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
    Function.Bijective (finiteGaloisStageRebasedH2Equiv E H hEH) :=
  (finiteGaloisStageRebasedH2Equiv E H hEH).bijective

end
end Dubon2026
