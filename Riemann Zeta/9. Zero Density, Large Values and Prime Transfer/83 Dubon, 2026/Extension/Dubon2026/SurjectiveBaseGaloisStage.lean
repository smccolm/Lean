import Mathlib.FieldTheory.Galois.Infinite

/-! # Rebase the same finite Galois stage across an actual base isomorphism

The completion/orbit comparison on DUB-17's reciprocity route has a
surjective base-field map. Thus every original finite stage already
contains the new base. Retaining its literal elements permits reuse of
the existing finite local-invariant base-change theorem.
-/
namespace Dubon2026
noncomputable section

variable (K E Ω : Type) [Field K] [Field E] [Field Ω]
  [Algebra K E] [Algebra K Ω] [Algebra E Ω] [IsScalarTower K E Ω]
  (h : Function.Surjective (algebraMap K E)) (F : FiniteGaloisIntermediateField K Ω)

/-- The same original subfield contains the entire new base because the base map is onto. -/
abbrev surjectiveBaseIntermediateField : IntermediateField E Ω :=
  F.toIntermediateField.toSubfield.toIntermediateField (by
    intro x
    obtain ⟨y, rfl⟩ := h x
    rw [← IsScalarTower.algebraMap_apply K E Ω]
    exact F.toIntermediateField.algebraMap_mem y)

/-- Retain the original small-base algebra on the identical stage carrier. -/
local instance surjectiveBaseStageOriginalAlgebra :
    Algebra K (surjectiveBaseIntermediateField K E Ω h F) := F.toIntermediateField.algebra'

/-- The new-base inclusion is compatible with the original small-base inclusion. -/
local instance surjectiveBaseStageTower :
    IsScalarTower K E (surjectiveBaseIntermediateField K E Ω h F) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact IsScalarTower.algebraMap_apply K E Ω x)

/-- The unchanged finite stage is still finite Galois over the isomorphic base. -/
abbrev surjectiveBaseGaloisStage : FiniteGaloisIntermediateField E Ω := by
  let G := surjectiveBaseIntermediateField K E Ω h F
  haveI : FiniteDimensional K G := F.finiteDimensional
  haveI : IsGalois K G := F.isGalois
  exact { toIntermediateField := G
          finiteDimensional := FiniteDimensional.right K E G
          isGalois := IsGalois.tower_top_of_isGalois K E G }

/-- Rebasing preserves the original literal subfield of the coefficient closure. -/
theorem surjectiveBaseGaloisStage_toSubfield :
    (surjectiveBaseGaloisStage K E Ω h F).toIntermediateField.toSubfield =
      F.toIntermediateField.toSubfield := rfl

end
end Dubon2026
