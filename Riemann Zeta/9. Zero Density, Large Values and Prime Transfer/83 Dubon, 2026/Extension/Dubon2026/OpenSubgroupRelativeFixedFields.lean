import Dubon2026.OpenSubgroupFixedFieldRestriction

/-! # Actual fixed fields in a normal tower of open Galois subgroups

The original subgroup inclusion gives the genuine fixed-field inclusion.
Passing through the already proved fixed-field automorphism equivalence
identifies the relative fixing subgroup. Normality then proves the actual
relative extension Galois. This is the field input for compatible finite
quotient actions in DUB-17's arithmetic class-formation coefficient maps.
-/

namespace Dubon2026
noncomputable section
open IntermediateField

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (U V : OpenSubgroup Gal(Ω/K))

/-- The actual smaller open subgroup viewed among automorphisms over the larger subgroup's fixed field. -/
def openGaloisSubgroupRelativeGroup : Subgroup Gal(Ω/fixedField U.toSubgroup) :=
  (V.toSubgroup.subgroupOf U.toSubgroup).map (openGaloisSubgroupFixedFieldEquiv U).toMonoidHom

/-- The original relative subgroup fixes exactly the actual smaller subgroup's fixed field, with extended base scalars. -/
theorem openGaloisSubgroupRelativeGroup_fixedField (hVU : V.toSubgroup ≤ U.toSubgroup) :
    fixedField (openGaloisSubgroupRelativeGroup U V) =
      IntermediateField.extendScalars (fixedField_le hVU) := by
  ext x
  change (∀ g : openGaloisSubgroupRelativeGroup U V, g.val x = x) ↔
    ∀ g : V, g.val x = x
  constructor
  · intro hx g
    let u : U := ⟨g.val, hVU g.property⟩
    have hu : u ∈ V.toSubgroup.subgroupOf U.toSubgroup := g.property
    have hm : openGaloisSubgroupFixedFieldEquiv U u ∈ openGaloisSubgroupRelativeGroup U V :=
      ⟨u, hu, rfl⟩
    exact hx ⟨openGaloisSubgroupFixedFieldEquiv U u, hm⟩
  · intro hx g
    obtain ⟨u, hu, he⟩ := g.property
    rw [← he]
    exact hx ⟨u.val, hu⟩

/-- Normality in the original larger open subgroup is preserved by the genuine fixed-field automorphism comparison. -/
theorem openGaloisSubgroupRelativeGroup_normal
    [(V.toSubgroup.subgroupOf U.toSubgroup).Normal] :
    (openGaloisSubgroupRelativeGroup U V).Normal :=
  Subgroup.Normal.map inferInstance (openGaloisSubgroupFixedFieldEquiv U).toMonoidHom
    (openGaloisSubgroupFixedFieldEquiv U).surjective

/-- A normal inclusion of actual open subgroups yields the genuine finite relative Galois extension of their fixed fields. -/
theorem openGaloisSubgroup_fixedField_relative_isGalois
    (hVU : V.toSubgroup ≤ U.toSubgroup)
    [(V.toSubgroup.subgroupOf U.toSubgroup).Normal] :
    letI : Algebra (fixedField U.toSubgroup) (fixedField V.toSubgroup) :=
      (IntermediateField.inclusion (fixedField_le hVU)).toAlgebra
    IsGalois (fixedField U.toSubgroup) (fixedField V.toSubgroup) := by
  letI : Algebra (fixedField U.toSubgroup) (fixedField V.toSubgroup) :=
    (IntermediateField.inclusion (fixedField_le hVU)).toAlgebra
  let T := IntermediateField.extendScalars (fixedField_le hVU)
  haveI : (openGaloisSubgroupRelativeGroup U V).Normal := openGaloisSubgroupRelativeGroup_normal U V
  have hT : IsGalois (fixedField U.toSubgroup) T := by
    let e := IntermediateField.equivOfEq (openGaloisSubgroupRelativeGroup_fixedField U V hVU)
    exact IsGalois.of_algEquiv e
  exact hT

end
end Dubon2026
