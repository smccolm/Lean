import Dubon2026.OpenSubgroupRelativeRestriction
import Dubon2026.FiniteBaseGaloisTopology

/-! # Original Krull continuity in normal towers of open subgroups

The fixed-field automorphism equivalence and relative restriction preserve
the actual Krull topologies. This permits the finite quotient coefficient
comparison to feed continuous H2 on DUB-17's arithmetic duality route.
-/

namespace Dubon2026
noncomputable section
open IntermediateField

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The genuine open-subgroup fixed-field equivalence is continuous for the original Krull topologies. -/
theorem openGaloisSubgroupFixedFieldEquiv_continuous (U : OpenSubgroup Gal(Ω/K)) :
    Continuous (openGaloisSubgroupFixedFieldEquiv U) := by
  let E := fixedField U.toSubgroup
  letI : FiniteDimensional K E := openGaloisSubgroup_fixedField_finite U
  let i : U → E.fixingSubgroup := fun g =>
    ⟨g.val, by rw [openGaloisSubgroup_fixing_fixedField U]; exact g.property⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  exact (finiteBase_fixingSubgroupEquiv_continuous E).comp hi

/-- Original relative fixed-field restriction is continuous on the actual larger open subgroup. -/
theorem openGaloisSubgroupRelativeRestriction_continuous
    (U V : OpenSubgroup Gal(Ω/K)) (hVU : V.toSubgroup ≤ U.toSubgroup)
    [(V.toSubgroup.subgroupOf U.toSubgroup).Normal] :
    Continuous (openGaloisSubgroupRelativeRestriction U V hVU) := by
  let T := IntermediateField.extendScalars (fixedField_le hVU)
  letI : IsGalois (fixedField U.toSubgroup) T :=
    openGaloisSubgroup_fixedField_relative_isGalois U V hVU
  exact (InfiniteGalois.restrictNormalHom_continuous T).comp
    (openGaloisSubgroupFixedFieldEquiv_continuous U)

end
end Dubon2026
