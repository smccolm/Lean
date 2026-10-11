import Dubon2026.LocalFieldIntegerAlgEquiv
import Dubon2026.CompactSeparatedLocalAdicTopology
import Mathlib.Topology.Algebra.Group.Units

/-! # Continuity of actual local-field equivalences in their original topologies -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]

/-- The actual induced local integer-ring equivalence is continuous in its
original compact adic topology. Its literal coefficient identity and the
openness of the original integer ring extend continuity to the actual fields. -/
theorem localField_algEquiv_continuous (e : L ≃ₐ[K] M) : Continuous e := by
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  letI := IsTopologicalAddGroup.rightUniformSpace M
  haveI := isUniformAddGroup_of_addCommGroup (G := M)
  haveI : IsLocalHom (localFieldIntegerAlgEquiv K L M e).toRingHom :=
    IsLocalHom.of_surjective _ (localFieldIntegerAlgEquiv K L M e).surjective
  have hc : Continuous (localFieldIntegerAlgEquiv K L M e) :=
    compactSeparatedLocalRingHom_continuous (localFieldIntegerAlgEquiv K L M e).toRingHom
  have hi : Continuous (fun x : 𝒪[L] => e (x : L)) := by
    have h := (continuous_subtype_val : Continuous (fun x : 𝒪[M] => (x : M))).comp hc
    convert h using 1
    funext x
    exact (localFieldIntegerAlgEquiv_coefficient K L M e x).symm
  apply continuous_of_continuousAt_zero e.toRingHom
  exact (Valuation.isOpen_integer (v := ValuativeRel.valuation L)).isOpenEmbedding_subtypeVal.continuousAt_iff.mp
    (hi.continuousAt (x := (0 : 𝒪[L])))

/-- The genuine unit map of the original field equivalence is continuous
in the original unit topologies. -/
theorem localField_algEquiv_units_continuous (e : L ≃ₐ[K] M) :
    Continuous (Units.map (e : L →+* M).toMonoidHom) := by
  exact Continuous.units_map _ (localField_algEquiv_continuous K L M e)

end
end Dubon2026
