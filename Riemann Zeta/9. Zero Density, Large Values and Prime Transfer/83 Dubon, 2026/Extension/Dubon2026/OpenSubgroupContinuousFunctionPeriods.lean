import Dubon2026.CompactDiscreteFunctionPeriods

/-! # Original open-subgroup functions have periods normal in the ambient group

The existing compact-open period proof is applied on the actual open
subgroup, whose open image in the ambient compact group contains an open
normal subgroup. This supplies finite arithmetic descent for open-subgroup
class H1, a remaining class-formation input on DUB-17's duality route.
-/

namespace Dubon2026
noncomputable section

variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TopologicalSpace A] [DiscreteTopology A]

/-- A continuous function on an actual open subgroup has periods in an ambient open normal subgroup contained in it. -/
theorem openSubgroupContinuousFunction_exists_ambient_periods
    (H : OpenSubgroup G) (f : C(H, A)) :
    ∃ N : OpenNormalSubgroup G, N.toSubgroup ≤ H.toSubgroup ∧
      ∀ g u : H, (u : G) ∈ N → f (g * u) = f g := by
  letI : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  letI : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  let P := functionRightPeriodSubgroup f
  have hP : IsOpen (P : Set H) := functionRightPeriodSubgroup_isOpen f
  let J : OpenSubgroup G := ⟨P.map H.toSubgroup.subtype, by
    change IsOpen ((P.map H.toSubgroup.subtype : Subgroup G) : Set G)
    rw [Subgroup.coe_map]
    exact H.isOpen.isOpenMap_subtype_val _ hP⟩
  obtain ⟨N, hN⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    (show IsClopen (J : Set G) from ⟨J.isClosed, J.isOpen⟩) J.one_mem
  refine ⟨N, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, _, rfl⟩ := hN hu
    exact v.property
  · intro g u hu
    obtain ⟨v, hv, hvu⟩ := hN hu
    have he : v = u := Subtype.ext hvu
    subst v
    exact hv g

end
end Dubon2026
