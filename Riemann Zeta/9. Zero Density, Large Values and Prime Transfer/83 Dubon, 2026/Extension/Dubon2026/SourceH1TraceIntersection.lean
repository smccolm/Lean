import Dubon2026.SourceH1TraceTower
import Dubon2026.OriginalGroupCohomologyReindex

/-! DUB-17/18 -> original all-weight adic association -> Gamma1 realization ->
surjective-transfer Hecke compatibility -> exchange of the two traces through
the actual subgroup intersection. The already proved native trace tower and
cohomology reindexing suffice; no new general Mackey theorem is needed. -/
namespace Dubon2026
noncomputable section
open CategoryTheory


private theorem trace_tower_of_eq
    {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G)
    (S T : Subgroup G) (hST : S ≤ T) (W : Subgroup T) (hW : W = S.subgroupOf T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)] [Fintype (T ⧸ W)] :
    groupCohomology.map (A := Rep.res S.subtype A)
      ((MulEquiv.subgroupCongr hW).trans (Subgroup.subgroupOfEquivOfLe hST)).toMonoidHom
      (𝟙 (Rep.res W.subtype (Rep.res T.subtype A))) 1 ≫
        subgroupCohomologyTrace (Rep.res T.subtype A) W 1 ≫
          subgroupCohomologyTrace A T 1 =
      subgroupCohomologyTrace A S 1 := by
  subst W
  exact sourceSubgroupH1Trace_tower A S T hST

/-- Swap the two nested subtype witnesses of the same actual intersection,
without changing the ambient group element. -/
def sourceSubgroupIntersectionSwap {G : Type} [Group G] (H U : Subgroup G) :
    U.subgroupOf H ≃* H.subgroupOf U where
  toFun g := ⟨⟨g.val.val, g.property⟩, g.val.property⟩
  invFun g := ⟨⟨g.val.val, g.property⟩, g.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private local instance subgroupQuotientFintype {G : Type} [Group G]
    (H : Subgroup G) [H.FiniteIndex] : Fintype (G ⧸ H) :=
  Subgroup.fintypeQuotientOfFiniteIndex

/-- The intersection trace exchange in the exact nested subgroup types used
by the Hecke base-change square. The actual ambient element is unchanged. -/
theorem sourceSubgroupH1Trace_intersection_swap
    {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (H U : Subgroup G)
    [H.FiniteIndex] [U.FiniteIndex] :
    subgroupCohomologyTrace (Rep.res U.subtype A) (H.subgroupOf U) 1 ≫
      subgroupCohomologyTrace A U 1 =
    groupCohomology.map (sourceSubgroupIntersectionSwap H U).toMonoidHom
      (𝟙 (Rep.res (U.subgroupOf H).subtype (Rep.res H.subtype A))) 1 ≫
      subgroupCohomologyTrace (Rep.res H.subtype A) (U.subgroupOf H) 1 ≫
        subgroupCohomologyTrace A H 1 := by
  let eU := (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right H U).symm).trans
    (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ U ≤ U))
  let eH := (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_left U H).symm).trans
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ U ≤ H))
  let rU := groupCohomology.map (A := Rep.res (H ⊓ U).subtype A) eU.toMonoidHom
    (𝟙 (Rep.res (H.subgroupOf U).subtype (Rep.res U.subtype A))) 1
  let rH := groupCohomology.map (A := Rep.res (H ⊓ U).subtype A) eH.toMonoidHom
    (𝟙 (Rep.res (U.subgroupOf H).subtype (Rep.res H.subtype A))) 1
  let rX := groupCohomology.map (A := Rep.res (H.subgroupOf U).subtype (Rep.res U.subtype A))
    (sourceSubgroupIntersectionSwap H U).toMonoidHom
    (𝟙 (Rep.res (U.subgroupOf H).subtype (Rep.res H.subtype A))) 1
  have hcomp : rU ≫ rX = rH := by
    dsimp only [rU, rX, rH]
    rw [← groupCohomology.map_comp]
    rfl
  haveI : IsIso rU := originalCohomologyReindex_isIso
    (Rep.res (H ⊓ U).subtype A) eU 1
  apply (cancel_epi rU).1
  change rU ≫ subgroupCohomologyTrace (Rep.res U.subtype A) (H.subgroupOf U) 1 ≫
      subgroupCohomologyTrace A U 1 =
    rU ≫ rX ≫ subgroupCohomologyTrace (Rep.res H.subtype A) (U.subgroupOf H) 1 ≫
      subgroupCohomologyTrace A H 1
  rw [← Category.assoc rU rX, hcomp]
  exact (trace_tower_of_eq A (H ⊓ U) U inf_le_right (H.subgroupOf U)
    (Subgroup.inf_subgroupOf_right H U).symm).trans
      (trace_tower_of_eq A (H ⊓ U) H inf_le_left (U.subgroupOf H)
        (Subgroup.inf_subgroupOf_left U H).symm).symm

end
end Dubon2026
