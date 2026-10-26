import Dubon2026.SourceCoinducedTowerTrace
import Dubon2026.SourceShapiroH1Tower
import Dubon2026.SourceShapiroH1CosetTrace

/-! DUB-17/18 -> original all-weight adic association -> actual Gamma1
surjective-transfer Hecke compatibility -> native H1 trace composition.
The genuine coefficient isomorphism, complete finite trace calculation
and existing Shapiro coefficient naturality discharge this obligation. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G]
  (A : Rep.{0} R G) (S T : Subgroup G) (hST : S ≤ T)
  [Fintype (G ⧸ S)] [Fintype (G ⧸ T)] [Fintype (T ⧸ S.subgroupOf T)]

/-- Native H1 trace through the actual intermediate subgroup is the
original direct trace, retaining the canonical nested-subgroup reindexing. -/
theorem sourceSubgroupH1Trace_tower :
    groupCohomology.map (Subgroup.subgroupOfEquivOfLe hST).toMonoidHom
      (𝟙 (Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A))) 1 ≫
        subgroupCohomologyTrace (Rep.res T.subtype A) (S.subgroupOf T) 1 ≫
          subgroupCohomologyTrace A T 1 =
      subgroupCohomologyTrace A S 1 := by
  let B := Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A)
  let C := Rep.coind (S.subgroupOf T).subtype B
  let e := (groupCohomology.functor R G 1).mapIso (sourceCoinducedTowerIso A S T hST)
  let ss := groupCohomology.coindIso (Rep.res S.subtype A) 1
  let st := groupCohomology.coindIso C 1
  let su := groupCohomology.coindIso B 1
  have hsh : e.hom ≫ ss.hom ≫
      groupCohomology.map (Subgroup.subgroupOfEquivOfLe hST).toMonoidHom
        (𝟙 B) 1 = st.hom ≫ su.hom :=
    sourceShapiroH1_tower A S T hST
  have hlift := originalCohomologyTrace_coinduced_lift T
    (coinducedCosetTrace (Rep.res T.subtype A) (S.subgroupOf T)) 1
  have hinner : su.hom ≫
      subgroupCohomologyTrace (Rep.res T.subtype A) (S.subgroupOf T) 1 =
      (groupCohomology.functor R T 1).map
        (coinducedCosetTrace (Rep.res T.subtype A) (S.subgroupOf T)) := by
    unfold subgroupCohomologyTrace
    dsimp only [su, B]
    simp only [Iso.hom_inv_id_assoc]
  have houter : st.hom ≫ (groupCohomology.functor R T 1).map
      (coinducedCosetTrace (Rep.res T.subtype A) (S.subgroupOf T)) ≫
        subgroupCohomologyTrace A T 1 =
      (groupCohomology.functor R G 1).map
        ((Rep.coindFunctor R T.subtype).map
          (coinducedCosetTrace (Rep.res T.subtype A) (S.subgroupOf T)) ≫
            coinducedCosetTrace A T) := by
    erw [Category.assoc, ← hlift]
    exact Iso.hom_inv_id_assoc st _
  have hfinal : ss.hom ≫ subgroupCohomologyTrace A S 1 =
      (groupCohomology.functor R G 1).map (coinducedCosetTrace A S) := by
    unfold subgroupCohomologyTrace
    dsimp only [ss]
    simp only [Iso.hom_inv_id_assoc]
  have hcomp := congrArg (fun z =>
    z ≫ subgroupCohomologyTrace (Rep.res T.subtype A) (S.subgroupOf T) 1 ≫
      subgroupCohomologyTrace A T 1) hsh
  simp only [Category.assoc] at hcomp houter
  erw [Category.assoc st.hom su.hom] at hcomp
  erw [← Category.assoc su.hom, hinner, houter] at hcomp
  rw [← sourceCoinducedTowerTrace_comp A S T hST] at hcomp
  erw [Functor.map_comp] at hcomp
  apply (cancel_epi (e.hom ≫ ss.hom)).1
  simp only [Category.assoc]
  erw [hfinal]
  exact hcomp

/-- The exact literal trace used by the original Hecke operators obeys
the same derived composition law on full native H1. -/
theorem sourceHeckeH1Trace_tower :
    (sourceHeckeH1Trace A T).comp
      ((sourceHeckeH1Trace (Rep.res T.subtype A) (S.subgroupOf T)).comp
        (groupCohomology.map (Subgroup.subgroupOfEquivOfLe hST).toMonoidHom
          (𝟙 (Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A))) 1).hom) =
      sourceHeckeH1Trace A S := by
  rw [sourceHeckeH1Trace_eq_subgroupTrace, sourceHeckeH1Trace_eq_subgroupTrace,
    sourceHeckeH1Trace_eq_subgroupTrace]
  exact congrArg ModuleCat.Hom.hom (sourceSubgroupH1Trace_tower A S T hST)

end
end Dubon2026
