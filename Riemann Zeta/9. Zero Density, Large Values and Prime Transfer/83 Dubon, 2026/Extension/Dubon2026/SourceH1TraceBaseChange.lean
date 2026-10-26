import Dubon2026.SourceShapiroH1PullbackNaturality
import Dubon2026.SourceShapiroH1CosetTrace

/-! DUB-17/18 -> all-weight adic association -> Gamma1 transfer/Hecke
compatibility -> exact native H1 trace base change. The coefficient-level
trace identity and proved native Shapiro naturality discharge the
cohomological comparison; only actual group-level coset surjectivity is used. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R D G : Type} [CommRing R] [Group D] [Group G]
  (A : Rep.{0} R G) (φ : D →* G) (S : Subgroup G)
  [Fintype (G ⧸ S)] [Fintype (D ⧸ S.comap φ)]

/-- The cohomology map of the actual coinduced trace commutes with group
pullback through the proved coefficient pullback morphism. -/
theorem sourceCoinducedH1Trace_pullback
    (hcosets : Function.Surjective (subgroupComapCosetMap φ S)) :
    (groupCohomology.functor R G 1).map (coinducedCosetTrace A S) ≫
        groupCohomology.map φ (𝟙 (Rep.res φ A)) 1 =
      groupCohomology.map φ (sourceCoinducedTracePullback A φ S) 1 ≫
        (groupCohomology.functor R D 1).map
          (coinducedCosetTrace (Rep.res φ A) (S.comap φ)) := by
  change groupCohomology.map (MonoidHom.id G) (coinducedCosetTrace A S) 1 ≫
      groupCohomology.map φ (𝟙 (Rep.res φ A)) 1 =
    groupCohomology.map φ (sourceCoinducedTracePullback A φ S) 1 ≫
      groupCohomology.map (MonoidHom.id D)
        (coinducedCosetTrace (Rep.res φ A) (S.comap φ)) 1
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  congr 1
  exact sourceCoinducedTracePullback_trace A φ S hcosets

/-- The full native H1 subgroup trace obeys base change whenever the
actual subgroup-preimage coset map is onto. -/
theorem sourceSubgroupH1Trace_pullback
    (hcosets : Function.Surjective (subgroupComapCosetMap φ S)) :
    subgroupCohomologyTrace A S 1 ≫ groupCohomology.map φ (𝟙 (Rep.res φ A)) 1 =
      groupCohomology.map (sourceTracePullbackSubgroupHom φ S)
        (𝟙 (Rep.res (S.comap φ).subtype (Rep.res φ A))) 1 ≫
          subgroupCohomologyTrace (Rep.res φ A) (S.comap φ) 1 := by
  have hnat := sourceShapiroH1_pullback_naturality A φ S
  apply (cancel_epi (groupCohomology.coindIso (Rep.res S.subtype A) 1).hom).1
  unfold subgroupCohomologyTrace
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_assoc]
  calc
    _ = groupCohomology.map φ (sourceCoinducedTracePullback A φ S) 1 ≫
        (groupCohomology.functor R D 1).map
          (coinducedCosetTrace (Rep.res φ A) (S.comap φ)) :=
      sourceCoinducedH1Trace_pullback A φ S hcosets
    _ = ((groupCohomology.coindIso (Rep.res S.subtype A) 1).hom ≫
          groupCohomology.map (sourceTracePullbackSubgroupHom φ S)
            (𝟙 (Rep.res (S.comap φ).subtype (Rep.res φ A))) 1) ≫
        ((groupCohomology.coindIso (Rep.res (S.comap φ).subtype (Rep.res φ A)) 1).inv ≫
          (groupCohomology.functor R D 1).map
            (coinducedCosetTrace (Rep.res φ A) (S.comap φ))) := by
      rw [← hnat]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := Category.assoc _ _ _

/-- The same base-change identity holds for the exact literal H1 trace
used by the original Hecke operators, by the proved convention bridge. -/
theorem sourceHeckeH1Trace_pullback
    (hcosets : Function.Surjective (subgroupComapCosetMap φ S)) :
    (groupCohomology.map φ (𝟙 (Rep.res φ A)) 1).hom.comp (sourceHeckeH1Trace A S) =
      (sourceHeckeH1Trace (Rep.res φ A) (S.comap φ)).comp
        (groupCohomology.map (sourceTracePullbackSubgroupHom φ S)
          (𝟙 (Rep.res (S.comap φ).subtype (Rep.res φ A))) 1).hom := by
  rw [sourceHeckeH1Trace_eq_subgroupTrace, sourceHeckeH1Trace_eq_subgroupTrace]
  exact congrArg ModuleCat.Hom.hom (sourceSubgroupH1Trace_pullback A φ S hcosets)

end
end Dubon2026
