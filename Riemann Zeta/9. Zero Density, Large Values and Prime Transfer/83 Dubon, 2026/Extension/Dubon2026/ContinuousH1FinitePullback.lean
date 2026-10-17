import Dubon2026.ContinuousAlgebraicH1Map
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Actual finite-stage H1 pullbacks have continuous representatives

Reuse the pinned cocycle surjection and literal cocycle group-change map.
Continuity follows from the discrete finite-stage group and the actual
continuous restriction. This supplies the H1 input needed to evaluate
DUB-17's source-class cup on the descended finite obstruction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace H] [DiscreteTopology H]
  (π : G →* H) (hπ : Continuous π) (A : Rep R H) (B : Rep R G)
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

include hπ in
omit [IsTopologicalGroup G] in
/-- Every original algebraic H1 class at the discrete stage has an actual
continuous pullback with precisely the prescribed group and coefficient map. -/
theorem continuousH1_exists_finite_pullback (φ : Rep.res π A ⟶ B)
    (y : groupCohomology A 1) :
    ∃ x : ContinuousRepresentationH1 B hB,
      continuousH1ToAlgebraic B hB x = groupCohomology.map π φ 1 y := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H1π A)).mp inferInstance y
  let w := groupCohomology.mapCocycles₁ π φ z
  have hw : Continuous (fun g => w g) := by
    change Continuous (fun g => φ.hom (z (π g)))
    exact (continuous_of_discreteTopology : Continuous (fun h : H => φ.hom (z h))).comp hπ
  let c : continuousRepresentationCocyclesOne B := ⟨w, hw⟩
  refine ⟨(continuousRepresentationCoboundariesOne B hB).mkQ c, ?_⟩
  exact (groupCohomology.H1π_comp_map_apply π φ z).symm

include hπ in
omit [IsTopologicalGroup G] in
/-- The same continuous representative realizes the separate original
group pullback and coefficient map used in the arithmetic tower diagram. -/
theorem continuousH1_exists_finite_pullback_factor (φ : Rep.res π A ⟶ B)
    (y : groupCohomology A 1) :
    ∃ x : ContinuousRepresentationH1 B hB,
      continuousH1ToAlgebraic B hB x =
        groupCohomology.map (MonoidHom.id G) φ 1
          (groupCohomology.map π (𝟙 (Rep.res π A)) 1 y) := by
  obtain ⟨x, hx⟩ := continuousH1_exists_finite_pullback π hπ A B hB φ y
  refine ⟨x, hx.trans ?_⟩
  have hm : groupCohomology.map π φ 1 =
      groupCohomology.map π (𝟙 (Rep.res π A)) 1 ≫
        groupCohomology.map (MonoidHom.id G) φ 1 := by
    simpa only [MonoidHom.comp_id, CategoryTheory.Functor.map_id, Category.id_comp] using
      (groupCohomology.map_comp π (MonoidHom.id G) (𝟙 (Rep.res π A)) φ 1)
  exact congrArg (fun m => m.hom y) hm

end
end Dubon2026
