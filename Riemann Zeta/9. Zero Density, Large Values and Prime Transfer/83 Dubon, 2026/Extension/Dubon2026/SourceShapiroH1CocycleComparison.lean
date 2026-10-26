import Dubon2026.CoinducedShapiroOneHomotopy
import Dubon2026.OriginalShapiroRestriction
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! DUB-17/18 -> original all-weight adic association -> Gamma1 geometric
Hecke comparison -> the native Shapiro map and the already proved explicit
degree-one lift. Reuse the existing cocycle homotopy rather than constructing
another resolution or assuming a comparison. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- The existing explicit lift restricted to the actual subgroup cocycles. -/
def sourceShapiroLiftCocycles :
    groupCohomology.cocycles₁ (Rep.res S.subtype A) →ₗ[R]
      groupCohomology.cocycles₁ (Rep.coind S.subtype (Rep.res S.subtype A)) :=
  (coinducedShapiroOne A S).restrict
    (fun c hc => coinducedShapiroOne_mem_cocycles A S ⟨c, hc⟩)

/-- Literal restriction and identity evaluation on genuine coinduced cocycles. -/
def sourceShapiroEvaluationCocycles :
    groupCohomology.cocycles₁ (Rep.coind S.subtype (Rep.res S.subtype A)) →ₗ[R]
      groupCohomology.cocycles₁ (Rep.res S.subtype A) :=
  (groupCohomology.mapCocycles₁ S.subtype
    ((Rep.resCoindHomEquiv S.subtype
      (Rep.coind S.subtype (Rep.res S.subtype A)) (Rep.res S.subtype A)).symm (𝟙 _))).hom

/-- The native Shapiro homomorphism has exactly the literal evaluation formula
on actual degree-one classes. -/
theorem sourceShapiroH1_hom_cocycle
    (c : groupCohomology.cocycles₁ (Rep.coind S.subtype (Rep.res S.subtype A))) :
    (groupCohomology.coindIso (Rep.res S.subtype A) 1).hom
      (groupCohomology.H1π _ c) =
        groupCohomology.H1π _ (sourceShapiroEvaluationCocycles A S c) := by
  let ev := (Rep.resCoindHomEquiv S.subtype
    (Rep.coind S.subtype (Rep.res S.subtype A)) (Rep.res S.subtype A)).symm (𝟙 _)
  have h := OriginalShapiroRestriction.originalShapiroIso_eq_restriction_eval
    (Rep.res S.subtype A) 1 ev (fun _ => rfl)
  rw [← groupCohomology.map_comp] at h
  rw [h]
  exact groupCohomology.H1π_comp_map_apply S.subtype ev c

/-- The already proved explicit cocycle homotopy gives the native H1
inverse identity without any assumed comparison. -/
theorem sourceShapiroH1_evaluation_lift
    (c : groupCohomology.cocycles₁ (Rep.coind S.subtype (Rep.res S.subtype A))) :
    groupCohomology.H1π _
      (sourceShapiroLiftCocycles A S (sourceShapiroEvaluationCocycles A S c)) =
        groupCohomology.H1π _ c := by
  apply (groupCohomology.H1π_eq_iff _ _).mpr
  exact ⟨coinducedShapiroOneHomotopy A S c,
    (coinducedShapiroOne_evaluation_sub A S c).symm⟩

end
end Dubon2026
