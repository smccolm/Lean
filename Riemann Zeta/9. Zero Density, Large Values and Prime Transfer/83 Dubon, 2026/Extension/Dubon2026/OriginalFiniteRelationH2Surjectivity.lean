import Dubon2026.OriginalFiniteFundamentalH2Surjectivity
import Dubon2026.OriginalFiniteRelationModule
import Dubon2026.OriginalRelationExtensionObstruction

/-! # Every actual finite relation obstruction is realized

The original finite coefficient has finite H1, and its genuine free-cover
boundary identifies this with H2 of the actual integral relation module.
The proved finite H2-map surjectivity therefore realizes every H1-to-H2
functional by an actual relation morphism. This discharges the surjectivity
input to DUB-17's finite relation dévissage; extension remains separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (B : Rep.{0} ℤ G) [Finite B]

/-- Actual H1 of a finite original coefficient over a finite group is
finite, as the image of its literal finite cocycle module. -/
theorem originalFiniteCoefficient_first_finite : Finite (groupCohomology B 1) := by
  letI : Finite (groupCohomology.cocycles₁ B) :=
    Finite.of_injective (fun c : groupCohomology.cocycles₁ B => c.val) Subtype.val_injective
  exact Finite.of_surjective (groupCohomology.H1π B)
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Actual H2 of the original finite relation lattice is finite through
the genuine connecting isomorphism. -/
theorem originalFiniteRelation_second_finite :
    Finite (groupCohomology (originalRelationModule B) 2) := by
  letI := originalFiniteCoefficient_first_finite B
  let δ : groupCohomology B 1 ⟶ groupCohomology (originalRelationModule B) 2 :=
    groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl
  letI : IsIso δ := originalRelationConnecting_isIso B
  exact Finite.of_surjective δ
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Every actual H1-to-H2 functional is the genuine connecting
obstruction of an original relation morphism. -/
theorem originalFiniteFundamental_relation_obstruction_surjective
    (C : Rep.{0} ℤ G) [Finite (groupCohomology C 2)] [IsAddCyclic (groupCohomology C 2)]
    (φ : groupCohomology.cocycles₂ C)
    (ho : addOrderOf (groupCohomology.H2π C φ) = Fintype.card G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology
        (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
      Limits.IsZero (groupCohomology
        (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2)) :
    Function.Surjective (originalRelationExtensionObstruction B C) := by
  letI := originalRelationModule_finite B
  letI := originalRelationModule_free B
  letI := originalFiniteRelation_second_finite B
  let δ : groupCohomology B 1 ⟶ groupCohomology (originalRelationModule B) 2 :=
    groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl
  letI : IsIso δ := originalRelationConnecting_isIso B
  let e := asIso δ
  intro t
  obtain ⟨χ, hχ⟩ := originalFiniteFundamental_h2_map_surjective
    (originalRelationModule B) C φ ho h (e.inv ≫ t)
  change (groupCohomology.functor ℤ G 2).map χ = e.inv ≫ t at hχ
  refine ⟨χ, ?_⟩
  change e.hom ≫ (groupCohomology.functor ℤ G 2).map χ = t
  rw [hχ]
  exact e.hom_inv_id_assoc t

end
end Dubon2026
