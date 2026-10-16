import Dubon2026.OriginalClassH2InvariantFromGenerator

/-! # Corestriction compatibility of the original normalized class invariants

The existing original full-order restriction theorem makes restriction
surjective. The proved restriction-index normalization therefore determines
the invariant of every corestricted class. This is the corestriction clause
of the finite class-invariant interface used by DUB-17's reverse localization
route; canonical local-fundamental-class normalization remains separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 AddCommGroup.toAddCommMonoid

variable (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]

/-- A full-order original class makes every literal subgroup restriction on class H2 surjective. -/
theorem originalIdeleClass_full_order_restriction_surjective
    (u : groupCohomology (originalIdeleClassRep K E) 2)
    (hu : addOrderOf u = Module.finrank K E) (S : Subgroup Gal(E/K)) :
    Function.Surjective
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom := by
  let r := (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom
  have hs := (originalIdeleClass_full_order_restricts_to_generators K E u hu).2 S
  change Submodule.span ℤ {r u} = ⊤ at hs
  have hr : Submodule.span ℤ {r u} ≤ LinearMap.range r :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ⟨u, rfl⟩)
  rw [hs] at hr
  exact LinearMap.range_eq_top.mp (top_unique hr)

/-- The original restriction-index formula forces corestriction compatibility on every actual subgroup class, using the constructed full-order class and the corestriction-index identity. -/
theorem originalIdeleClass_invariant_corestriction_of_full_order
    (u : groupCohomology (originalIdeleClassRep K E) 2)
    (hu : addOrderOf u = Module.finrank K E) (S : Subgroup Gal(E/K))
    (invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ))
    (invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2 →+ AddCircle (1 : ℚ))
    (hres : ∀ x : groupCohomology (originalIdeleClassRep K E) 2,
      invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom x) =
        S.index • invG x)
    (cor : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2 →+
      groupCohomology (originalIdeleClassRep K E) 2)
    (hcor : ∀ x : groupCohomology (originalIdeleClassRep K E) 2,
      cor ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom x) =
        S.index • x)
    (y : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2) :
    invG (cor y) = invS y := by
  obtain ⟨x, rfl⟩ := originalIdeleClass_full_order_restriction_surjective K E u hu S y
  rw [hcor, map_nsmul, hres]

/-- The genuine original cohomology trace satisfies the normalized class-invariant comparison; its restriction-index identity is supplied by the proved original trace theorem. -/
theorem originalIdeleClass_invariant_original_trace_of_full_order
    (u : groupCohomology (originalIdeleClassRep K E) 2)
    (hu : addOrderOf u = Module.finrank K E) (S : Subgroup Gal(E/K))
    (invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ))
    (invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2 →+ AddCircle (1 : ℚ))
    (hres : ∀ x : groupCohomology (originalIdeleClassRep K E) 2,
      invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom x) =
        S.index • invG x) :
    letI : Fintype (Gal(E/K) ⧸ S) := Fintype.ofFinite _
    ∀ y : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2,
      invG ((subgroupCohomologyTrace (originalIdeleClassRep K E) S 2).hom y) = invS y := by
  letI : Fintype (Gal(E/K) ⧸ S) := Fintype.ofFinite _
  intro y
  exact originalIdeleClass_invariant_corestriction_of_full_order K E u hu S invG invS hres
    (subgroupCohomologyTrace (originalIdeleClassRep K E) S 2).hom.toAddMonoidHom
    (fun x => originalCohomology_trace_restriction_apply (originalIdeleClassRep K E) S 2 x) y

end
end Dubon2026
