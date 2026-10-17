import Dubon2026.OriginalRelationModuleSequence

/-! # The actual relation presentation under field-group restriction

The free-cover map sends the original coefficient generator to the same
generator and maps each group coordinate along the given group homomorphism.
Its literal kernel map is needed to carry a relation morphism to DUB-17's
constructed enlarged stage before applying the proved extension criterion.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {G H : Type} [Group G] [Group H] (f : G →* H) (B : Rep ℤ H)

/-- The actual map of free relation covers under the group map. -/
def originalRelationFreeGroupChange :
    Rep.free ℤ G (Rep.res f B) ⟶ Rep.res f (Rep.free ℤ H B) :=
  Rep.freeLift ℤ G (Rep.res f (Rep.free ℤ H B))
    (fun b => Finsupp.single b (Finsupp.single 1 1))

/-- The canonical map of free covers preserves the original coefficient. -/
theorem originalRelationFreeGroupChange_cover :
    originalRelationFreeGroupChange f B ≫ (Rep.resFunctor f).map (originalRelationFreeCover B) =
      originalRelationFreeCover (Rep.res f B) := by
  apply Rep.free_ext
  intro b
  simp [originalRelationFreeGroupChange, originalRelationFreeCover, Rep.freeLift,
    Representation.freeLift]

/-- The canonical free-cover map restricts to its actual relation kernels. -/
def originalRelationGroupChange :
    originalRelationModule (Rep.res f B) ⟶ Rep.res f (originalRelationModule B) :=
  Rep.ofHom {
    toLinearMap := ((originalRelationFreeGroupChange f B).hom.toLinearMap.comp
      (LinearMap.ker (originalRelationFreeCover (Rep.res f B)).hom.toLinearMap).subtype).codRestrict _
        (fun x => (congrArg (fun m : Rep.free ℤ G (Rep.res f B) ⟶ Rep.res f B => m.hom x.val)
          (originalRelationFreeGroupChange_cover f B)).trans x.property)
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact Rep.hom_comm_apply (originalRelationFreeGroupChange f B) g x.val }

/-- The original relation, free-cover and coefficient maps form the genuine
commuting diagram of relation presentations. -/
def originalRelationGroupChangeSequenceMap :
    originalRelationShortComplex (Rep.res f B) ⟶
      (originalRelationShortComplex B).map (Rep.resFunctor f) where
  τ₁ := originalRelationGroupChange f B
  τ₂ := originalRelationFreeGroupChange f B
  τ₃ := 𝟙 (Rep.res f B)
  comm₁₂ := rfl
  comm₂₃ := by
    simpa only [Category.comp_id] using (originalRelationFreeGroupChange_cover f B)

/-- Restriction along the actual field-group map retains the short exact
original relation presentation. -/
theorem originalRelationGroupChange_shortExact :
    ((originalRelationShortComplex B).map (Rep.resFunctor f)).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (fun x y h => Subtype.ext h)
    epi_g := (Rep.epi_iff_surjective _).mpr (originalRelationFreeCover_surjective B) }
  apply (((originalRelationShortComplex B).map (Rep.resFunctor f)).exact_map_iff_of_faithful
    (forget₂ (Rep ℤ G) (ModuleCat ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact Submodule.range_subtype _

end
end Dubon2026
