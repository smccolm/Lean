import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # The actual integral relation module and its projective presentation

The finite class/Ext route to DUB-17's reverse H1 localization uses the
kernel of the free representation on the original coefficient elements.
The pinned free representation and projectivity theorem are reused; the
literal cover, kernel and short exact sequence are retained. No extension
criterion or duality statement is assumed here.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] (B : Rep ℤ G)

/-- The actual free integral representation maps each basis generator to its original coefficient. -/
def originalRelationFreeCover : Rep.free ℤ G B ⟶ B :=
  Rep.freeLift ℤ G B (fun b => b)

/-- The literal kernel of the original free cover, with the inherited Galois action. -/
abbrev originalRelationModule : Rep ℤ G :=
  Rep.of (Representation.subrepresentation (Rep.free ℤ G B).ρ
    (LinearMap.ker (originalRelationFreeCover B).hom.toLinearMap) fun g x hx => by
      change (originalRelationFreeCover B).hom x = 0 at hx
      change (originalRelationFreeCover B).hom ((Rep.free ℤ G B).ρ g x) = 0
      rw [Rep.hom_comm_apply, hx, map_zero])

/-- The literal kernel inclusion into the original free representation. -/
def originalRelationInclusion : originalRelationModule B ⟶ Rep.free ℤ G B :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

/-- The original cover is surjective because each original coefficient is the image of its basis generator. -/
theorem originalRelationFreeCover_surjective : Function.Surjective (originalRelationFreeCover B).hom := by
  intro b
  refine ⟨Finsupp.single b (MonoidAlgebra.single 1 1), ?_⟩
  simp [originalRelationFreeCover, Rep.freeLift, Representation.freeLift]
  exact (int_smul_eq_zsmul B.hV2 1 b).trans (one_zsmul b)

/-- The genuine relation module, free cover and original coefficient form the intended coefficient complex. -/
def originalRelationShortComplex : ShortComplex (Rep ℤ G) where
  X₁ := originalRelationModule B
  X₂ := Rep.free ℤ G B
  X₃ := B
  f := originalRelationInclusion B
  g := originalRelationFreeCover B
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.property))

/-- The actual integral relation presentation is short exact, with no short-exactness hypothesis. -/
theorem originalRelationShortComplex_shortExact : (originalRelationShortComplex B).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (fun x y h => Subtype.ext h)
    epi_g := (Rep.epi_iff_surjective _).mpr (originalRelationFreeCover_surjective B) }
  apply ((originalRelationShortComplex B).exact_map_iff_of_faithful
    (forget₂ (Rep ℤ G) (ModuleCat ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact Submodule.range_subtype _

/-- The actual middle term is projective by the pinned free-representation theorem. -/
theorem originalRelationFreeCover_projective : Projective (originalRelationShortComplex B).X₂ := by
  change Projective (Rep.free ℤ G B)
  infer_instance

end
end Dubon2026
