import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Reindexing the original cochain complex along an actual group isomorphism -/

namespace Dubon2026
noncomputable section

open CategoryTheory

/-- The original cochain pullback along an actual group isomorphism is an
isomorphism in every degree. Its coefficient map is the identity. -/
theorem originalCohomologyReindex_isIso
    {k G H : Type} [CommRing k] [Group G] [Group H]
    (A : Rep.{0} k H) (e : G ≃* H) (n : ℕ) :
    IsIso (groupCohomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) n) := by
  let f := groupCohomology.cochainsMap e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A))
  haveI (i : ℕ) : Mono (f.f i) :=
    groupCohomology.cochainsMap_f_map_mono e.toMonoidHom _ e.surjective i
  haveI (i : ℕ) : Epi (f.f i) :=
    groupCohomology.cochainsMap_f_map_epi e.toMonoidHom _ e.injective i
  haveI (i : ℕ) : IsIso (f.f i) := isIso_of_mono_of_epi (f.f i)
  haveI : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  change IsIso (HomologicalComplex.homologyMap f n)
  infer_instance

/-- Actual cohomology isomorphism obtained by pulling back cochains along
the given group isomorphism, keeping the same coefficient module and action. -/
def originalCohomologyReindex
    {k G H : Type} [CommRing k] [Group G] [Group H]
    (A : Rep.{0} k H) (e : G ≃* H) (n : ℕ) :
    groupCohomology A n ≅ groupCohomology (Rep.res e.toMonoidHom A) n :=
  @asIso _ _ _ _ (groupCohomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) n)
    (originalCohomologyReindex_isIso A e n)

end
end Dubon2026
