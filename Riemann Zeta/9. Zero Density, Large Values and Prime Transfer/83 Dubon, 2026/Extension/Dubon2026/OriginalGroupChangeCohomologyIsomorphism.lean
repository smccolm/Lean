import Dubon2026.OriginalGroupCohomologyReindex

/-! # Actual coefficient isomorphisms and group isomorphisms preserve cohomology -/

namespace Dubon2026
noncomputable section

open CategoryTheory

/-- Pulling original cochains back along an actual group isomorphism,
then applying an actual coefficient isomorphism, is an isomorphism on
the original cohomology in every degree. -/
theorem originalGroupChangeCohomology_isIso
    {k G H : Type} [CommRing k] [Group G] [Group H]
    (A : Rep.{0} k H) (B : Rep.{0} k G) (e : G ≃* H)
    (φ : Rep.res e.toMonoidHom A ⟶ B) [IsIso φ] (n : ℕ) :
    IsIso (groupCohomology.map e.toMonoidHom φ n) := by
  let f := groupCohomology.cochainsMap e.toMonoidHom φ
  haveI (i : ℕ) : Mono (f.f i) :=
    groupCohomology.cochainsMap_f_map_mono e.toMonoidHom φ e.surjective i
  haveI (i : ℕ) : Epi (f.f i) :=
    groupCohomology.cochainsMap_f_map_epi e.toMonoidHom φ e.injective i
  haveI (i : ℕ) : IsIso (f.f i) := isIso_of_mono_of_epi (f.f i)
  haveI : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  change IsIso (HomologicalComplex.homologyMap f n)
  infer_instance

end
end Dubon2026
