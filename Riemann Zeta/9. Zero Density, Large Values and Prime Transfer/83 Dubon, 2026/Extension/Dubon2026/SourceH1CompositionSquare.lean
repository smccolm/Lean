import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! DUB-17/18 -> original Gamma1 diamond transfer square. Reuse the
degree-one group/coefficient comparison argument already used in
SourceGammaOneHeckePullbackSquare, exposing exactly the required square.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

private theorem map_eq_of_group_and_coeff
    {R G H : Type} [CommRing R] [Group G] [Group H]
    {A : Rep R G} {B : Rep R H} {f g : H →* G}
    (hfg : f = g) (a : Rep.res f A ⟶ B) (b : Rep.res g A ⟶ B)
    (hab : a.hom.toLinearMap = b.hom.toLinearMap) :
    groupCohomology.map f a 1 = groupCohomology.map g b 1 := by
  subst g
  have he : a = b := by
    apply Rep.hom_ext
    ext x
    exact LinearMap.congr_fun hab x
  rw [he]

theorem sourceH1Composition_square
    {R G H K L : Type} [CommRing R] [Group G] [Group H] [Group K] [Group L]
    {A : Rep R G} {B : Rep R H} {C : Rep R K} {D : Rep R L}
    (f : H →* G) (g : K →* H) (u : L →* G) (v : K →* L)
    (a : Rep.res f A ⟶ B) (b : Rep.res g B ⟶ C)
    (c : Rep.res u A ⟶ D) (d : Rep.res v D ⟶ C)
    (hfg : f.comp g = u.comp v)
    (hab : (((Rep.resFunctor g).map a) ≫ b).hom.toLinearMap =
      (((Rep.resFunctor v).map c) ≫ d).hom.toLinearMap) :
    groupCohomology.map f a 1 ≫ groupCohomology.map g b 1 =
      groupCohomology.map u c 1 ≫ groupCohomology.map v d 1 := by
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  exact map_eq_of_group_and_coeff hfg _ _ hab

end
end Dubon2026
