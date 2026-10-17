import Dubon2026.OriginalArbitraryFreeCoinduced

/-! # The actual arbitrary relation presentation on every subgroup

The fundamental arithmetic coefficient is infinite, so retain its
literal free cover and kernel with arbitrary index. Restriction changes
only the action. This is the exact sequence required to derive kernel
vanishing on DUB-17's lattice/internal-Hom duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] (B : Rep ℤ G)

/-- The actual arbitrary-index relation presentation remains short exact on every original subgroup. -/
theorem originalArbitraryRelationSubgroup_shortExact (S : Subgroup G) :
    ((originalRelationShortComplex B).map (Rep.resFunctor S.subtype)).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (fun x y h => Subtype.ext h)
    epi_g := (Rep.epi_iff_surjective _).mpr (originalRelationFreeCover_surjective B) }
  apply (((originalRelationShortComplex B).map (Rep.resFunctor S.subtype)).exact_map_iff_of_faithful
    (forget₂ (Rep ℤ S) (ModuleCat ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact Submodule.range_subtype _

end
end Dubon2026
