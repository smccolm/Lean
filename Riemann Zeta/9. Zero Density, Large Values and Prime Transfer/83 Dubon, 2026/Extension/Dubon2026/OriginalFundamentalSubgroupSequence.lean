import Dubon2026.OriginalFundamentalClassKilling

/-! # The actual fundamental extension on every original subgroup

The literal splitting sequence remains exact after restriction, and
pinned restriction naturality carries its class-killing identity to the
same restricted fundamental class. These are required inputs to the
subgroup vanishing deduction in DUB-17's finite class/Ext argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G]
  (C : Rep k G) (φ : groupCohomology.cocycles₂ C) (S : Subgroup G)

/-- The literal fundamental-class coefficient sequence is short exact on every actual subgroup. -/
theorem originalFundamentalSubgroup_shortExact :
    ((originalFundamentalSplittingShortComplex C φ).map (Rep.resFunctor S.subtype)).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr LinearMap.inl_injective
    epi_g := (Rep.epi_iff_surjective _).mpr (fun x => ⟨(0, x), rfl⟩) }
  apply (((originalFundamentalSplittingShortComplex C φ).map (Rep.resFunctor S.subtype)).exact_map_iff_of_faithful
    (forget₂ (Rep k S) (ModuleCat k))).mp
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro v hv
  exact ⟨v.1, Prod.ext rfl hv.symm⟩

/-- Actual restriction naturality carries the explicit class-killing identity to every original subgroup. -/
theorem originalFundamentalSubgroup_class_zero :
    (groupCohomology.map (MonoidHom.id S)
      ((Rep.resFunctor S.subtype).map (originalFundamentalSplittingInclusion C φ)) 2)
      ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2)
        (groupCohomology.H2π C φ)) = 0 := by
  have hn := congrArg
    (fun f : groupCohomology C 2 ⟶
      groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2 =>
        f (groupCohomology.H2π C φ))
    ((groupCohomology.resNatTrans k S.subtype 2).naturality
      (originalFundamentalSplittingInclusion C φ))
  change (groupCohomology.map S.subtype
      (𝟙 (Rep.res S.subtype (originalFundamentalSplittingModule C φ))) 2)
      ((groupCohomology.map (MonoidHom.id G) (originalFundamentalSplittingInclusion C φ) 2)
        (groupCohomology.H2π C φ)) = _ at hn
  rw [originalFundamentalSplittingInclusion_class_zero, map_zero] at hn
  exact hn.symm

end
end Dubon2026
