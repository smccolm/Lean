import Dubon2026.OriginalNestedSubgroupNorms
import Dubon2026.OriginalFundamentalTwoDegreeVanishing
import Dubon2026.OriginalGroupCohomologyReindex

/-! # Derive the actual subgroup fundamental data

DUB-17's induced relation extension uses the original coefficient
restricted to its actual normal kernel. The image-subgroup equivalence
transports the existing class-system cardinality and generator data.
The restricted fundamental cocycle and its two-degree vanishing are
then derived, without a separately supplied subgroup class system.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] (C : Rep.{0} ℤ G)

/-- Nested restriction preserves the literal image subgroup's H2
cardinality, with the actual subgroup cardinality on the right. -/
theorem originalNestedSubgroup_second_card (N : Subgroup G) (T : Subgroup N)
    (hc : Nat.card (groupCohomology (Rep.res (T.map N.subtype).subtype C) 2) =
      Nat.card (T.map N.subtype)) :
    Nat.card (groupCohomology (Rep.res T.subtype (Rep.res N.subtype C)) 2) = Nat.card T := by
  let e := T.equivMapOfInjective N.subtype N.subtype_injective
  let E := originalCohomologyReindex (Rep.res (T.map N.subtype).subtype C) e 2
  exact (Nat.card_congr E.toLinearEquiv.toEquiv).symm.trans
    (hc.trans (Nat.card_congr e.toEquiv).symm)

/-- Restricting the original fundamental generator twice gives the
generator transported from the actual image subgroup. -/
theorem originalNestedSubgroup_second_generator
    (u : groupCohomology C 2) (N : Subgroup G) (T : Subgroup N)
    (hg : Submodule.span ℤ
      {(groupCohomology.map (T.map N.subtype).subtype
        (𝟙 (Rep.res (T.map N.subtype).subtype C)) 2).hom u} = ⊤) :
    Submodule.span ℤ
      {(groupCohomology.map T.subtype (𝟙 (Rep.res T.subtype (Rep.res N.subtype C))) 2).hom
        ((groupCohomology.map N.subtype (𝟙 (Rep.res N.subtype C)) 2).hom u)} = ⊤ := by
  let e := T.equivMapOfInjective N.subtype N.subtype_injective
  let D := Rep.res (T.map N.subtype).subtype C
  let E := originalCohomologyReindex D e 2
  have he : (groupCohomology.map (T.map N.subtype).subtype (𝟙 D) 2) ≫ E.hom =
      groupCohomology.map N.subtype (𝟙 (Rep.res N.subtype C)) 2 ≫
        groupCohomology.map T.subtype (𝟙 (Rep.res T.subtype (Rep.res N.subtype C))) 2 := by
    change groupCohomology.map (T.map N.subtype).subtype (𝟙 D) 2 ≫
      groupCohomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom D)) 2 = _
    rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
    rfl
  apply (Submodule.span_singleton_eq_top_iff ℤ _).mpr
  intro z
  obtain ⟨w, rfl⟩ := E.toLinearEquiv.surjective z
  obtain ⟨a, ha⟩ := (Submodule.span_singleton_eq_top_iff ℤ _).mp hg w
  refine ⟨a, ?_⟩
  have h := congrArg (fun f => f.hom u) he
  change E.hom.hom ((groupCohomology.map (T.map N.subtype).subtype (𝟙 D) 2).hom u) =
    (groupCohomology.map T.subtype (𝟙 (Rep.res T.subtype (Rep.res N.subtype C))) 2).hom
      ((groupCohomology.map N.subtype (𝟙 (Rep.res N.subtype C)) 2).hom u) at h
  rw [← h]
  exact (E.hom.hom.map_smul a _).symm.trans (congrArg E.hom.hom ha)

variable [Finite G]

/-- The original full class system constructs a restricted fundamental
cocycle of full subgroup order and derives every subgroup H1/H2 vanishing
condition for its actual splitting coefficient. -/
theorem originalRestrictedFundamentalData_exists
    (u : groupCohomology C 2)
    (h1 : ∀ H : Subgroup G, Limits.IsZero (groupCohomology (Rep.res H.subtype C) 1))
    (hc : ∀ H : Subgroup G, Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (hg : ∀ H : Subgroup G, Submodule.span ℤ
      {(groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype C)) 2).hom u} = ⊤)
    (N : Subgroup G) [Fintype N] :
    ∃ φ : groupCohomology.cocycles₂ (Rep.res N.subtype C),
      addOrderOf (groupCohomology.H2π (Rep.res N.subtype C) φ) = Fintype.card N ∧
      ∀ T : Subgroup N,
        Limits.IsZero (groupCohomology (Rep.res T.subtype
          (originalFundamentalSplittingModule (Rep.res N.subtype C) φ)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res T.subtype
          (originalFundamentalSplittingModule (Rep.res N.subtype C) φ)) 2) := by
  let CN := Rep.res N.subtype C
  let v := (groupCohomology.map N.subtype (𝟙 CN) 2).hom u
  letI : Finite (groupCohomology CN 2) := Nat.finite_of_card_ne_zero
    ((hc N).trans_ne Nat.card_pos.ne')
  have hv : ∀ z : groupCohomology CN 2, z ∈ AddSubgroup.zmultiples v := by
    intro z
    obtain ⟨a, ha⟩ := (Submodule.span_singleton_eq_top_iff ℤ v).mp (hg N) z
    refine ⟨a, ?_⟩
    exact (int_smul_eq_zsmul (inferInstance : Module ℤ (groupCohomology CN 2)) a v).symm.trans ha
  have ho : addOrderOf v = Fintype.card N :=
    (addOrderOf_eq_card_of_forall_mem_zmultiples hv).trans ((hc N).trans Nat.card_eq_fintype_card)
  obtain ⟨φ, hφ⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π CN)).mp inferInstance v
  refine ⟨φ, hφ ▸ ho, ?_⟩
  intro T
  letI : Fintype T := Fintype.ofFinite T
  apply originalFundamentalSubgroup_first_second_zero CN φ T
    (originalNestedSubgroup_zero C N T 1 (h1 _))
    ((originalNestedSubgroup_second_card C N T (hc _)).trans Nat.card_eq_fintype_card)
  rw [hφ]
  exact originalNestedSubgroup_second_generator C u N T (hg _)

end
end Dubon2026
