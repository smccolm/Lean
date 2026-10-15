/-
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0; see ../../Dependencies/AnthropicFLTReuse/LICENSE.
Adapted from anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero.lean.
Changes: native Dubon inflation-restriction imports, named theorem, and module documentation.
-/
import Dubon2026.OriginalSecondCohomologyInflationRestriction

/-! # Original H2 generator transfer

This is the algebraic transfer step for DUB-17's class-formation invariant
construction. The arithmetic auxiliary generator and its vanishing
restriction remain explicit upstream obligations. The target H2 generator
is derived using the actual inflation/restriction maps, not assumed.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Limits groupCohomology Rep

/-- The original inflation-restriction sequence transfers an auxiliary finite-order cyclic class to a generator of the target quotient H2. -/
theorem originalH2_generator_from_inflated_cyclic_class
    {k Γ : Type} [CommRing k] [Group Γ] [Fintype Γ] (C : Rep k Γ) (S T : Subgroup Γ) [S.Normal] [T.Normal]
    [Fintype (Γ ⧸ S)]
    (hS1 : IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (hT1 : IsZero (groupCohomology (Rep.res T.subtype C) 1))
    (n' : ℕ) (hn : Fintype.card (Γ ⧸ S) ∣ n') (hn'0 : n' ≠ 0)
    (u' : groupCohomology (C.quotientToInvariants T) 2) (hu' : addOrderOf u' = n')
    (hres : (map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom
        ((n' / Fintype.card (Γ ⧸ S)) •
          (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
            (ofHom (C.ρ.quotientToInvariants_lift T)) 2).hom u') = 0)
    (hfin : Finite (groupCohomology (C.quotientToInvariants S) 2))
    (hle : Nat.card (groupCohomology (C.quotientToInvariants S) 2) ≤ Fintype.card (Γ ⧸ S)) :
    ∃ y : groupCohomology (C.quotientToInvariants S) 2,
      Nat.card (groupCohomology (C.quotientToInvariants S) 2) = Fintype.card (Γ ⧸ S) ∧
      Submodule.span k {y} = ⊤ ∧
      (map (A := C.quotientToInvariants S) (B := C) (QuotientGroup.mk' S)
          (ofHom (C.ρ.quotientToInvariants_lift S)) 2).hom y =
        (n' / Fintype.card (Γ ⧸ S)) •
          (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
            (ofHom (C.ρ.quotientToInvariants_lift T)) 2).hom u' := by
  classical

  have hinjT := (ModuleCat.mono_iff_injective _).mp
    (originalSecondCohomology_inflation_mono C T hT1)
  have hinjS := (ModuleCat.mono_iff_injective _).mp
    (originalSecondCohomology_inflation_mono C S hS1)
  have hrangeS := (originalSecondCohomology_inflation_restriction_exact C S hS1).moduleCat_range_eq_ker
  set infT := ModuleCat.Hom.hom (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
      (ofHom (C.ρ.quotientToInvariants_lift T)) 2) with hinfT
  set infS := ModuleCat.Hom.hom (map (A := C.quotientToInvariants S) (B := C) (QuotientGroup.mk' S)
      (ofHom (C.ρ.quotientToInvariants_lift S)) 2) with hinfS
  change infS.range = (ModuleCat.Hom.hom
    (map S.subtype (𝟙 (Rep.res S.subtype C)) 2)).ker at hrangeS
  set n := Fintype.card (Γ ⧸ S) with hn_def
  have hn0 : n ≠ 0 := Fintype.card_ne_zero
  set x := (n' / n) • infT u' with hx

  have hordw : addOrderOf (infT u') = n' := by rw [← hu']; exact addOrderOf_injective infT.toAddMonoidHom hinjT u'
  have hm0 : n' / n ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hn).mpr ⟨hn'0, hn0⟩
  have hordx : addOrderOf x = n := by
    rw [hx, addOrderOf_nsmul' _ hm0, hordw, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hn), Nat.div_div_self hn hn'0]

  have hxker : x ∈ LinearMap.ker (ModuleCat.Hom.hom (map S.subtype (𝟙 (Rep.res S.subtype C)) 2)) := by
    rw [LinearMap.mem_ker]; exact hres
  rw [← hrangeS] at hxker
  obtain ⟨y, hy⟩ := hxker
  have hordy : addOrderOf y = n := by
    have h1 : addOrderOf (infS y) = addOrderOf y := addOrderOf_injective infS.toAddMonoidHom hinjS y
    rw [← h1]; show addOrderOf (infS y) = n; rw [hy, hordx]

  haveI := hfin
  letI : Fintype (groupCohomology (C.quotientToInvariants S) 2) := Fintype.ofFinite _
  have hcard : Nat.card (groupCohomology (C.quotientToInvariants S) 2) = n := by
    refine le_antisymm hle ?_
    calc n = addOrderOf y := hordy.symm
      _ ≤ Fintype.card (groupCohomology (C.quotientToInvariants S) 2) := addOrderOf_le_card_univ
      _ = Nat.card (groupCohomology (C.quotientToInvariants S) 2) := (Nat.card_eq_fintype_card).symm
  have hzm : AddSubgroup.zmultiples y = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hordy, hcard]
  refine ⟨y, hcard, ?_, hy⟩
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ AddSubgroup.zmultiples y := by rw [hzm]; trivial
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
  rw [← hm, ← Int.cast_smul_eq_zsmul k m y]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)


end
end Dubon2026
