/-
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0; see ../../Dependencies/AnthropicFLTReuse/LICENSE.
The order and generation argument follows the native
OriginalH2GeneratorInflationTransfer adaptation of
anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero.lean.
Changes: use the proved original field-tower exact sequence directly.
-/
import Dubon2026.OriginalIdeleClassH2InflationRestriction
import Dubon2026.OriginalIdeleClassFiniteGaloisCohomology

/-! # Generator transfer through actual field towers

The existing exact sequence and injective inflations transfer an actual
auxiliary class of sufficient order to the target field. The original
finite H2 bound proves that this target class generates. This is DUB-17's
arbitrary-stage generator step, with only its arithmetic auxiliary witness
and restriction vanishing left as explicit upstream inputs.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K M] [IsGalois K E] [IsGalois K L] [IsGalois K M]

/-- The proved original tower exact sequence transfers a full-order auxiliary class with vanishing scaled restriction to an actual generator of the target original idele-class H2. -/
theorem originalIdeleClass_tower_generator_from_auxiliary
    (n' : ℕ) (hn : Module.finrank K E ∣ n') (hn'0 : n' ≠ 0)
    (u' : groupCohomology (originalIdeleClassRep K L) 2) (hu' : addOrderOf u' = n')
    (hres : originalIdeleClassTowerH2Restriction K E M
      ((n' / Module.finrank K E) •
        groupCohomology.map (AlgEquiv.restrictNormalHom L)
          (originalIdeleClassTowerInclusion K L M) 2 u') = 0) :
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      Nat.card (groupCohomology (originalIdeleClassRep K E) 2) = Module.finrank K E ∧
      Submodule.span ℤ {y} = ⊤ ∧
      groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (originalIdeleClassTowerInclusion K E M) 2 y =
        (n' / Module.finrank K E) •
          groupCohomology.map (AlgEquiv.restrictNormalHom L)
            (originalIdeleClassTowerInclusion K L M) 2 u' := by
  classical
  letI : FiniteDimensional K E := FiniteDimensional.left K E M
  let infL := (groupCohomology.map (AlgEquiv.restrictNormalHom L)
    (originalIdeleClassTowerInclusion K L M) 2).hom
  let infE := (groupCohomology.map (AlgEquiv.restrictNormalHom E)
    (originalIdeleClassTowerInclusion K E M) 2).hom
  have hiL := originalIdeleClassH2Inflation_injective K L M
  have hiE := originalIdeleClassH2Inflation_injective K E M
  let n := Module.finrank K E
  have hn0 : n ≠ 0 := ne_of_gt (Module.finrank_pos (R := K) (M := E))
  let x := (n' / n) • infL u'
  have hoL : addOrderOf (infL u') = n' :=
    (addOrderOf_injective infL.toAddMonoidHom hiL u').trans hu'
  have hm : n' / n ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hn).mpr ⟨hn'0, hn0⟩
  have hox : addOrderOf x = n := by
    rw [addOrderOf_nsmul' _ hm, hoL, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hn),
      Nat.div_div_self hn hn'0]
  obtain ⟨y, hy⟩ := (originalIdeleClassH2_inflation_exists_iff_restriction_zero K E M x).mpr hres
  have hoy : addOrderOf y = n :=
    (addOrderOf_injective infE.toAddMonoidHom hiE y).symm.trans
      ((congrArg addOrderOf hy).trans hox)
  obtain ⟨hf, hd⟩ := originalIdeleClass_finiteGalois_second_card_dvd K E
  letI := hf
  have hc : Nat.card (groupCohomology (originalIdeleClassRep K E) 2) = n :=
    Nat.dvd_antisymm hd (hoy ▸ addOrderOf_dvd_natCard y)
  have hz : AddSubgroup.zmultiples y = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hoy, hc]
  refine ⟨y, hc, ?_, hy⟩
  apply (Submodule.span_singleton_eq_top_iff ℤ y).mpr
  intro z
  have hmem : z ∈ AddSubgroup.zmultiples y := by rw [hz]; trivial
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  refine ⟨m, ?_⟩
  simpa only [Int.cast_id] using (Int.cast_smul_eq_zsmul ℤ m y).trans hm

end
end Dubon2026
