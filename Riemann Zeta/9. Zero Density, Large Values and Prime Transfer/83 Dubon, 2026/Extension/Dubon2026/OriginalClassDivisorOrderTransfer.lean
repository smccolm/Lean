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

/-! # Transfer a prescribed divisor order through the actual field tower

This discharges the indicated prime-power order obligation inside DUB-17's
mixed-degree full-order class construction. The original field and cohomology
maps are retained. No general cyclic auxiliary extension is required.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K E L M : Type) [Field K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K M] [IsGalois K E] [IsGalois K L] [IsGalois K M]

/-- The original tower exact sequence transfers the prescribed divisor of the auxiliary class order when its scaled restriction vanishes. -/
theorem originalIdeleClass_tower_order_from_auxiliary
    (d n' : ℕ) (hd0 : d ≠ 0) (hn : d ∣ n') (hn'0 : n' ≠ 0)
    (u' : groupCohomology (originalIdeleClassRep K L) 2) (hu' : addOrderOf u' = n')
    (hres : originalIdeleClassTowerH2Restriction K E M
      ((n' / d) •
        groupCohomology.map (AlgEquiv.restrictNormalHom L)
          (originalIdeleClassTowerInclusion K L M) 2 u') = 0) :
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf y = d ∧
      groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (originalIdeleClassTowerInclusion K E M) 2 y =
        (n' / d) •
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
  let n := d
  have hn0 : n ≠ 0 := hd0
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
  exact ⟨y, hoy, hy⟩

end
end Dubon2026
