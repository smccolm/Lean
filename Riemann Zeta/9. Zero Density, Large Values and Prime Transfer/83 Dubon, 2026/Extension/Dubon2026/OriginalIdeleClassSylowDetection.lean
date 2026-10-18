import Dubon2026.OriginalIdeleClassSubgroupCohomology
import Dubon2026.OriginalIdeleClassH2Restriction
import Dubon2026.OriginalRelationObstructionSylowDetection

/-! The actual class at DUB-17's common source-cup field is prime-annihilated.
Detect its vanishing on the actual Sylow fixed field, using the existing
subgroup trace and the original class-coefficient comparison. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- Literal fixed-field class restriction is subgroup restriction under
the existing original class-cohomology isomorphism. -/
theorem originalIdeleClassTowerH2Restriction_subgroup
    (S : Subgroup Gal(L/K)) (x : groupCohomology (originalIdeleClassRep K L) 2) :
    (originalIdeleClassSubgroupCohomologyIso S 2).hom
      (originalIdeleClassTowerH2Restriction K (IntermediateField.fixedField S) L x) =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2 x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map (MonoidHom.id S) (originalIdeleClassSubgroupCoefficientIso S).hom 2
      (groupCohomology.map (IntermediateField.subgroupEquivAlgEquiv S).toMonoidHom (𝟙 _) 2
        (groupCohomology.map (galoisTowerBaseRestriction K (IntermediateField.fixedField S) L)
          (originalIdeleClassTowerRestrictionCoefficient K (IntermediateField.fixedField S) L).hom 2
          (groupCohomology.H2π _ c))) = _
    simp only [groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    rfl

/-- A prime-annihilated actual full class vanishes exactly when its
restriction to the chosen Sylow fixed field vanishes. -/
theorem originalIdeleClassH2_eq_zero_iff_sylow_fixedField
    (p : ℕ) [Fact p.Prime] (S : Sylow p Gal(L/K))
    (x : groupCohomology (originalIdeleClassRep K L) 2) (hx : p • x = 0) :
    x = 0 ↔ originalIdeleClassTowerH2Restriction K
      (IntermediateField.fixedField (S : Subgroup Gal(L/K))) L x = 0 := by
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    letI : Fintype (Gal(L/K) ⧸ (S : Subgroup Gal(L/K))) := Fintype.ofFinite _
    have hp : p.Coprime (Fintype.card (Gal(L/K) ⧸ (S : Subgroup Gal(L/K)))) := by
      simpa only [Subgroup.index, Nat.card_eq_fintype_card] using
        (Fact.out : p.Prime).coprime_iff_not_dvd.mpr S.not_dvd_index
    apply subgroupCohomologyComparison_coprime_zero (originalIdeleClassRep K L)
      (S : Subgroup Gal(L/K)) 2 p hp x hx
    rw [subgroupCohomologyComparison_eq_restriction]
    rw [← originalIdeleClassTowerH2Restriction_subgroup K L (S : Subgroup Gal(L/K)) x,
      h, map_zero]

end
end Dubon2026
