import Dubon2026.OriginalCoinducedGlobalDimensionShift

/-! # Retract the original restricted functions from actual coinduction

The finite class/Ext converse needs the two-degree cohomological-triviality
criterion. Its subgroup induction uses positive dimension shifts after
restriction. Reuse the original coset coordinates to split the subgroup
coinduction unit, so pinned Shapiro supplies every positive degree at once.
No new cochain homotopies or integer-graded Tate complex are introduced.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (S : Subgroup G)

/-- Evaluate subgroup-coinduced original functions at the genuine coset remainder and representative. -/
def originalCoinducedSubgroupRetraction :
    originalCoinducedFunctionRep (Rep.res S.subtype (originalCoinducedFunctionRep A)) ⟶
      Rep.res S.subtype (originalCoinducedFunctionRep A) :=
  Rep.ofHom ⟨{
    toFun := fun f => originalCoinducedFunction A
      (fun g => (f.val (subgroupCosetRemainder S g)).val (subgroupCosetRepresentative S g))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }, by
      intro s
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext g
      change (f.val (subgroupCosetRemainder S g * s)).val (subgroupCosetRepresentative S g) =
        (f.val (subgroupCosetRemainder S (g * s))).val (subgroupCosetRepresentative S (g * s))
      rw [subgroupCosetRemainder_mul, subgroupCosetRepresentative_mul]⟩

/-- The actual subgroup coinduction unit followed by the original coset retraction is the identity. -/
theorem originalCoinducedSubgroup_unit_retraction :
    originalCoinducedUnit (Rep.res S.subtype (originalCoinducedFunctionRep A)) ≫
      originalCoinducedSubgroupRetraction A S = 𝟙 _ := by
  apply Rep.hom_ext
  ext f g
  change f.val (subgroupCosetRepresentative S g * (subgroupCosetRemainder S g : G)) = f.val g
  rw [subgroupCosetRepresentative_mul_remainder]

/-- Every positive cohomology group of the original subgroup-restricted coinduced coefficient vanishes by its genuine retraction from Shapiro-acyclic functions. -/
theorem originalCoinducedSubgroup_positive_zero (n : ℕ) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalCoinducedFunctionRep A)) (n + 1)) := by
  let F := groupCohomology.functor k S (n + 1)
  have hz : F.map (originalCoinducedUnit (Rep.res S.subtype (originalCoinducedFunctionRep A))) = 0 :=
    (originalCoinducedFunction_positive_zero
      (Rep.res S.subtype (originalCoinducedFunctionRep A)) n).eq_zero_of_tgt _
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  have he := congrArg F.map (originalCoinducedSubgroup_unit_retraction A S)
  rw [F.map_comp, F.map_id, hz, Limits.zero_comp] at he
  exact he.symm

end
end Dubon2026
