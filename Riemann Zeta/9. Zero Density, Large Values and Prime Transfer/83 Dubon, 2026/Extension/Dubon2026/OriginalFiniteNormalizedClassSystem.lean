import Dubon2026.OriginalCompletionClassRestrictions
import Dubon2026.OriginalClassH2SubgroupGenerators

/-! # The original finite class system with source-normalized local restrictions

Assemble the existing subgroup H1 vanishing and H2 generator/cardinality
results with the one global class compatible with all normalized original
completion classes. This is DUB-17's finite-stage class-system input;
continuous and inter-stage class-formation claims remain separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- One original global class generates every subgroup H2, all subgroup H1 vanish, the subgroup H2 cardinalities are exact, and every normalized original completion class has the prescribed restriction image. This proposition alone asserts no existence. -/
def OriginalFiniteNormalizedClassSystem : Prop :=
    ∃ u : groupCohomology (originalIdeleClassRep K L) 2,
      addOrderOf u = Module.finrank K L ∧
      (∀ S : Subgroup Gal(L/K), Limits.IsZero
        (groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 1)) ∧
      (∀ S : Subgroup Gal(L/K),
        Nat.card (groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2) = Nat.card S) ∧
      (∀ S : Subgroup Gal(L/K), Submodule.span ℤ
        {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2).hom u} = ⊤) ∧
      OriginalCompletionClassRestrictions K L u

/-- The constructed source-normalized global class assembles the complete finite original subgroup class system using already proved H1 vanishing, exact H2 cardinalities and restriction generators. -/
theorem originalIdeleClass_finite_normalized_system_of_completion_restrictions
    (h : ∃ u : groupCohomology (originalIdeleClassRep K L) 2,
      addOrderOf u = Module.finrank K L ∧ OriginalCompletionClassRestrictions K L u) :
    OriginalFiniteNormalizedClassSystem K L := by
  obtain ⟨u, hu, hl⟩ := h
  obtain ⟨hcard, hgen⟩ := originalIdeleClass_full_order_restricts_to_generators K L u hu
  refine ⟨u, hu, fun S => ?_, hcard, hgen, hl⟩
  exact (originalIdeleClass_finiteGalois_first_zero (IntermediateField.fixedField S) L).of_iso
    (originalIdeleClassSubgroupCohomologyIso S 1).symm

end
end Dubon2026
