import Dubon2026.GaloisUnitBaseChangeContinuity
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Homeomorph.Lemmas

/-! # The original finite-base fixing subgroup with its genuine Krull topology -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω)

/-- Changing the fixed base in the same original Galois field is the
literal inclusion of its actual fixing subgroup. -/
theorem galoisBaseChangeRestriction_eq_fixingSubgroup (g : Gal(Ω/E)) :
    galoisBaseChangeRestriction K E Ω Ω g =
      ((IntermediateField.fixingSubgroupEquiv E).symm g : Gal(Ω/K)) := by
  ext x
  exact galoisBaseChangeRestriction_commutes K E Ω Ω g x

/-- The actual fixing-subgroup inverse is continuous for the original
Krull topologies. -/
theorem fixingSubgroupEquiv_symm_continuous :
    Continuous (IntermediateField.fixingSubgroupEquiv E).symm := by
  apply Continuous.subtype_mk
  have heq : (fun g : Gal(Ω/E) =>
      ((IntermediateField.fixingSubgroupEquiv E).symm g : Gal(Ω/K))) =
      galoisBaseChangeRestriction K E Ω Ω := by
    funext g
    exact (galoisBaseChangeRestriction_eq_fixingSubgroup K Ω E g).symm
  change (AlgEquiv.restrictScalars K : Gal(Ω/E) → Gal(Ω/K)) =
    galoisBaseChangeRestriction K E Ω Ω at heq
  rw [heq]
  exact galoisBaseChangeRestriction_continuous K E Ω Ω

/-- The original fixing-subgroup equivalence is continuous in the other
direction as well, by compactness of the original Galois group. -/
theorem fixingSubgroupEquiv_continuous :
    Continuous (IntermediateField.fixingSubgroupEquiv E) := by
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  exact (fixingSubgroupEquiv_symm_continuous K Ω E).continuous_symm_of_equiv_compact_to_t2

variable [FiniteDimensional K E]

/-- The quotient by the actual finite-base fixing subgroup is finite. -/
instance finiteOriginalGaloisFixingCosets : Finite (Gal(Ω/K) ⧸ E.fixingSubgroup) :=
  Subgroup.quotient_finite_of_isOpen E.fixingSubgroup E.fixingSubgroup_isOpen

omit [FiniteDimensional K E] in
/-- The exact number of genuine fixing cosets is the original field degree. -/
theorem galoisFixingCosets_card [Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup)] :
    Fintype.card (Gal(Ω/K) ⧸ E.fixingSubgroup) = Module.finrank K E := by
  rw [E.finrank_eq_fixingSubgroup_index, Subgroup.index, Nat.card_eq_fintype_card]

end
end Dubon2026
