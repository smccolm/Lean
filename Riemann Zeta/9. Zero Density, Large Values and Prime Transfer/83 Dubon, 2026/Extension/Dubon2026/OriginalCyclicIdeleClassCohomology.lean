import Dubon2026.OriginalCyclicNormIndex

/-! # The original cyclic idele-class cohomology orders

The proved literal norm index transfers through the existing original
invariant-norm and periodic H2 equivalences. The already proved original
Herbrand formula then forces H1 to vanish. These discharge the original
cyclic low-degree class-field obligations needed for reciprocity and the
global invariant sum-zero on DUB-17's actual arithmetic duality chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

/-- The original cyclic idele-class H2 has cardinal equal to the actual field degree. -/
theorem original_ideleClass_second_card :
    Nat.card (groupCohomology (originalIdeleClassRep K L) 2) = Module.finrank K L := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let e := (originalIdeleClassNormQuotientEquiv K L g hg).trans
    (originalIdeleClassInvariantNormQuotientEquiv K L g hg)
  exact (Nat.card_congr e.toEquiv).symm.trans (original_cyclic_normQuotient_card K L)

/-- The actual original cyclic idele-class H1 vanishes by its proved Herbrand formula. -/
theorem original_ideleClass_first_zero :
    Limits.IsZero (groupCohomology (originalIdeleClassRep K L) 1) := by
  obtain ⟨_, _, hCard⟩ := original_ideleClass_herbrand K L
  rw [original_ideleClass_second_card, IsGalois.card_aut_eq_finrank] at hCard
  have hOne : Nat.card (groupCohomology (originalIdeleClassRep K L) 1) = 1 := by
    apply Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := K) (M := L))
    rw [one_mul]
    exact hCard.symm
  exact ModuleCat.isZero_iff_subsingleton.mpr (Nat.card_eq_one_iff_unique.mp hOne).1

end
end Dubon2026
