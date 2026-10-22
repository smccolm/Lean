import Dubon2026.SourceOriginalAllLevelDegree
import Dubon2026.SourceOriginalJCoordinatePlaces
import Dubon2026.SourceCurveTranscendentalDegree

/-! DUB-17/18 -> numerical modular genus -> exact finite j-fiber degrees.
The proved all-level coordinate degree and the existing literal place-order
sum give total multiplicity dedekindPsi(N) over every finite j value. The
residue degree is derived to be one over algebraically closed constants.
No ramification or fiber cardinality hypothesis is introduced: those are
the remaining inputs to the numerical genus calculation.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve IntermediateField
open scoped IntermediateField

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

omit [NeZero N] in
theorem original_j_sub_transcendental (c : L) :
    Transcendental L (jOver N L - algebraMap L (modularFunctionFieldOver N L) c) := by
  intro h
  apply transcendental_jOver N L
  simpa only [sub_add_cancel] using h.add (isAlgebraic_algebraMap c)

omit [NeZero N] in
theorem original_j_sub_adjoin (c : L) :
    L⟮jOver N L - algebraMap L (modularFunctionFieldOver N L) c⟯ = L⟮jOver N L⟯ := by
  apply le_antisymm
  · exact adjoin_simple_le_iff.mpr
      (L⟮jOver N L⟯.sub_mem (mem_adjoin_simple_self _ _) (L⟮jOver N L⟯.algebraMap_mem c))
  · apply adjoin_simple_le_iff.mpr
    have h := (L⟮jOver N L - algebraMap L (modularFunctionFieldOver N L) c⟯).add_mem
      (mem_adjoin_simple_self _ _) (IntermediateField.algebraMap_mem _ c)
    simpa only [sub_add_cancel] using h

theorem sum_original_j_fiber_orders_eq_psi [IsAlgClosed L] (c : L) :
    (∑ᶠ v : {v : Place L (modularFunctionFieldOver N L) //
        0 < v.ord (jOver N L - algebraMap L (modularFunctionFieldOver N L) c)},
      v.1.ord (jOver N L - algebraMap L (modularFunctionFieldOver N L) c)) =
        (SourceLevelProjective.dedekindPsi N : ℤ) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := finiteDimensional_original_over_transcendental N L (original_j_sub_transcendental N L c)
  have h := sum_positive_orders_eq_finrank_adjoin _ (original_j_sub_transcendental N L c)
  have hr : ∀ v : Place L (modularFunctionFieldOver N L), Module.finrank L v.ResidueField = 1 :=
    fun v => Module.finrank_of_bijective_algebraMap (original_place_residue_algebraMap_bijective N L v)
  simp only [hr, Nat.cast_one, mul_one] at h
  rw [original_j_sub_adjoin, finrank_original_over_j_eq_psi] at h
  exact h

end
end Dubon2026.SourceFunctionField
