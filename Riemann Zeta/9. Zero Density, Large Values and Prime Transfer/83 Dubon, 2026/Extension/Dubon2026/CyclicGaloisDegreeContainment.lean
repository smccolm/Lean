import Dubon2026.FiniteCyclicSubgroupContainment
import Mathlib.FieldTheory.KrullTopology

/-! # Actual intermediate-field containment from cyclic Galois degrees

This is the Galois-correspondence step for placing the original unramified
stage in the larger original stage, using their cyclic compositum. It serves
the characteristic-degree H2 vanishing and finite support required before
DUB-17's global reciprocity and Selmer duality.
-/

namespace Dubon2026
noncomputable section

variable {K E : Type} [Field K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E] [IsCyclic Gal(E/K)]

/-- Inside the same original finite cyclic Galois extension, divisibility
of the actual intermediate-field degrees implies literal field containment. -/
theorem cyclicGaloisIntermediateField_le_of_finrank_dvd
    (F L : IntermediateField K E) (h : Module.finrank K F ∣ Module.finrank K L) : F ≤ L := by
  have hi : F.fixingSubgroup.index ∣ L.fixingSubgroup.index := by
    simpa only [← IntermediateField.finrank_eq_fixingSubgroup_index] using h
  have hs := finiteCyclicSubgroup_le_of_index_dvd L.fixingSubgroup F.fixingSubgroup hi
  have hf := (IntermediateField.le_iff_le L.fixingSubgroup F).mpr hs
  simpa only [IsGalois.fixedField_fixingSubgroup] using hf

end
end Dubon2026
