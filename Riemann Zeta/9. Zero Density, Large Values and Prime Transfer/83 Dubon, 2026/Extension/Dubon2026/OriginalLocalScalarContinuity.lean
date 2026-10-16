import Dubon2026.LocalFieldCompactLattice

/-! # Continuity of the original compatible local-field inclusion

Reuse the proved continuity on the original integer rings and their
openness. This supplies the base-field closure step identifying DUB-17's
arithmetic orbit field with the completion at its actual finite prime.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K E : Type) [Field K] [Field E] [Algebra K E]
  [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]

/-- The actual local-field inclusion is continuous in the original topologies. -/
theorem originalLocalScalar_continuous : Continuous (algebraMap K E) := by
  have hi : Continuous (fun x : 𝒪[K] => algebraMap K E (x : K)) :=
    localField_integerScalar_continuous K E
  apply continuous_of_continuousAt_zero (algebraMap K E)
  exact (Valuation.isOpen_integer (v := ValuativeRel.valuation K)).isOpenEmbedding_subtypeVal.continuousAt_iff.mp
    (hi.continuousAt (x := (0 : 𝒪[K])))

end
end Dubon2026
