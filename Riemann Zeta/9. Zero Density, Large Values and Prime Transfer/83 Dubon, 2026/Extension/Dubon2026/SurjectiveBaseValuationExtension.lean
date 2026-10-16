import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-! # Retaining a local-stage valuation across the proved completion equivalence

On DUB-17's completion-invariant comparison, the new base is the image of
the entire original base. The existing stage valuation therefore extends
the new base valuation; no new spectral construction is required.
-/
namespace Dubon2026
noncomputable section

/-- A valuation extending the original base also extends a surjective intermediate base. -/
theorem surjectiveBase_valuation_hasExtension
    (K E F : Type) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [ValuativeRel K] [ValuativeRel E] [ValuativeRel F]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    (h : Function.Surjective (algebraMap K E)) :
    (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation F) := by
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := h x
  obtain ⟨y, rfl⟩ := h y
  change ValuativeRel.valuation E (algebraMap K E x) ≤ ValuativeRel.valuation E (algebraMap K E y) ↔
    ValuativeRel.valuation F (algebraMap E F (algebraMap K E x)) ≤
      ValuativeRel.valuation F (algebraMap E F (algebraMap K E y))
  rw [← IsScalarTower.algebraMap_apply K E F, ← IsScalarTower.algebraMap_apply K E F,
    Valuation.HasExtension.val_map_le_iff (ValuativeRel.valuation K) (ValuativeRel.valuation E),
    Valuation.HasExtension.val_map_le_iff (ValuativeRel.valuation K) (ValuativeRel.valuation F)]

end
end Dubon2026
