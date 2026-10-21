import Dubon2026.SourceAllDivisorMonicRelations
import Dubon2026.SourceOriginalFieldDifferentialConsumer

/-! DUB-17/18 -> original cusp-form lower dimension bound -> regular
differential realization -> injective original differential expansion.
The actual monic relations are now derived from the original analytic j
series and its finite conjugate products, for every nonzero divisor.
This discharges the monic-relation and separability premises of the previous
original-field consumer. Regularity, geometric genus and cusp-form realization
are still separate obligations.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

/-- The original divisor-generated modular function field is finite over its actual j coordinate. -/
theorem finiteDimensional_original :
    FiniteDimensional
      (IntermediateField.adjoin L ({jOver N L} : Set (modularFunctionFieldOver N L)))
      (modularFunctionFieldOver N L) :=
  finiteDimensional_original_of_monic_relations L N
    (fun d _ _ => exists_monic_relation d)

/-- Differential q-expansion on the original modular function field is injective. -/
theorem diffQExp_original_injective :
    Function.Injective (SourceDifferential.diffQExp (modularFunctionFieldOver N L)) :=
  diffQExp_original_injective_of_monic_relations N L
    (fun d _ _ => exists_monic_relation d)

end
end Dubon2026.SourceFunctionField
