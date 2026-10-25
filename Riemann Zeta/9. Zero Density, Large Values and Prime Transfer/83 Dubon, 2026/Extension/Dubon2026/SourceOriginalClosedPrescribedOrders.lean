import Dubon2026.SourceOriginalClosedFiniteSeparation
import Dubon2026.SourceCurvePrescribedOrders

/-! DUB-17/18 -> original Weil pairing descent -> moving arithmetic
Picard representatives. The existing generic finite-place indicator theorem
now receives proved separation over every closed original constant field.
No approximation assumption is left to the caller. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem exists_original_closed_prescribed_place_orders
    (S : Finset (Place L (modularFunctionFieldOver N L)))
    (n : Place L (modularFunctionFieldOver N L) → ℤ) :
    ∃ f : modularFunctionFieldOver N L, f ≠ 0 ∧ ∀ v ∈ S, v.ord f = n v := by
  classical
  apply Place.exists_forall_ord_eq_of_sep S n
  intro v _
  obtain ⟨z, hz, hw⟩ := exists_original_closed_polar_regular_separator N L (S.erase v)
    (Finset.notMem_erase v S)
  exact ⟨z, hz, fun w hwS hwv => hw w (Finset.mem_erase.mpr ⟨hwv, hwS⟩)⟩

end
end Dubon2026.SourceFunctionField
