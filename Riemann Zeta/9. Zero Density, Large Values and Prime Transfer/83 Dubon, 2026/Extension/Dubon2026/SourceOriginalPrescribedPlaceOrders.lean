import Dubon2026.SourceOriginalFinitePlaceSeparation
import Dubon2026.SourceCurvePrescribedOrders

/-! DUB-17/18 -> original Picard-period Hecke compatibility -> moving
divisor classes away from cusps. The existing actual place separation
supplies the finite-family separation required by the proved indicator
construction. Thus prescribed orders are obtained on any finite set of
original complex places, with no approximation input left to the caller.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]

theorem exists_original_prescribed_place_orders
    (S : Finset (Place ℂ (modularFunctionFieldOver N ℂ)))
    (n : Place ℂ (modularFunctionFieldOver N ℂ) → ℤ) :
    ∃ f : modularFunctionFieldOver N ℂ, f ≠ 0 ∧ ∀ v ∈ S, v.ord f = n v := by
  classical
  apply Place.exists_forall_ord_eq_of_sep S n
  intro v _
  obtain ⟨z, hz, hw⟩ := exists_original_polar_regular_separator N (S.erase v)
    (Finset.notMem_erase v S)
  exact ⟨z, hz, fun w hwS hwv => hw w (Finset.mem_erase.mpr ⟨hwv, hwS⟩)⟩

end
end Dubon2026.SourceFunctionField
