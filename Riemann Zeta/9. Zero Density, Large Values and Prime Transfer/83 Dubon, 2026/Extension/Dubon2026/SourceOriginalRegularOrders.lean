import Dubon2026.SourceCurveOrders
import Dubon2026.SourceOriginalLocalDifferentials

/-! DUB-17/18 -> actual cusp-form lower bound -> regular differential
realization. Regularity of the original field's actual differentials is
equivalent to nonnegative order of every actual local coefficient. This is
the order interface used by divisor spaces and analytic regularity.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open KaehlerDifferential SourceCurve

theorem mem_original_regularDifferentials_iff_ord_nonneg
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]
    (ω : Ω[modularFunctionFieldOver N L⁄L]) :
    ω ∈ regularDifferentials L (modularFunctionFieldOver N L) ↔
      ∀ v : Place L (modularFunctionFieldOver N L), 0 ≤ v.ordDifferential ω := by
  rw [mem_original_regularDifferentials_iff]
  exact forall_congr' fun v => v.mem_iff_ord_nonneg

end
end Dubon2026.SourceFunctionField
