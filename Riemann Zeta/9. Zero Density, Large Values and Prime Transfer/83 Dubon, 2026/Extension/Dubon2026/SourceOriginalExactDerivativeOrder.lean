import Dubon2026.SourceCurveExactDerivativeOrder
import Dubon2026.SourceOriginalIntegralDerivatives

/-! DUB-17/18 -> matching cusp-form dimension -> numerical geometric genus
-> original canonical j-divisor degree -> exact local ramification orders.
All original-field local differential finiteness, separability and coordinate
generation inputs are derived. At every actual place, differentiating a
function of nonzero order decreases that order by exactly one.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem original_ordDifferential_D_eq_ord_sub_one
    (v : Place L (modularFunctionFieldOver N L)) {f : modularFunctionFieldOver N L}
    (hf : v.ord f ≠ 0) :
    v.ordDifferential (D L (modularFunctionFieldOver N L) f) = v.ord f - 1 := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := finite_original_place_differentials N L v
  haveI := original_place_residue_isAlgebraic N L v
  haveI := original_place_dCoordGenerates N L v
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  exact v.ordDifferential_D_eq_ord_sub_one hf

end
end Dubon2026.SourceFunctionField
