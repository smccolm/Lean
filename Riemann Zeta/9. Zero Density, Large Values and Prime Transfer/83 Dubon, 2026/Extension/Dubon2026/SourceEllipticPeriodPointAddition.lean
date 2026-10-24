import Dubon2026.SourceEllipticWeierstrassAdditionY
import Dubon2026.SourceEllipticPeriodGenericShift
import Dubon2026.SourceEllipticPeriodPoint

/-! The actual period-point map respects addition in every case. The native
elliptic-curve addition formula handles generic points; a simultaneous
shift and group cancellation remove all extra hypotheses. This supplies
the homomorphism needed for uniformization, the odd-prime product identity
and the DUB-17/18 cyclic-root and inertia obligations.
Adapted from the frozen Apache-2.0 FLT period uniformization proof. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve
open scoped PeriodPair
variable (L : PeriodPair) [(periodCurve L).IsElliptic]

theorem periodPoint_add_generic {w z : ℂ}
    (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice)
    (hz : z ∉ L.lattice) (hzw : z + w ∉ L.lattice) (hne : ℘[L] z ≠ ℘[L] w) :
    periodPoint L (z + w) = periodPoint L z + periodPoint L w := by
  rw [periodPoint_of_notMem L hz, periodPoint_of_notMem L hw, periodPoint_of_notMem L hzw,
    Affine.Point.add_of_X_ne hne]
  simp only [Affine.Point.some.injEq]
  exact ⟨weierstrassP_add_eq_addX L hw h2w hz hzw hne,
    derivWeierstrassP_add_eq_addY L hw h2w hz hzw hne⟩

theorem periodPoint_add (z w : ℂ) :
    periodPoint L (z + w) = periodPoint L z + periodPoint L w := by
  by_cases hz : z ∈ L.lattice
  · rw [periodPoint_of_mem L hz, zero_add, add_comm, periodPoint_add_mem L w hz]
  by_cases hw : w ∈ L.lattice
  · rw [periodPoint_of_mem L hw, add_zero, periodPoint_add_mem L z hw]
  by_cases hzw : z + w ∈ L.lattice
  · rw [periodPoint_of_mem L hzw]
    have h : periodPoint L w = periodPoint L (-z) := by
      rw [show w = -z + (z + w) from by ring, periodPoint_add_mem L (-z) hzw]
    rw [h, periodPoint_neg, add_neg_cancel]
  obtain ⟨u, hu, h2u, hwu, hzwu, h2wu, hne_wu, hne_zwu, hne_zwuP⟩ :=
    exists_generic_period_shift L z w
  have A2 := periodPoint_add_generic L hu h2u hw hwu hne_wu
  have A3 := periodPoint_add_generic L hu h2u hzw hzwu hne_zwu
  have A4 := periodPoint_add_generic L hwu h2wu hz
    (by rwa [show z + (w + u) = z + w + u from by ring]) hne_zwuP
  have hchain : periodPoint L (z + w) + periodPoint L u =
      periodPoint L z + periodPoint L w + periodPoint L u := by
    rw [← A3, show z + w + u = z + (w + u) from by ring, A4, A2]
    abel
  exact add_right_cancel hchain

end Dubon2026.SourceEllipticPeriod
