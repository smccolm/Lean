import Dubon2026.SourceEllipticWeierstrassAdditionCoreOrder

/-! The actual Weierstrass addition defect has removable principal parts.
Its explicit fourth-order remainder and exact differential-equation identity
reduce the addition law to an entire periodic function. This serves the
actual uniformization, odd-prime product identity and DUB-17/18 cyclic roots.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean. -/

namespace Dubon2026.SourceEllipticPeriod
noncomputable section
open Complex Filter Set
open scoped PeriodPair Topology
variable (L : PeriodPair) {w : ℂ}

theorem weierstrassPExcept_zero_order_ge_two :
    (2 : ℕ∞) ≤ analyticOrderAt (L.weierstrassPExcept (0 : ℂ)) (0 : ℂ) := by
  rw [show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) from rfl,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (PeriodPair.analyticAt_weierstrassPExcept L (0 : ℂ))]
  intro i hi
  interval_cases i
  · simp only [iteratedDeriv_zero]; exact PeriodPair.weierstrassPExcept_zero L (0 : ℂ)
  · simp only [iteratedDeriv_one]
    rw [PeriodPair.deriv_weierstrassPExcept_same L (0 : ℂ)]
    exact PeriodPair.derivWeierstrassPExcept_zero_zero L


/-- The analytic tail built from the native Weierstrass regular parts. -/
def additionTail (w : ℂ) (z : ℂ) : ℂ :=
  4 * ((L.weierstrassPExcept (0:ℂ)) z - ℘[L] w) ^ 2 * ℘[L] (z + w)
    - 4 * ℘[L] w * (L.weierstrassPExcept (0:ℂ)) z ^ 2 - 4 * ℘[L] w ^ 2 * (L.weierstrassPExcept (0:ℂ)) z
    + L.g₂ * (L.weierstrassPExcept (0:ℂ)) z + L.g₂ * ℘[L] w + 2 * L.g₃ + 2 * ℘'[L] w * (L.derivWeierstrassPExcept (0:ℂ)) z


/-- The remainder after the explicit Taylor core, with order at least four. -/
def additionRemainder (w : ℂ) (z : ℂ) : ℂ :=
  8 * (z ^ 2 * (L.weierstrassPExcept (0:ℂ)) z) * (℘[L] (z + w) - ℘[L] w) + z ^ 4 * (additionTail L) w z


theorem analyticAt_additionTail (hw : w ∉ L.lattice) :
    AnalyticAt ℂ ((additionTail L) w) 0 := by
  unfold additionTail
  have h1 := PeriodPair.analyticAt_weierstrassPExcept L (0 : ℂ)
  have h2 := (analyticAt_weierstrassP_add_zero L) hw
  have h3 := PeriodPair.analyticAt_derivWeierstrassPExcept L (0 : ℂ)
  fun_prop


theorem analyticAt_additionRemainder (hw : w ∉ L.lattice) :
    AnalyticAt ℂ ((additionRemainder L) w) 0 := by
  unfold additionRemainder
  have h1 := PeriodPair.analyticAt_weierstrassPExcept L (0 : ℂ)
  have h2 := (analyticAt_weierstrassP_add_zero L) hw
  have h3 := (analyticAt_additionTail L) hw
  fun_prop


theorem additionRemainder_order_ge_four (hw : w ∉ L.lattice) :
    (4 : ℕ∞) ≤ analyticOrderAt ((additionRemainder L) w) (0 : ℂ) := by
  have hg := PeriodPair.analyticAt_weierstrassPExcept L (0 : ℂ)
  have hP := (analyticAt_weierstrassP_add_zero L) hw
  have hid : AnalyticAt ℂ (id : ℂ → ℂ) (0 : ℂ) := analyticAt_id

  have hord_id : analyticOrderAt (id : ℂ → ℂ) (0 : ℂ) = 1 := analyticOrderAt_id

  have hReq : (additionRemainder L) w =
      (fun _ : ℂ => (8 : ℂ)) * ((id ^ 2 * L.weierstrassPExcept (0 : ℂ))
        * ((fun z => ℘[L] (z + w)) - fun _ => ℘[L] w))
        + (id : ℂ → ℂ) ^ 4 * (additionTail L) w := by
    funext z
    simp only [additionRemainder, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
    ring
  rw [hReq]
  refine le_trans ?_ le_analyticOrderAt_add
  refine le_min ?_ ?_
  ·
    rw [analyticOrderAt_mul analyticAt_const (((hid.pow 2).mul hg).mul (hP.sub analyticAt_const)),
      analyticOrderAt_mul ((hid.pow 2).mul hg) (hP.sub analyticAt_const),
      analyticOrderAt_mul (hid.pow 2) hg, analyticOrderAt_pow hid, hord_id]
    calc (4 : ℕ∞) = 0 + ((2 • 1 + 2) + 0) := by norm_num
      _ ≤ _ := add_le_add zero_le'
              (add_le_add (add_le_add le_rfl (weierstrassPExcept_zero_order_ge_two L)) zero_le')
  ·
    rw [analyticOrderAt_mul (hid.pow 4) ((analyticAt_additionTail L) hw),
      analyticOrderAt_pow hid, hord_id]
    calc (4 : ℕ∞) = 4 • 1 + 0 := by norm_num
      _ ≤ _ := add_le_add le_rfl zero_le'


end
end Dubon2026.SourceEllipticPeriod
