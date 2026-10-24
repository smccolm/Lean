import Dubon2026.SourceEllipticWeierstrassAdditionRemainder

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

/-- The exact denominator-cleared x-addition defect of the Weierstrass functions. -/
def additionPhi (w : ℂ) (z : ℂ) : ℂ :=
  4 * (℘[L] z - ℘[L] w) ^ 2 * (℘[L] (z + w) + ℘[L] z + ℘[L] w)
    - (℘'[L] z - ℘'[L] w) ^ 2


theorem additionPhi_diffEq {z : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    (additionPhi L) w z = 4 * (℘[L] z - ℘[L] w) ^ 2 * ℘[L] (z + w)
      - 4 * ℘[L] w * ℘[L] z ^ 2 - 4 * ℘[L] w ^ 2 * ℘[L] z
      + L.g₂ * (℘[L] z + ℘[L] w) + 2 * L.g₃ + 2 * ℘'[L] z * ℘'[L] w := by
  have hdz := L.derivWeierstrassP_sq z hz
  have hdw := L.derivWeierstrassP_sq w hw
  unfold additionPhi
  linear_combination -hdz - hdw


theorem addBridge_identity {z : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hz0 : z ≠ 0) :
    z ^ 4 * (additionPhi L) w z = (additionCore L) w z + (additionRemainder L) w z := by

  have hPz : ℘[L] z = (z ^ 2)⁻¹ + L.weierstrassPExcept (0 : ℂ) z := by
    have h := PeriodPair.weierstrassPExcept_add L ⟨0, zero_mem _⟩ z
    simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, div_zero, one_div] at h
    linear_combination -h
  have hP'z : ℘'[L] z = -2 * (z ^ 3)⁻¹ + L.derivWeierstrassPExcept (0 : ℂ) z := by
    have h := PeriodPair.derivWeierstrassPExcept_sub L ⟨0, zero_mem _⟩ z
    simp only [sub_zero] at h
    have hr : (2 : ℂ) / z ^ 3 = 2 * (z ^ 3)⁻¹ := by ring
    rw [hr] at h
    linear_combination -h

  rw [(additionPhi_diffEq L) hz hw, hPz, hP'z]
  unfold additionCore additionRemainder additionTail
  field_simp
  ring


theorem additionCore_add_R_order_ge_four (hw : w ∉ L.lattice) :
    (4 : ℕ∞) ≤ analyticOrderAt (fun z => (additionCore L) w z + (additionRemainder L) w z) 0 := by
  refine le_trans ?_ le_analyticOrderAt_add
  exact le_min ((additionCore_order_ge_four L) hw) ((additionRemainder_order_ge_four L) hw)


end
end Dubon2026.SourceEllipticPeriod
