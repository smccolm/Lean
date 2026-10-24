import Dubon2026.SourceEllipticWeierstrassDerivatives

/-! Principal-part cancellation for the actual Weierstrass addition formula.
The explicit analytic core vanishes to fourth order; the proved second and
third differential identities discharge its Taylor coefficients. This is
needed for the addition law, uniformization and odd-prime quotient-product
identity on the DUB-17/18 cyclic-root chain.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean. -/

namespace Dubon2026.SourceEllipticPeriod
noncomputable section
open Complex Filter Set
open scoped PeriodPair Topology
variable (L : PeriodPair) {w : ℂ}

theorem hasDerivAt_weierstrassP_add {z : ℂ} (hzw : z + w ∉ L.lattice) :
    HasDerivAt (fun u => ℘[L] (u + w)) (℘'[L] (z + w)) z := by
  have h := (L.analyticOnNhd_weierstrassP (z + w) hzw).differentiableAt.hasDerivAt
  simpa [L.deriv_weierstrassP] using h.comp_add_const z w


theorem add_notMem_mem_nhds_zero (hw : w ∉ L.lattice) :
    {u : ℂ | u + w ∉ L.lattice} ∈ 𝓝 (0 : ℂ) :=
  IsOpen.mem_nhds
    (L.isClosed_lattice.isOpen_compl.preimage (continuous_id.add continuous_const))
    (by simpa using hw)


theorem analyticAt_weierstrassP_add_zero (hw : w ∉ L.lattice) :
    AnalyticAt ℂ (fun u => ℘[L] (u + w)) 0 := by
  have hd : DifferentiableOn ℂ (fun u => ℘[L] (u + w)) {u : ℂ | u + w ∉ L.lattice} := by
    intro u hu
    exact ((hasDerivAt_weierstrassP_add L) hu).differentiableAt.differentiableWithinAt
  exact (hd.analyticOnNhd
    (L.isClosed_lattice.isOpen_compl.preimage (continuous_id.add continuous_const)))
    0 (by simpa using hw)


/-- The regular Taylor core obtained after clearing the addition defect's fourth-order pole. -/
def additionCore (w : ℂ) (z : ℂ) : ℂ :=
  4 * ℘[L] (z + w) + (-8 * ℘[L] w) * (z ^ 2 * ℘[L] (z + w))
    + (-4 * ℘[L] w) + (-4 * ℘'[L] w) * z + (L.g₂ - 4 * ℘[L] w ^ 2) * z ^ 2


/-- The explicit first derivative of the regular addition core. -/
def additionCoreOne (w : ℂ) (z : ℂ) : ℂ :=
  4 * ℘'[L] (z + w)
    + (-8 * ℘[L] w) * (2 * z * ℘[L] (z + w) + z ^ 2 * ℘'[L] (z + w))
    + 0 + (-4 * ℘'[L] w) * 1 + (L.g₂ - 4 * ℘[L] w ^ 2) * (2 * z)


/-- The explicit second derivative of the regular addition core. -/
def additionCoreTwo (w : ℂ) (z : ℂ) : ℂ :=
  4 * deriv ℘'[L] (z + w)
    + (-8 * ℘[L] w) * (2 * ℘[L] (z + w) + 4 * z * ℘'[L] (z + w)
        + z ^ 2 * deriv ℘'[L] (z + w))
    + 0 + 0 + (L.g₂ - 4 * ℘[L] w ^ 2) * 2


theorem analyticAt_additionCore (hw : w ∉ L.lattice) : AnalyticAt ℂ ((additionCore L) w) 0 := by
  unfold additionCore
  have hP := (analyticAt_weierstrassP_add_zero L) hw
  fun_prop


theorem additionCore_zero : (additionCore L) w 0 = 0 := by
  simp only [additionCore, zero_add, zero_pow, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_mul]
  ring


theorem hasDerivAt_additionCore {z : ℂ} (hz : z + w ∉ L.lattice) :
    HasDerivAt ((additionCore L) w)
      (4 * ℘'[L] (z + w)
        + (-8 * ℘[L] w) * (2 * z * ℘[L] (z + w) + z ^ 2 * ℘'[L] (z + w))
        + 0 + (-4 * ℘'[L] w) * 1 + (L.g₂ - 4 * ℘[L] w ^ 2) * (2 * z)) z := by
  have hP : HasDerivAt (fun u => ℘[L] (u + w)) (℘'[L] (z + w)) z :=
    (hasDerivAt_weierstrassP_add L) hz
  have hid : HasDerivAt (fun u : ℂ => u) 1 z := hasDerivAt_id z
  have hz2 : HasDerivAt (fun u : ℂ => u ^ 2) (2 * z) z :=
    (hid.pow 2).congr_deriv (by ring)
  have hQ : HasDerivAt (fun u => u ^ 2 * ℘[L] (u + w))
      (2 * z * ℘[L] (z + w) + z ^ 2 * ℘'[L] (z + w)) z := hz2.mul hP
  exact ((((hP.const_mul 4).add (hQ.const_mul _)).add (hasDerivAt_const z _)).add
    (hid.const_mul _)).add (hz2.const_mul _)


theorem deriv_additionCore_eqNhds (hw : w ∉ L.lattice) :
    deriv ((additionCore L) w) =ᶠ[𝓝 0] (additionCoreOne L) w := by
  filter_upwards [(add_notMem_mem_nhds_zero L) hw] with z hz
  exact ((hasDerivAt_additionCore L) hz).deriv


theorem deriv_additionCore_zero (hw : w ∉ L.lattice) : deriv ((additionCore L) w) 0 = 0 := by
  rw [((deriv_additionCore_eqNhds L) hw).eq_of_nhds]
  simp only [additionCoreOne, zero_add, mul_zero, zero_mul, add_zero, mul_one]
  ring


end
end Dubon2026.SourceEllipticPeriod
