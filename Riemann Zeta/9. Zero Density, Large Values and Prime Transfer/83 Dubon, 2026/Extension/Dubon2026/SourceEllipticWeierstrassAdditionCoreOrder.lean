import Dubon2026.SourceEllipticWeierstrassAdditionCore

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

theorem hasDerivAt_additionCore₁ {z : ℂ} (hz : z + w ∉ L.lattice) :
    HasDerivAt ((additionCoreOne L) w)
      (4 * deriv ℘'[L] (z + w)
        + (-8 * ℘[L] w) * (2 * ℘[L] (z + w) + 4 * z * ℘'[L] (z + w)
            + z ^ 2 * deriv ℘'[L] (z + w))
        + 0 + 0 + (L.g₂ - 4 * ℘[L] w ^ 2) * 2) z := by
  have hP : HasDerivAt (fun u => ℘[L] (u + w)) (℘'[L] (z + w)) z :=
    (hasDerivAt_weierstrassP_add L) hz
  have hP' : HasDerivAt (fun u => ℘'[L] (u + w)) (deriv ℘'[L] (z + w)) z :=
    (L.analyticOnNhd_derivWeierstrassP (z + w) hz).differentiableAt.hasDerivAt.comp_add_const z w
  have hid : HasDerivAt (fun u : ℂ => u) 1 z := hasDerivAt_id z
  have hz2 : HasDerivAt (fun u : ℂ => u ^ 2) (2 * z) z :=
    (hid.pow 2).congr_deriv (by ring)
  have hQ : HasDerivAt (fun u => 2 * u * ℘[L] (u + w) + u ^ 2 * ℘'[L] (u + w))
      (2 * ℘[L] (z + w) + 4 * z * ℘'[L] (z + w) + z ^ 2 * deriv ℘'[L] (z + w)) z := by
    have h1 : HasDerivAt (fun u => 2 * u * ℘[L] (u + w))
        (2 * 1 * ℘[L] (z + w) + 2 * z * ℘'[L] (z + w)) z := (hid.const_mul 2).mul hP
    have h2 : HasDerivAt (fun u => u ^ 2 * ℘'[L] (u + w))
        (2 * z * ℘'[L] (z + w) + z ^ 2 * deriv ℘'[L] (z + w)) z := hz2.mul hP'
    exact (h1.add h2).congr_deriv (by ring)
  have h2z : HasDerivAt (fun u : ℂ => 2 * u) (2 : ℂ) z :=
    (hid.const_mul 2).congr_deriv (by ring)
  exact ((((hP'.const_mul 4).add (hQ.const_mul _)).add (hasDerivAt_const z _)).add
    (hasDerivAt_const z _)).add (h2z.const_mul _)


theorem deriv2_additionCore_eqNhds (hw : w ∉ L.lattice) :
    deriv (deriv ((additionCore L) w)) =ᶠ[𝓝 0] (additionCoreTwo L) w := by
  refine (((deriv_additionCore_eqNhds L) hw).deriv).trans ?_
  filter_upwards [(add_notMem_mem_nhds_zero L) hw] with z hz
  exact ((hasDerivAt_additionCore₁ L) hz).deriv


theorem deriv2_additionCore_zero (hw : w ∉ L.lattice) : deriv (deriv ((additionCore L) w)) 0 = 0 := by
  rw [((deriv2_additionCore_eqNhds L) hw).eq_of_nhds]
  simp only [additionCoreTwo, zero_add, mul_zero, zero_mul, add_zero]
  rw [(deriv_derivWeierstrassP L) hw]
  ring


theorem hasDerivAt_additionCore₂ {z : ℂ} (hz : z + w ∉ L.lattice) :
    HasDerivAt ((additionCoreTwo L) w)
      (4 * deriv (deriv ℘'[L]) (z + w)
        + (-8 * ℘[L] w) * (6 * ℘'[L] (z + w) + 6 * z * deriv ℘'[L] (z + w)
            + z ^ 2 * deriv (deriv ℘'[L]) (z + w))
        + 0 + 0 + 0) z := by
  have hP : HasDerivAt (fun u => ℘[L] (u + w)) (℘'[L] (z + w)) z :=
    (hasDerivAt_weierstrassP_add L) hz
  have hP' : HasDerivAt (fun u => ℘'[L] (u + w)) (deriv ℘'[L] (z + w)) z :=
    (L.analyticOnNhd_derivWeierstrassP (z + w) hz).differentiableAt.hasDerivAt.comp_add_const z w
  have hP'' : HasDerivAt (fun u => deriv ℘'[L] (u + w)) (deriv (deriv ℘'[L]) (z + w)) z :=
    ((L.analyticOnNhd_derivWeierstrassP (z + w)
      hz).deriv).differentiableAt.hasDerivAt.comp_add_const z w
  have hid : HasDerivAt (fun u : ℂ => u) 1 z := hasDerivAt_id z
  have hz2 : HasDerivAt (fun u : ℂ => u ^ 2) (2 * z) z :=
    (hid.pow 2).congr_deriv (by ring)
  have hQ : HasDerivAt
      (fun u => 2 * ℘[L] (u + w) + 4 * u * ℘'[L] (u + w) + u ^ 2 * deriv ℘'[L] (u + w))
      (6 * ℘'[L] (z + w) + 6 * z * deriv ℘'[L] (z + w)
        + z ^ 2 * deriv (deriv ℘'[L]) (z + w)) z := by
    have h1 : HasDerivAt (fun u => 4 * u * ℘'[L] (u + w))
        (4 * 1 * ℘'[L] (z + w) + 4 * z * deriv ℘'[L] (z + w)) z := (hid.const_mul 4).mul hP'
    have h2 : HasDerivAt (fun u => u ^ 2 * deriv ℘'[L] (u + w))
        (2 * z * deriv ℘'[L] (z + w) + z ^ 2 * deriv (deriv ℘'[L]) (z + w)) z := hz2.mul hP''
    exact (((hP.const_mul 2).add h1).add h2).congr_deriv (by ring)
  exact ((((hP''.const_mul 4).add (hQ.const_mul _)).add (hasDerivAt_const z _)).add
    (hasDerivAt_const z _)).add (hasDerivAt_const z _)


theorem deriv3_additionCore_eqNhds (hw : w ∉ L.lattice) :
    deriv (deriv (deriv ((additionCore L) w))) =ᶠ[𝓝 0]
      fun z => 4 * deriv (deriv ℘'[L]) (z + w)
        + (-8 * ℘[L] w) * (6 * ℘'[L] (z + w) + 6 * z * deriv ℘'[L] (z + w)
            + z ^ 2 * deriv (deriv ℘'[L]) (z + w))
        + 0 + 0 + 0 := by
  refine (((deriv2_additionCore_eqNhds L) hw).deriv).trans ?_
  filter_upwards [(add_notMem_mem_nhds_zero L) hw] with z hz
  exact ((hasDerivAt_additionCore₂ L) hz).deriv


theorem deriv3_additionCore_zero (hw : w ∉ L.lattice) : deriv (deriv (deriv ((additionCore L) w))) 0 = 0 := by
  rw [((deriv3_additionCore_eqNhds L) hw).eq_of_nhds]
  simp only [zero_add, mul_zero, zero_mul, add_zero]
  rw [(deriv2_derivWeierstrassP L) hw]
  ring


theorem additionCore_order_ge_four (hw : w ∉ L.lattice) :
    (4 : ℕ∞) ≤ analyticOrderAt ((additionCore L) w) 0 := by
  rw [show (4 : ℕ∞) = ((4 : ℕ) : ℕ∞) from rfl,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((analyticAt_additionCore L) hw)]
  intro i hi
  interval_cases i
  · simpa [iteratedDeriv_zero] using (additionCore_zero L)
  · simpa [iteratedDeriv_one] using (deriv_additionCore_zero L) hw
  · have : iteratedDeriv 2 ((additionCore L) w) = deriv (deriv ((additionCore L) w)) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [this]; exact (deriv2_additionCore_zero L) hw
  · have : iteratedDeriv 3 ((additionCore L) w) = deriv (deriv (deriv ((additionCore L) w))) := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
    rw [this]; exact (deriv3_additionCore_zero L) hw


end
end Dubon2026.SourceEllipticPeriod
