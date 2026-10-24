import Dubon2026.SourceEllipticWeierstrassAdditionDomain

/-! Remove the actual addition defect's singularities at the two lattice
cosets and apply periodic Liouville. This proves the generic x-coordinate
addition formula for the native Weierstrass functions, required for the
uniformization map and the DUB-17/18 odd-prime quotient-product identity.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean. -/

namespace Dubon2026.SourceEllipticPeriod
noncomputable section
open Complex Filter Set
open scoped PeriodPair Topology
variable (L : PeriodPair) {w : ℂ}

theorem additionPhi_removable_at_zero (hw : w ∉ L.lattice) :
    ∃ B, AnalyticAt ℂ B (0 : ℂ) ∧ (additionPhi L) w =ᶠ[𝓝[≠] (0 : ℂ)] B := by

  have hER : AnalyticAt ℂ (fun z => (additionCore L) w z + (additionRemainder L) w z) 0 :=
    ((analyticAt_additionCore L) hw).add ((analyticAt_additionRemainder L) hw)
  obtain ⟨B, hB_an, hB_eq⟩ := (natCast_le_analyticOrderAt hER).mp
    ((additionCore_add_R_order_ge_four L) hw)
  refine ⟨B, hB_an, ?_⟩

  filter_upwards [(compl_lattice_mem_nhdsNE L) 0,
    mem_nhdsWithin_of_mem_nhds ((add_notMem_mem_nhds_zero L) hw),
    self_mem_nhdsWithin, hB_eq.filter_mono nhdsWithin_le_nhds] with z hzL hzwL hz0 hzB
  have hbridge := (addBridge_identity L) hzL hw hz0
  rw [hzB] at hbridge
  simp only [sub_zero, smul_eq_mul] at hbridge
  exact mul_left_cancel₀ (pow_ne_zero 4 hz0) hbridge


theorem sq_mul_weierstrassP_add_eq {z : ℂ} (hz : z + w ≠ 0) :
    (z + w) ^ 2 * ℘[L] (z + w) = 1 + (z + w) ^ 2 * L.weierstrassPExcept (0 : ℂ) (z + w) := by
  have h := PeriodPair.weierstrassPExcept_add L ⟨0, zero_mem _⟩ (z + w)
  simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero, one_div] at h
  rw [show ℘[L] (z + w) = ((z + w) ^ 2)⁻¹ + L.weierstrassPExcept (0 : ℂ) (z + w) from by
    linear_combination -h, mul_add, mul_inv_cancel₀ (pow_ne_zero 2 hz)]


theorem additionPhi_removable_at_neg (hw : w ∉ L.lattice) :
    ∃ B, AnalyticAt ℂ B (-w) ∧ (additionPhi L) w =ᶠ[𝓝[≠] (-w)] B := by

  have hnw : -w ∉ L.lattice := fun h => hw (by simpa using neg_mem h)
  have hPw : ℘[L] (-w) = ℘[L] w := L.weierstrassP_neg w
  have hP_an : AnalyticAt ℂ (fun z => ℘[L] z - ℘[L] w) (-w) :=
    (L.analyticOnNhd_weierstrassP (-w) hnw).sub analyticAt_const
  have hord : (1 : ℕ∞) ≤ analyticOrderAt (fun z => ℘[L] z - ℘[L] w) (-w) := by
    rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl,
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hP_an]
    intro i hi; interval_cases i
    simp [hPw]
  obtain ⟨g, hg_an, hg_eq⟩ := (natCast_le_analyticOrderAt hP_an).mp hord

  refine ⟨fun z => 4 * g z ^ 2 *
      (1 + (z + w) ^ 2 * L.weierstrassPExcept (0 : ℂ) (z + w) + (z + w) ^ 2 * (℘[L] z + ℘[L] w))
    - (℘'[L] z - ℘'[L] w) ^ 2, ?_, ?_⟩
  · have hE' : AnalyticAt ℂ (fun z => L.weierstrassPExcept (0 : ℂ) (z + w)) (-w) := by
      have hd : DifferentiableOn ℂ (fun z => L.weierstrassPExcept (0 : ℂ) (z + w))
          {z : ℂ | z + w ∉ (L.lattice : Set ℂ) \ {0}} := fun u hu =>
        ((L.analyticOnNhd_weierstrassPExcept (0 : ℂ) (u + w)
          hu).differentiableAt.comp u (differentiableAt_id.add_const w)).differentiableWithinAt
      exact hd.analyticOnNhd
        (L.isOpen_compl_lattice_diff.preimage (continuous_id.add continuous_const))
        (-w) (by simp)
    have hP := L.analyticOnNhd_weierstrassP (-w) hnw
    have hP' := L.analyticOnNhd_derivWeierstrassP (-w) hnw
    fun_prop
  ·
    have hmem : (L.lattice : Set ℂ)ᶜ ∈ 𝓝 (-w) := L.isClosed_lattice.isOpen_compl.mem_nhds hnw
    filter_upwards [mem_nhdsWithin_of_mem_nhds hmem, self_mem_nhdsWithin,
      hg_eq.filter_mono nhdsWithin_le_nhds] with z hzL hzne hzg
    have hzw0 : z + w ≠ 0 := fun h => hzne (eq_neg_of_add_eq_zero_left h)
    unfold additionPhi
    simp only [sub_neg_eq_add, pow_one, smul_eq_mul] at hzg

    have hsq := (sq_mul_weierstrassP_add_eq L) hzw0
    rw [hzg]
    linear_combination 4 * g z ^ 2 * hsq


end
end Dubon2026.SourceEllipticPeriod
