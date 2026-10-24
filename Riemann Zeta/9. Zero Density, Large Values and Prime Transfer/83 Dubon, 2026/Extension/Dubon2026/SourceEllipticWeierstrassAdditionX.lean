import Dubon2026.SourceEllipticWeierstrassAdditionRemovable
import Dubon2026.SourceEllipticPeriodCurve

/-! Remove the actual addition defect's singularities at the two lattice
cosets and apply periodic Liouville. This proves the generic x-coordinate
addition formula for the native Weierstrass functions, required for the
uniformization map and the DUB-17/18 odd-prime quotient-product identity.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean. -/

namespace Dubon2026.SourceEllipticPeriod
noncomputable section
open Complex Filter Set WeierstrassCurve
open scoped PeriodPair Topology
variable (L : PeriodPair) {w : ℂ}

theorem elliptic_Liouville_zero (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice)
    {H : ℂ → ℂ} (hHan : AnalyticOnNhd ℂ H ((additionPhiDomain L) w))
    (hHper : ∀ l ∈ L.lattice, ∀ z, H (z + l) = H z)
    (hH0 : ∃ B, AnalyticAt ℂ B (0 : ℂ) ∧ H =ᶠ[𝓝[≠] (0 : ℂ)] B)
    (hHnw : ∃ B, AnalyticAt ℂ B (-w) ∧ H =ᶠ[𝓝[≠] (-w)] B)
    (hHw : H w = 0) {z : ℂ} (hz : z ∉ L.lattice) (hzw : z + w ∉ L.lattice) :
    H z = 0 := by
  classical
  obtain ⟨B₀, hB₀_an, hB₀_eq⟩ := hH0
  obtain ⟨B₁, hB₁_an, hB₁_eq⟩ := hHnw

  let Φext : ℂ → ℂ := fun u => if u ∈ L.lattice then B₀ 0
    else if u + w ∈ L.lattice then B₁ (-w) else H u
  have hΦD : ∀ u ∈ (additionPhiDomain L) w, Φext u = H u := fun u ⟨h1, h2⟩ => by
    simp only [Φext, if_neg h1, if_neg h2]

  have hper : ∀ l ∈ L.lattice, ∀ u, Φext (u + l) = Φext u := by
    intro l hl u
    by_cases h1 : u ∈ L.lattice
    · simp only [Φext, if_pos h1, if_pos (add_mem h1 hl)]
    have h1' : u + l ∉ L.lattice := fun h => h1 (by simpa using sub_mem h hl)
    by_cases h2 : u + w ∈ L.lattice
    · have h2' : u + l + w ∈ L.lattice := by
        rw [show u + l + w = u + w + l from by ring]; exact add_mem h2 hl
      simp only [Φext, if_neg h1, if_neg h1', if_pos h2, if_pos h2']
    · have h2' : u + l + w ∉ L.lattice := fun h => h2 (by
        rw [show u + l + w = u + w + l from by ring] at h; simpa using sub_mem h hl)
      rw [hΦD u ⟨h1, h2⟩, hΦD (u + l) ⟨h1', h2'⟩, hHper l hl u]

  have hDdiff : DifferentiableOn ℂ Φext ((additionPhiDomain L) w) :=
    hHan.differentiableOn.congr hΦD

  have hdiff0 : DifferentiableAt ℂ Φext 0 := by
    set s := ((L.lattice : Set ℂ) \ {0})ᶜ ∩ {u | u + w ∉ L.lattice} with hs_def
    have hs_nhds : s ∈ 𝓝 (0 : ℂ) :=
      Filter.inter_mem (L.compl_lattice_diff_singleton_mem_nhds 0)
        ((add_notMem_mem_nhds_zero L) hw)
    have hs_diff : s \ {(0 : ℂ)} = (additionPhiDomain L) w ∩ s := by
      ext u; simp only [hs_def, mem_diff, mem_inter_iff, mem_compl_iff, mem_singleton_iff,
        mem_setOf_eq, additionPhiDomain]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨fun hu => h1 ⟨hu, h3⟩, h2⟩, ⟨h1, h2⟩⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h3, fun h => h1 (h ▸ zero_mem _)⟩
    have hcont : ContinuousAt Φext 0 := by
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt,
        show Φext 0 = B₀ 0 from if_pos (zero_mem _)]
      refine Tendsto.congr' ?_ (hB₀_an.continuousAt.continuousWithinAt)
      filter_upwards [mem_nhdsWithin_of_mem_nhds hs_nhds, self_mem_nhdsWithin, hB₀_eq]
        with u ⟨h1, h2⟩ h3 h4
      rw [hΦD u ⟨fun hu => h1 ⟨hu, h3⟩, h2⟩, h4]
    exact ((differentiableOn_compl_singleton_and_continuousAt_iff hs_nhds).mp
      ⟨hs_diff ▸ hDdiff.mono inter_subset_left, hcont⟩).differentiableAt hs_nhds

  have hnw : -w ∉ L.lattice := fun h => hw (by simpa using neg_mem h)
  have hdiff_nw : DifferentiableAt ℂ Φext (-w) := by
    set s := (L.lattice : Set ℂ)ᶜ ∩ ({u | u + w ∈ L.lattice} \ {-w})ᶜ with hs_def
    have hs_nhds : s ∈ 𝓝 (-w) := by
      refine Filter.inter_mem (L.isClosed_lattice.isOpen_compl.mem_nhds hnw) ?_
      have hpre : {u : ℂ | u + w ∈ L.lattice} \ {-w} =
          (· + w) ⁻¹' ((L.lattice : Set ℂ) \ {0}) := by
        ext u
        simp only [mem_diff, mem_preimage, mem_singleton_iff, mem_setOf_eq, SetLike.mem_coe,
          and_congr_right_iff]
        exact fun _ => ⟨fun h1 h2 => h1 (eq_neg_of_add_eq_zero_left h2),
          fun h1 h2 => h1 (by rw [h2, _root_.neg_add_cancel])⟩
      rw [hpre, ← Set.preimage_compl]
      refine (continuous_add_const w).continuousAt.preimage_mem_nhds ?_
      rw [_root_.neg_add_cancel]; exact L.compl_lattice_diff_singleton_mem_nhds 0
    have hs_diff : s \ {-w} = (additionPhiDomain L) w ∩ s := by
      ext u; simp only [hs_def, mem_diff, mem_inter_iff, mem_compl_iff, mem_singleton_iff,
        mem_setOf_eq, additionPhiDomain]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, fun hu => h2 ⟨hu, h3⟩⟩, ⟨h1, h2⟩⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h3, fun h => h2 (h ▸ by simp)⟩
    have hcont : ContinuousAt Φext (-w) := by
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt,
        show Φext (-w) = B₁ (-w) from by
          simp only [Φext, if_neg hnw, _root_.neg_add_cancel, if_pos (zero_mem _)]]
      refine Tendsto.congr' ?_ (hB₁_an.continuousAt.continuousWithinAt)
      filter_upwards [mem_nhdsWithin_of_mem_nhds hs_nhds, self_mem_nhdsWithin, hB₁_eq]
        with u ⟨h1, h2⟩ h3 h4
      rw [hΦD u ⟨h1, fun hu => h2 ⟨hu, h3⟩⟩, h4]
    exact ((differentiableOn_compl_singleton_and_continuousAt_iff hs_nhds).mp
      ⟨hs_diff ▸ hDdiff.mono inter_subset_left, hcont⟩).differentiableAt hs_nhds

  have hshift : ∀ l ∈ L.lattice, Φext = fun v => Φext (v - l) := fun l hl =>
    funext fun v => by rw [← hper l hl (v - l), sub_add_cancel]
  have hdiff : Differentiable ℂ Φext := by
    intro u
    by_cases h1 : u ∈ L.lattice
    · rw [hshift u h1]
      exact DifferentiableAt.comp (f := fun v => v - u) u
        (by simp only [sub_self]; exact hdiff0) (differentiableAt_id.sub_const u)
    by_cases h2 : u + w ∈ L.lattice
    · rw [hshift (u + w) h2]
      exact DifferentiableAt.comp (f := fun v => v - (u + w)) u
        (by simp only [sub_add_cancel_left]; exact hdiff_nw)
        (differentiableAt_id.sub_const (u + w))
    · exact (hDdiff u ⟨h1, h2⟩).differentiableAt ((isOpen_additionPhiDomain L).mem_nhds ⟨h1, h2⟩)

  have hconst := (periodic_entire_constant L) hdiff hper

  have hwD : w ∈ (additionPhiDomain L) w := ⟨hw, by rwa [← two_mul]⟩
  calc H z = Φext z := (hΦD z ⟨hz, hzw⟩).symm
    _ = Φext w := hconst z w
    _ = H w := hΦD w hwD
    _ = 0 := hHw


theorem additionPhi_eq_zero (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice)
    {z : ℂ} (hz : z ∉ L.lattice) (hzw : z + w ∉ L.lattice) :
    (additionPhi L) w z = 0 :=
  (elliptic_Liouville_zero L) hw h2w (analyticOnNhd_additionPhi L) ((additionPhi_periodic L))
    ((additionPhi_removable_at_zero L) hw) ((additionPhi_removable_at_neg L) hw)
    (additionPhi_self_eq_zero L) hz hzw


theorem weierstrassP_add_eq_addX (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice)
    {z : ℂ} (hz : z ∉ L.lattice) (hzw : z + w ∉ L.lattice) (hne : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w) = (periodCurve L).toAffine.addX (℘[L] z) (℘[L] w)
      ((periodCurve L).toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2)) := by
  have hΦ := (additionPhi_eq_zero L) hw h2w hz hzw
  unfold additionPhi at hΦ
  rw [Affine.slope_of_X_ne hne, Affine.addX]
  simp only [periodCurve]
  have hne' : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hne
  field_simp
  linear_combination hΦ


end
end Dubon2026.SourceEllipticPeriod
