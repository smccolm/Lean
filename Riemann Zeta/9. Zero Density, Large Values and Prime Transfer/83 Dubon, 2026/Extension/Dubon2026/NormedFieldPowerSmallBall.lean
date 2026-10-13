import Dubon2026.NormedFieldPowerLocalScaling

/-! # Exact images of sufficiently small original unit balls under powers

The actual inverse function theorem and proved ultrametric scaling identify
power images of small balls. This supplies the local numerical-index route
for DUB-17 without an unproved principal-unit structure theorem.
-/

namespace Dubon2026
noncomputable section
open Filter Topology Metric

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- Every sufficiently small closed ball at the original unit one maps
bijectively to the ball with radius multiplied by the norm of the exponent. -/
theorem normedField_power_small_closedBall (n : ℕ) (hn : (n : K) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ s : ℝ, 0 < s → s ≤ r →
      Set.BijOn (fun x : K => x ^ n) (closedBall 1 s)
        (closedBall 1 (‖(n : K)‖ * s)) := by
  have hd : HasStrictDerivAt (fun x : K => x ^ n) (n : K) 1 := by
    simpa only [id_eq, one_pow, mul_one] using (hasStrictDerivAt_id (1 : K)).pow n
  let g := hd.localInverse (fun x : K => x ^ n) (n : K) 1 hn
  have hl : ∀ᶠ x in 𝓝 (1 : K), g (x ^ n) = x := hd.eventually_left_inverse hn
  have hr : ∀ᶠ y in 𝓝 (1 : K), (g y) ^ n = y := by
    simpa only [one_pow] using hd.eventually_right_inverse hn
  have hg : g 1 = 1 := by simpa only [one_pow] using hl.self_of_nhds
  have hc : ContinuousAt g 1 := by
    simpa only [one_pow] using (hd.to_localInverse hn).hasDerivAt.continuousAt
  have he := normedField_power_norm_sub_eventually K n hn
  have he' : ∀ᶠ y in 𝓝 (1 : K), ‖(g y) ^ n - 1‖ = ‖(n : K)‖ * ‖g y - 1‖ :=
    (show Tendsto g (𝓝 1) (𝓝 1) by
      change Tendsto g (𝓝 1) (𝓝 (g 1)) at hc
      simpa only [hg] using hc).eventually he
  obtain ⟨a, ha, hballa⟩ := Metric.mem_nhds_iff.mp (he.and hl)
  obtain ⟨b, hb, hballb⟩ := Metric.mem_nhds_iff.mp (hr.and he')
  have hnpos : 0 < ‖(n : K)‖ := norm_pos_iff.mpr hn
  let r := min (min a 1) (b / ‖(n : K)‖) / 2
  have hrpos : 0 < r := half_pos (lt_min (lt_min ha zero_lt_one) (div_pos hb hnpos))
  have hra : r < a := (half_lt_self (lt_min (lt_min ha zero_lt_one)
    (div_pos hb hnpos))).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hrone : r < 1 := (half_lt_self (lt_min (lt_min ha zero_lt_one)
    (div_pos hb hnpos))).trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hrb : ‖(n : K)‖ * r < b := by
    have h := (half_lt_self (lt_min (lt_min ha zero_lt_one)
      (div_pos hb hnpos))).trans_le (min_le_right (min a 1) (b / ‖(n : K)‖))
    simpa only [mul_comm] using (lt_div_iff₀ hnpos).mp h
  refine ⟨r, hrpos, hrone, ?_⟩
  intro s _hs hsr
  have hsource : ∀ x ∈ closedBall (1 : K) s,
      ‖x ^ n - 1‖ = ‖(n : K)‖ * ‖x - 1‖ ∧ g (x ^ n) = x := by
    intro x hx
    apply hballa
    exact (mem_closedBall.mp hx).trans_lt (hsr.trans_lt hra)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_closedBall, dist_eq_norm, (hsource x hx).1]
    exact mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hx) hnpos.le
  · intro x hx y hy hxy
    exact ((hsource x hx).2.symm.trans (congrArg g hxy)).trans (hsource y hy).2
  · intro y hy
    have hyt : y ∈ ball (1 : K) b :=
      (mem_closedBall.mp hy).trans_lt ((mul_le_mul_of_nonneg_left hsr hnpos.le).trans_lt hrb)
    obtain ⟨hgy, hnorm⟩ := hballb hyt
    refine ⟨g y, ?_, hgy⟩
    rw [mem_closedBall, dist_eq_norm]
    apply (mul_le_mul_iff_right₀ hnpos).mp
    rw [← hnorm, hgy]
    simpa only [mem_closedBall, dist_eq_norm] using hy

end
end Dubon2026
