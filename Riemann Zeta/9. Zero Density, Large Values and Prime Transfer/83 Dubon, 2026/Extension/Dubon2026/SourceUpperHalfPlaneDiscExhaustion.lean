import Mathlib

/-! DUB-17/18 -> actual Gamma1 Picard/H1 -> principal-divisor converse ->
construct a meromorphic function with the prescribed divisor. The local
integer-residue expansion gives finite polar products on an exhaustion
by disks; analytic primitives of the regular part are exponentiated and
normalized to agree on overlaps. Local residue expansions remain an
explicit upstream analytic obligation, not a function-existence premise.
Adapted from anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue.lean,
Apache-2.0; retained LICENSE and NOTICE. -/

namespace Dubon2026.SourceUpperHalfPlaneMeromorphicPrimitive
open scoped Topology
open Filter Set Metric

theorem isPreconnected_range_diff_of_countable {e : ℂ → ℂ} (he : Continuous e)
    (hinj : Function.Injective e) {S : Set ℂ} (hS : S.Countable) :
    IsPreconnected (range e \ S) := by
  have h1 : (e ⁻¹' S).Countable := hS.preimage_of_injOn (hinj.injOn)
  have h2 : IsPathConnected (e ⁻¹' S)ᶜ :=
    h1.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
  have h3 : IsPathConnected (e '' (e ⁻¹' S)ᶜ) := h2.image' he.continuousOn
  have h4 : e '' (e ⁻¹' S)ᶜ = range e \ S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨mem_range_self w, hw⟩
    · rintro ⟨⟨w, rfl⟩, hz⟩
      exact ⟨w, hz, rfl⟩
  rw [← h4]
  exact h3.isConnected.isPreconnected

theorem isPreconnected_ball_diff_of_countable (c : ℂ) {r : ℝ} (hr : 0 < r) {S : Set ℂ}
    (hS : S.Countable) : IsPreconnected (ball c r \ S) := by
  let e := OpenPartialHomeomorph.univBall c r
  have hrange : range (e : ℂ → ℂ) = ball c r := by
    rw [← image_univ, ← OpenPartialHomeomorph.univBall_source c r, e.image_source_eq_target,
      OpenPartialHomeomorph.univBall_target c hr]
  have hinj : Function.Injective (e : ℂ → ℂ) := by
    intro x y hxy
    exact e.injOn (by rw [OpenPartialHomeomorph.univBall_source]; trivial)
      (by rw [OpenPartialHomeomorph.univBall_source]; trivial) hxy
  rw [← hrange]
  exact isPreconnected_range_diff_of_countable (OpenPartialHomeomorph.continuous_univBall c r)
    hinj hS

/-- Height of the center of the exhausting disk. -/
noncomputable def cht (n : ℕ) : ℝ := ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1)

/-- Actual complex center of the exhausting disk. -/
noncomputable def ctr (n : ℕ) : ℂ := (cht n : ℂ) * Complex.I

/-- Radius of the exhausting disk. -/
noncomputable def rad (n : ℕ) : ℝ := (n : ℝ) + 1

theorem rad_pos (n : ℕ) : 0 < rad n := by unfold rad; positivity

theorem ctr_im (n : ℕ) : (ctr n).im = cht n := by simp [ctr]

theorem ctr_re (n : ℕ) : (ctr n).re = 0 := by simp [ctr]

theorem cht_sub_rad (n : ℕ) : cht n - rad n = 1 / ((n : ℝ) + 1) := by unfold cht rad; ring

theorem im_pos_of_mem_closedBall {n : ℕ} {z : ℂ} (hz : z ∈ closedBall (ctr n) (rad n)) :
    0 < z.im := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h1 : |(z - ctr n).im| ≤ rad n := (Complex.abs_im_le_norm _).trans hz
  rw [Complex.sub_im, ctr_im] at h1
  have h2 : cht n - rad n ≤ z.im := by
    have := (abs_le.mp h1).1
    linarith
  rw [cht_sub_rad] at h2
  have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem im_pos_of_mem_ball {n : ℕ} {z : ℂ} (hz : z ∈ ball (ctr n) (rad n)) : 0 < z.im :=
  im_pos_of_mem_closedBall (ball_subset_closedBall hz)

theorem dist_ctr_succ (n : ℕ) : dist (ctr n) (ctr (n + 1)) ≤ 1 := by
  rw [dist_eq_norm]
  have : ctr n - ctr (n + 1) = ((cht n - cht (n + 1) : ℝ) : ℂ) * Complex.I := by
    simp [ctr]; ring
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h1 : cht (n + 1) - cht n = 1 + (1 / ((n : ℝ) + 2) - 1 / ((n : ℝ) + 1)) := by
    unfold cht; push_cast; ring
  have h2 : 0 ≤ cht (n + 1) - cht n := by
    rw [h1]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have h3 : cht (n + 1) - cht n ≤ 1 := by
    rw [h1]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  rw [abs_sub_comm, abs_of_nonneg h2]
  exact h3

theorem ball_mono_succ (n : ℕ) : ball (ctr n) (rad n) ⊆ ball (ctr (n + 1)) (rad (n + 1)) := by
  intro z hz
  rw [mem_ball] at hz ⊢
  calc dist z (ctr (n + 1)) ≤ dist z (ctr n) + dist (ctr n) (ctr (n + 1)) := dist_triangle _ _ _
    _ < rad n + 1 := add_lt_add_of_lt_of_le hz (dist_ctr_succ n)
    _ = rad (n + 1) := by unfold rad; push_cast; ring

theorem ball_mono {n k : ℕ} (h : n ≤ k) : ball (ctr n) (rad n) ⊆ ball (ctr k) (rad k) := by
  induction h with
  | refl => exact Subset.rfl
  | step _ ih => exact ih.trans (ball_mono_succ _)

theorem exists_mem_ball {z : ℂ} (hz : 0 < z.im) : ∃ n : ℕ, z ∈ ball (ctr n) (rad n) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((‖z‖ ^ 2 + 3) / (2 * z.im))
  refine ⟨n, ?_⟩
  have hn' : ‖z‖ ^ 2 + 3 < 2 * z.im * ((n : ℝ) + 1) := by
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  rw [mem_ball, dist_eq_norm]
  have hr : 0 ≤ rad n := (rad_pos n).le
  rw [← sq_lt_sq₀ (norm_nonneg _) hr, Complex.sq_norm, Complex.normSq_apply]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn'
  simp only [Complex.sub_re, Complex.sub_im, ctr_re, ctr_im, sub_zero]
  have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hε1 : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hcht : cht n = rad n + 1 / ((n : ℝ) + 1) := by unfold cht rad; ring
  set ε := 1 / ((n : ℝ) + 1) with hε_def
  have hεn : ((n : ℝ) + 1) * ε = 1 := by
    rw [hε_def]; field_simp
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
  rw [hcht]
  unfold rad
  nlinarith [sq_nonneg ε, hz, mul_pos hz hε, hεn, hε2, hn']

end Dubon2026.SourceUpperHalfPlaneMeromorphicPrimitive
