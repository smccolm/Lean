import Dubon2026.PhaseVerticalCountRegularity
import Dubon2026.ZeroFreeBoundaries

/-! # Almost-everywhere regularity of actual vertical-line counts in real phase coordinates -/

namespace Dubon2026

open Filter Set MeasureTheory Complex
open scoped Topology

noncomputable section

theorem ae_of_locally_ae_ball {V : Type*} [PseudoMetricSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] (μ : Measure V) {P : V → Prop}
    (h : ∀ x, ∃ r > 0, ∀ᵐ y ∂μ.restrict (Metric.ball x r), P y) :
    ∀ᵐ y ∂μ, P y := by
  classical
  choose r hr hg using h
  obtain ⟨t, _, ht, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := Set.univ) (f := fun x => Metric.ball x (r x)) (fun x _ =>
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (hr x)))
  have hh : ∀ᵐ y ∂μ.restrict (⋃ x ∈ t, Metric.ball x (r x)), P y :=
    (ae_restrict_biUnion_iff (fun x => Metric.ball x (r x)) ht _).mpr (fun x _ => hg x)
  simpa only [Measure.restrict_univ] using ae_restrict_of_ae_restrict_of_subset hcover hh

/-- Once the line is interior, the auxiliary vertical sides do not change its count. -/
theorem twistVerticalLineZeroCount_eq_of_bounds {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u L U σ : ℝ}
    (hl : l < σ) (hu : σ < u) (hL : L < σ) (hU : σ < U)
    (H : ℝ) (z : PrimeTorus N) :
    twistVerticalLineZeroCount a N hN ha l u H σ z =
      twistVerticalLineZeroCount a N hN ha L U H σ z := by
  classical
  unfold twistVerticalLineZeroCount
  congr 1
  ext s
  simp only [Finset.mem_filter, mem_zerosInOpenRectangleFinset]
  constructor
  · rintro ⟨⟨_, _, ht, hz⟩, he⟩
    exact ⟨⟨by simpa only [he] using hL, by simpa only [he] using hU, ht, hz⟩, he⟩
  · rintro ⟨⟨_, _, ht, hz⟩, he⟩
    exact ⟨⟨by simpa only [he] using hl, by simpa only [he] using hu, ht, hz⟩, he⟩

theorem ae_real_phase_vertical_count_locally_constant {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u σ : ℝ} (hl : l < σ) (hu : σ < u) (H : ℝ) :
    ∀ᵐ y ∂(volume : Measure (PrimeCoordinate N → ℝ)), ∀ᶠ z in 𝓝 y,
      twistVerticalLineZeroCount a N hN ha l u H σ (fun p => (z p : UnitAddCircle)) =
        twistVerticalLineZeroCount a N hN ha l u H σ (fun p => (y p : UnitAddCircle)) := by
  apply ae_of_locally_ae_ball
  intro x
  have hx : twistedCoefficients a N (fun p => (x p : UnitAddCircle)) 1 ≠ 0 := by
    rwa [twistedCoefficients_one]
  obtain ⟨L, hL, hnL⟩ := exists_zero_free_vertical_line hN hx
    (show σ - 1 < σ by linarith)
  obtain ⟨U, hU, hnU⟩ := exists_zero_free_vertical_line hN hx
    (show σ < σ + 1 by linarith)
  obtain ⟨T, hT, hnT⟩ := exists_zero_free_symmetric_height hN hx
    (show max H 0 < max H 0 + 1 by linarith)
  have hTp : 0 ≤ T := (le_max_right H 0).trans hT.1.le
  have hn := rectangle_boundary_ne_zero_of_lines hTp hnL hnU hnT
  have hnc : ∀ s ∈ RectangleBorder (⟨L, -T⟩ : ℂ) (⟨U, T⟩ : ℂ),
      complexPhaseFamily a N (complexifyPhase x, s) ≠ 0 := by
    intro s hs
    change complexPhaseFamily a N ((fun p => (x p : ℂ)), s) ≠ 0
    rw [complexPhaseFamily_real]
    exact hn s hs
  obtain ⟨r, hr, hg⟩ := phase_vertical_count_locally_ae_constant a N hN ha x hL.2 hU.1 hTp
    ((le_max_left H 0).trans hT.1.le) hnc
  refine ⟨r, hr, ?_⟩
  filter_upwards [hg] with y hy
  filter_upwards [hy] with z hz
  simpa only [twistVerticalLineZeroCount_eq_of_bounds hN ha hl hu hL.2 hU.1] using hz

end

end Dubon2026
