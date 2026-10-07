import Dubon2026.PhasePolynomialDegree

/-! # Generic local constancy of the actual multiplicity count on a vertical segment -/

namespace Dubon2026

open Filter MeasureTheory Complex
open scoped Topology

noncomputable section

/-- Actual twisted zeros on the prescribed vertical segment, retaining analytic multiplicity. -/
def twistVerticalLineZeroCount (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u H σ : ℝ) (z : PrimeTorus N) : ℕ :=
  ∑ s ∈ (zerosInOpenRectangleFinset (twistedCoefficients a N z) N hN
    (by rwa [twistedCoefficients_one]) l u H).filter (fun s => s.re = σ),
      zeroMultiplicity (twistedCoefficients a N z) N s

theorem phase_vertical_count_locally_ae_constant (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : PrimeCoordinate N → ℝ) {l u T H σ : ℝ}
    (hl : l < σ) (hu : σ < u) (hT : 0 ≤ T) (hH : H ≤ T)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      complexPhaseFamily a N (complexifyPhase x, s) ≠ 0) :
    ∃ r > 0, ∀ᵐ y ∂(volume : Measure (PrimeCoordinate N → ℝ)).restrict (Metric.ball x r),
      ∀ᶠ z in 𝓝 y,
        twistVerticalLineZeroCount a N hN ha l u H σ (fun p => (z p : UnitAddCircle)) =
          twistVerticalLineZeroCount a N hN ha l u H σ (fun p => (y p : UnitAddCircle)) := by
  obtain ⟨d, hd⟩ := exists_uniform_phaseVerticalRealPolynomial_degree_bound a N hN ha l u T σ
  obtain ⟨r, hr, hc⟩ := analytic_polynomial_root_count_locally_ae_constant volume hd
    (analyticAt_phaseVerticalRealPolynomial_coeff hN ha x (hl.trans hu).le hT hn σ) (-H) H
  refine ⟨r, hr, ?_⟩
  filter_upwards [hc] with y hy
  filter_upwards [hy] with z hz
  rw [phase_real_root_count_eq_twice_vertical_count a N hN ha hl hu hH z,
    phase_real_root_count_eq_twice_vertical_count a N hN ha hl hu hH y] at hz
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < (2 : ℕ)) hz

theorem phase_vertical_count_locally_ae_continuous (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : PrimeCoordinate N → ℝ) {l u T H σ : ℝ}
    (hl : l < σ) (hu : σ < u) (hT : 0 ≤ T) (hH : H ≤ T)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      complexPhaseFamily a N (complexifyPhase x, s) ≠ 0) :
    ∃ r > 0, ∀ᵐ y ∂(volume : Measure (PrimeCoordinate N → ℝ)).restrict (Metric.ball x r),
      ContinuousAt (fun z => twistVerticalLineZeroCount a N hN ha l u H σ
        (fun p => (z p : UnitAddCircle))) y := by
  obtain ⟨r, hr, hc⟩ := phase_vertical_count_locally_ae_constant a N hN ha x hl hu hT hH hn
  refine ⟨r, hr, hc.mono ?_⟩
  intro y hy
  exact continuousAt_const.congr (hy.mono fun _ h => h.symm)

end

end Dubon2026
