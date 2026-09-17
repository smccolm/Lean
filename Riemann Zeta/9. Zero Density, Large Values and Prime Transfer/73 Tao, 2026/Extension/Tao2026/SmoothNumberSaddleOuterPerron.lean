import Tao2026.SmoothNumberSaddleWidePerron

/-!
# The outer smooth-saddle Perron tails

This module names the two physical Perron tails beyond `pi / log y`.  It
decomposes the finite complementary line exactly into the already vanishing
principal-phase annulus plus these outer tails, identifies the corresponding
infinite-height object, and proves that the critical saddle asymptotic is
equivalent to decay of this outer object alone.
-/

open Filter Topology MeasureTheory Set
open scoped Interval

namespace Tao2026

noncomputable section

noncomputable def smoothSaddleOuterPerronLine
    (X y : ℕ) (T : ℝ) : ℂ :=
  ((smoothSaddleStandardDeviation X y : ℂ) /
      (Real.sqrt (2 * Real.pi) : ℂ)) *
    ((∫ t in (-T)..(-smoothSaddleWidePerronHeight X y),
        smoothSaddlePerronLineIntegrand X y t) +
      ∫ t in (smoothSaddleWidePerronHeight X y)..T,
        smoothSaddlePerronLineIntegrand X y t)

theorem smoothSaddleComplementaryPerronLine_eq_wideAnnular_add_outer
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (T : ℝ) :
    smoothSaddleComplementaryPerronLine X y T =
      smoothSaddleWideAnnularPerronContribution X y +
        smoothSaddleOuterPerronLine X y T := by
  let f := smoothSaddlePerronLineIntegrand X y
  let Hc := smoothSaddleCentralPerronHeight X y
  let Hw := smoothSaddleWidePerronHeight X y
  have hf : Continuous f := continuous_smoothSaddlePerronLineIntegrand hX hy
  have hleftOuter : IntervalIntegrable f volume (-T) (-Hw) :=
    hf.intervalIntegrable _ _
  have hleftAnnular : IntervalIntegrable f volume (-Hw) (-Hc) :=
    hf.intervalIntegrable _ _
  have hrightAnnular : IntervalIntegrable f volume Hc Hw :=
    hf.intervalIntegrable _ _
  have hrightOuter : IntervalIntegrable f volume Hw T :=
    hf.intervalIntegrable _ _
  have hleftSplit : (∫ t in (-T)..(-Hc), f t) =
      (∫ t in (-T)..(-Hw), f t) + ∫ t in (-Hw)..(-Hc), f t :=
    (intervalIntegral.integral_add_adjacent_intervals
      hleftOuter hleftAnnular).symm
  have hrightSplit : (∫ t in Hc..T, f t) =
      (∫ t in Hc..Hw, f t) + ∫ t in Hw..T, f t :=
    (intervalIntegral.integral_add_adjacent_intervals
      hrightAnnular hrightOuter).symm
  rw [smoothSaddleComplementaryPerronLine_eq_tailIntegrals hX hy]
  unfold smoothSaddleWideAnnularPerronContribution
    smoothSaddleOuterPerronLine
  change _ * ((∫ t in (-T)..(-Hc), f t) + ∫ t in Hc..T, f t) =
    _ * ((∫ t in (-Hw)..(-Hc), f t) + ∫ t in Hc..Hw, f t) +
      _ * ((∫ t in (-T)..(-Hw), f t) + ∫ t in Hw..T, f t)
  rw [hleftSplit, hrightSplit]
  ring

noncomputable def smoothSaddleInfiniteOuterPerronLine
    (X y : ℕ) : ℂ :=
  smoothSaddleInfiniteComplementaryPerronLine X y -
    smoothSaddleWideAnnularPerronContribution X y

theorem smoothSaddleInfiniteComplementaryPerronLine_eq_wideAnnular_add_outer
    (X y : ℕ) :
    smoothSaddleInfiniteComplementaryPerronLine X y =
      smoothSaddleWideAnnularPerronContribution X y +
        smoothSaddleInfiniteOuterPerronLine X y := by
  unfold smoothSaddleInfiniteOuterPerronLine
  ring

theorem tendsto_smoothSaddleOuterPerronLine_atTop_eq_infinite
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    Tendsto (smoothSaddleOuterPerronLine X y) atTop
      (nhds (smoothSaddleInfiniteOuterPerronLine X y)) := by
  have h :=
    (tendsto_smoothSaddleComplementaryPerronLine_atTop_eq_infinite hX hy).sub_const
      (smoothSaddleWideAnnularPerronContribution X y)
  apply h.congr'
  filter_upwards [] with T
  rw [smoothSaddleComplementaryPerronLine_eq_wideAnnular_add_outer hX hy]
  ring

theorem IsTaoCriticalSmoothRegime.tendsto_infiniteOuterPerronLine_zero_iff
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleInfiniteOuterPerronLine (X n) (y n))
        atTop (nhds 0) ↔
      Tendsto (fun n =>
        smoothSaddleInfiniteComplementaryPerronLine (X n) (y n))
        atTop (nhds 0) := by
  have hannular :=
    hregime.tendsto_smoothSaddleWideAnnularPerronContribution_zero hα
  constructor
  · intro houter
    have hsum := hannular.add houter
    have hsum' : Tendsto (fun n =>
        smoothSaddleWideAnnularPerronContribution (X n) (y n) +
          smoothSaddleInfiniteOuterPerronLine (X n) (y n))
        atTop (nhds 0) := by simpa using hsum
    apply hsum'.congr'
    filter_upwards [] with n
    exact (smoothSaddleInfiniteComplementaryPerronLine_eq_wideAnnular_add_outer
      (X n) (y n)).symm
  · intro hcomplement
    have hdiff := hcomplement.sub hannular
    simpa only [smoothSaddleInfiniteOuterPerronLine, sub_zero] using hdiff

theorem criticalSmoothSaddleAsymptotic_iff_infiniteOuterPerronLine
    : TaoCriticalSmoothSaddleAsymptoticConclusion ↔
      ∀ (α : ℝ) (X y : ℕ → ℕ), 0 < α →
        IsTaoCriticalSmoothRegime X y α →
          Tendsto (fun n =>
            smoothSaddleInfiniteOuterPerronLine (X n) (y n))
            atTop (nhds 0) := by
  rw [criticalSmoothSaddleAsymptotic_iff_infiniteComplementaryPerronLine]
  constructor
  · intro h α X y hα hregime
    exact (hregime.tendsto_infiniteOuterPerronLine_zero_iff hα).2
      (h α X y hα hregime)
  · intro h α X y hα hregime
    exact (hregime.tendsto_infiniteOuterPerronLine_zero_iff hα).1
      (h α X y hα hregime)

end

end Tao2026
