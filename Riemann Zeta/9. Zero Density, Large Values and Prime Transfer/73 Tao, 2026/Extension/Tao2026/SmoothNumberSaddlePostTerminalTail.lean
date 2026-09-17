import Tao2026.SmoothNumberSaddleIndexedTelescoping
import Tao2026.SmoothNumberSaddleOuterPerron

/-!
# The post-terminal smooth-saddle Perron tail

The three already controlled outer pieces between the principal-phase cutoff
and indexed height one concatenate to one pre-indexed segment.  After the
moving indexed segment is removed from the infinite outer Perron line, the
remaining object is the genuine post-terminal tail.  This module proves that
decay of that single remainder is equivalent to the critical smooth-number
saddle asymptotic.
-/

open Filter Topology MeasureTheory Set
open scoped Interval

namespace Tao2026

noncomputable section

/-- The complete outer Perron segment before the indexed shell family. -/
noncomputable def smoothSaddlePreIndexedOuterPerronSegment
    (X y : ℕ) : ℂ :=
  smoothSaddleSymmetricPerronShellContribution X y
    (smoothSaddleWidePerronHeight X y)
    (smoothSaddleIndexedOuterUpperHeight 1 y)

/-- The first, extended, and second outer-shell contributions concatenate to
the pre-indexed segment. -/
theorem smoothSaddlePreIndexedOuterPerronSegment_eq
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddlePreIndexedOuterPerronSegment X y =
      smoothSaddleFirstOuterPerronContribution X y +
        smoothSaddleExtendedOuterPerronContribution X y +
          smoothSaddleSecondOuterPerronContribution X y := by
  rw [smoothSaddlePreIndexedOuterPerronSegment,
    smoothSaddleIndexedOuterUpperHeight_one]
  change smoothSaddleSymmetricPerronShellContribution X y
      (smoothSaddleWidePerronHeight X y)
      (smoothSaddleSecondOuterUpperHeight y) =
    smoothSaddleSymmetricPerronShellContribution X y
        (smoothSaddleWidePerronHeight X y)
        (smoothSaddleFirstOuterUpperHeight y) +
      smoothSaddleSymmetricPerronShellContribution X y
        (smoothSaddleFirstOuterUpperHeight y)
        (smoothSaddleExtendedOuterUpperHeight y) +
      smoothSaddleSymmetricPerronShellContribution X y
        (smoothSaddleExtendedOuterUpperHeight y)
        (smoothSaddleSecondOuterUpperHeight y)
  rw [smoothSaddleSymmetricPerronShellContribution_add_adjacent hX hy
      (smoothSaddleWidePerronHeight X y)
      (smoothSaddleFirstOuterUpperHeight y)
      (smoothSaddleExtendedOuterUpperHeight y),
    smoothSaddleSymmetricPerronShellContribution_add_adjacent hX hy
      (smoothSaddleWidePerronHeight X y)
      (smoothSaddleExtendedOuterUpperHeight y)
      (smoothSaddleSecondOuterUpperHeight y)]

/-- The whole pre-indexed outer segment is negligible in every critical
smooth regime. -/
theorem IsTaoCriticalSmoothRegime.tendsto_preIndexedOuterPerronSegment_zero
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) :
    Tendsto (fun n =>
      smoothSaddlePreIndexedOuterPerronSegment (X n) (y n))
      atTop (𝓝 0) := by
  have hsum :=
    ((hregime.tendsto_smoothSaddleFirstOuterPerronContribution_zero hα).add
      (hregime.tendsto_smoothSaddleExtendedOuterPerronContribution_zero hα)).add
      (hregime.tendsto_smoothSaddleSecondOuterPerronContribution_zero hα)
  have hsum' : Tendsto (fun n =>
      smoothSaddleFirstOuterPerronContribution (X n) (y n) +
        smoothSaddleExtendedOuterPerronContribution (X n) (y n) +
          smoothSaddleSecondOuterPerronContribution (X n) (y n))
      atTop (𝓝 0) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hX hy
  exact (smoothSaddlePreIndexedOuterPerronSegment_eq hX hy).symm

/-- What remains of the infinite outer line after the pre-indexed piece and a
finite indexed segment have been removed. -/
noncomputable def smoothSaddlePostTerminalPerronTail
    (K X y : ℕ) : ℂ :=
  smoothSaddleInfiniteOuterPerronLine X y -
    smoothSaddlePreIndexedOuterPerronSegment X y -
      smoothSaddleIndexedOuterPerronSegment K X y

/-- Exact decomposition of the infinite outer line at any indexed terminal
height. -/
theorem smoothSaddleInfiniteOuterPerronLine_eq_preIndexed_add_segment_add_postTerminal
    (K X y : ℕ) :
    smoothSaddleInfiniteOuterPerronLine X y =
      smoothSaddlePreIndexedOuterPerronSegment X y +
        smoothSaddleIndexedOuterPerronSegment K X y +
          smoothSaddlePostTerminalPerronTail K X y := by
  unfold smoothSaddlePostTerminalPerronTail
  ring

/-- Once the indexed segment vanishes, decay of the post-terminal tail is
equivalent to decay of the full infinite outer Perron line. -/
theorem IsTaoCriticalSmoothRegime.tendsto_postTerminalPerronTail_zero_iff
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) (K : ℕ → ℕ)
    (hsegment : Tendsto (fun n => smoothSaddleIndexedOuterPerronSegment
      (K n) (X n) (y n)) atTop (𝓝 0)) :
    Tendsto (fun n => smoothSaddlePostTerminalPerronTail
        (K n) (X n) (y n)) atTop (𝓝 0) ↔
      Tendsto (fun n => smoothSaddleInfiniteOuterPerronLine (X n) (y n))
        atTop (𝓝 0) := by
  have hpre := hregime.tendsto_preIndexedOuterPerronSegment_zero hα
  constructor
  · intro htail
    have hsum := (hpre.add hsegment).add htail
    have hsum' : Tendsto (fun n =>
        smoothSaddlePreIndexedOuterPerronSegment (X n) (y n) +
          smoothSaddleIndexedOuterPerronSegment (K n) (X n) (y n) +
            smoothSaddlePostTerminalPerronTail (K n) (X n) (y n))
        atTop (𝓝 0) := by
      simpa using hsum
    apply hsum'.congr'
    filter_upwards [] with n
    exact (smoothSaddleInfiniteOuterPerronLine_eq_preIndexed_add_segment_add_postTerminal
      (K n) (X n) (y n)).symm
  · intro houter
    have hdiff := (houter.sub hpre).sub hsegment
    simpa only [smoothSaddlePostTerminalPerronTail, sub_zero] using hdiff

/-- The exact remaining smooth-saddle obligation: choose the already
available growing indexed segment and prove that its post-terminal remainder
vanishes. -/
theorem criticalSmoothSaddleAsymptotic_iff_exists_vanishing_postTerminalPerronTail :
    TaoCriticalSmoothSaddleAsymptoticConclusion ↔
      ∀ (α : ℝ) (X y : ℕ → ℕ), 0 < α →
        IsTaoCriticalSmoothRegime X y α →
          ∃ K : ℕ → ℕ,
            Tendsto K atTop atTop ∧
            Tendsto (fun n => smoothSaddleIndexedOuterPerronSegment
              (K n) (X n) (y n)) atTop (𝓝 0) ∧
            (∀ᶠ n in atTop, ∀ k : ℕ, 2 ≤ k → k ≤ K n →
              IndexedOuterShellLossAt X y n k) ∧
            Tendsto (fun n => smoothSaddlePostTerminalPerronTail
              (K n) (X n) (y n)) atTop (𝓝 0) := by
  rw [criticalSmoothSaddleAsymptotic_iff_infiniteOuterPerronLine]
  constructor
  · intro houter α X y hα hregime
    obtain ⟨K, hK, hsegment, hloss⟩ :=
      hregime.exists_vanishing_indexedOuterPerronSegment hα
    have htail :=
      (hregime.tendsto_postTerminalPerronTail_zero_iff hα K hsegment).2
        (houter α X y hα hregime)
    exact ⟨K, hK, hsegment, hloss, htail⟩
  · intro h α X y hα hregime
    obtain ⟨K, _hK, hsegment, _hloss, htail⟩ := h α X y hα hregime
    exact (hregime.tendsto_postTerminalPerronTail_zero_iff
      hα K hsegment).1 htail

end

end Tao2026
