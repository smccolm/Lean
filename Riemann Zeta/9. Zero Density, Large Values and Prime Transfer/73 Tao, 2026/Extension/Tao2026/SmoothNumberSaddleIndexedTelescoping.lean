import Tao2026.SmoothNumberSaddleIndexedPrefix

/-!
# Telescoping the indexed Perron-shell prefix

Adjacent symmetric shell contributions add exactly.  Hence the indexed
finite sum is the single symmetric Perron segment from indexed height one to
its terminal height.  Applying this identity to the slow prefix diagonal
gives a contiguous segment whose endpoint escapes through the indexed shell
family and whose normalized contribution tends to zero.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

/-- Adjacent normalized symmetric Perron shells concatenate exactly. -/
theorem smoothSaddleSymmetricPerronShellContribution_add_adjacent
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (a b c : ℝ) :
    smoothSaddleSymmetricPerronShellContribution X y a b +
        smoothSaddleSymmetricPerronShellContribution X y b c =
      smoothSaddleSymmetricPerronShellContribution X y a c := by
  let f := smoothSaddlePerronLineIntegrand X y
  have hf : Continuous f := continuous_smoothSaddlePerronLineIntegrand hX hy
  have hneg : (∫ t in (-c)..(-b), f t) + ∫ t in (-b)..(-a), f t =
      ∫ t in (-c)..(-a), f t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hpos : (∫ t in a..b, f t) + ∫ t in b..c, f t =
      ∫ t in a..c, f t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  unfold smoothSaddleSymmetricPerronShellContribution
  change _ * ((∫ t in (-b)..(-a), f t) + ∫ t in a..b, f t) +
      _ * ((∫ t in (-c)..(-b), f t) + ∫ t in b..c, f t) =
    _ * ((∫ t in (-c)..(-a), f t) + ∫ t in a..c, f t)
  rw [← hneg, ← hpos]
  ring

noncomputable def smoothSaddleIndexedOuterPerronSegment
    (K X y : ℕ) : ℂ :=
  smoothSaddleSymmetricPerronShellContribution X y
    (smoothSaddleIndexedOuterUpperHeight 1 y)
    (smoothSaddleIndexedOuterUpperHeight K y)

/-- The algebraic indexed prefix is exactly its contiguous symmetric Perron
segment. -/
theorem smoothSaddleIndexedOuterPerronPrefix_eq_segment
    {K X y : ℕ} (hK : 2 ≤ K) (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleIndexedOuterPerronPrefix K X y =
      smoothSaddleIndexedOuterPerronSegment K X y := by
  induction K, hK using Nat.le_induction with
  | base =>
      simp [smoothSaddleIndexedOuterPerronPrefix,
        smoothSaddleIndexedOuterPerronContribution,
        smoothSaddleIndexedOuterPerronSegment]
  | succ K hK ih =>
      unfold smoothSaddleIndexedOuterPerronPrefix
      rw [Finset.sum_Icc_succ_top (hK.trans (Nat.le_succ K))]
      change smoothSaddleIndexedOuterPerronPrefix K X y +
        smoothSaddleIndexedOuterPerronContribution (K + 1) X y =
          smoothSaddleIndexedOuterPerronSegment (K + 1) X y
      rw [ih]
      unfold smoothSaddleIndexedOuterPerronContribution
        smoothSaddleIndexedOuterPerronSegment
      rw [show K + 1 - 1 = K by omega]
      exact smoothSaddleSymmetricPerronShellContribution_add_adjacent
        hX hy _ _ _

/-- A moving contiguous indexed Perron segment reaches arbitrarily high
indexed endpoints while its normalized contribution tends to zero. -/
theorem IsTaoCriticalSmoothRegime.exists_vanishing_indexedOuterPerronSegment
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) :
    ∃ K : ℕ → ℕ,
      Tendsto K atTop atTop ∧
      Tendsto (fun n => smoothSaddleIndexedOuterPerronSegment
        (K n) (X n) (y n)) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ k : ℕ, 2 ≤ k → k ≤ K n →
        IndexedOuterShellLossAt X y n k := by
  obtain ⟨K, hK, hprefix, hloss⟩ :=
    hregime.exists_vanishing_indexedOuterPerronPrefix hα
  have htwo : ∀ᶠ n in atTop, 2 ≤ K n :=
    hK.eventually (eventually_ge_atTop 2)
  have hsegment : Tendsto (fun n => smoothSaddleIndexedOuterPerronSegment
      (K n) (X n) (y n)) atTop (𝓝 0) := by
    apply hprefix.congr'
    filter_upwards [htwo, hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hKn hX hy
    exact smoothSaddleIndexedOuterPerronPrefix_eq_segment hKn hX hy
  exact ⟨K, hK, hsegment, hloss⟩

end

end Tao2026
