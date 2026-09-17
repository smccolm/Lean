import Tao2026.SmoothNumberSaddleIndexedFixedLoss
import GafniTao.CountableDiagonal

/-!
# A growing diagonal of controlled indexed shells

Every fixed finite prefix of the indexed shell family is eventually
controlled.  The countable diagonal principle therefore selects a single
depth tending to infinity for which all shells below that depth satisfy the
critical-regime cosine-loss estimate simultaneously.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

/-- The complete cosine-loss assertion on indexed shell `k` at parameter
index `n`. -/
def IndexedOuterShellLossAt
    (X y : ℕ → ℕ) (n k : ℕ) : Prop :=
  ∀ t : ℝ,
    smoothSaddleIndexedOuterUpperHeight (k - 1) (y n) ≤ t →
    t ≤ smoothSaddleIndexedOuterUpperHeight k (y n) →
    (cepDyadicCofactorCutoff
        (smoothSaddleIteratedPrimeScale k (y n))
        (smoothRankinRatio (X n) (y n)) : ℝ) ^
          (1 - smoothSaddlePoint (X n) (y n)) /
        (16 * Real.log 2 *
          Real.log (smoothRankinRatio (X n) (y n))) ≤
      smoothSaddleCosineLoss (y n)
        (smoothSaddlePoint (X n) (y n)) t

/-- Every fixed finite prefix of indexed shells is eventually controlled
simultaneously. -/
theorem IsTaoCriticalSmoothRegime.eventually_indexedOuterShellLoss_prefix
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) (K : ℕ) :
    ∀ᶠ n in atTop, ∀ k ∈ Finset.Icc 2 K,
      IndexedOuterShellLossAt X y n k := by
  rw [Filter.eventually_all_finset]
  intro k hk
  have hkTwo : 2 ≤ k := List.left_le_of_mem_range' hk
  simpa only [IndexedOuterShellLossAt] using
    hregime.eventually_indexedOuterMultiShell_cosineLoss_lower hα hkTwo

/-- There is one shell depth tending to infinity such that, eventually, all
indexed shells from `2` through that depth obey their full loss estimate at
the same parameter value. -/
theorem IsTaoCriticalSmoothRegime.exists_indexedOuterShellLoss_diagonal
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) :
    ∃ K : ℕ → ℕ, Tendsto K atTop atTop ∧
      ∀ᶠ n in atTop, ∀ k : ℕ, 2 ≤ k → k ≤ K n →
        IndexedOuterShellLossAt X y n k := by
  let P : ℕ → ℕ → Prop := fun K n =>
    ∀ k ∈ Finset.Icc 2 K, IndexedOuterShellLossAt X y n k
  have hP : ∀ K, ∀ᶠ n in atTop, P K n := by
    intro K
    simpa only [P] using
      hregime.eventually_indexedOuterShellLoss_prefix hα K
  obtain ⟨K, hK, hdiagonal⟩ :=
    GafniTao.exists_tendsto_nat_diagonal P hP
  refine ⟨K, hK, ?_⟩
  filter_upwards [hdiagonal] with n hn
  intro k hkTwo hkK
  exact hn k (Finset.mem_Icc.mpr ⟨hkTwo, hkK⟩)

end

end Tao2026
