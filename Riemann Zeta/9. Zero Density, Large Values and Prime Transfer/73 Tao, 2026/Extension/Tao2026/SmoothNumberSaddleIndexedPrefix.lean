import Tao2026.SmoothNumberSaddleIndexedShellIntegral

/-!
# A vanishing growing prefix of indexed shells

Every fixed indexed shell contribution tends to zero, hence so does every
fixed finite prefix.  A second countable diagonal chooses a depth tending to
infinity for which the complete moving prefix is small, while retaining the
simultaneous shellwise cosine-loss assertions.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

noncomputable def smoothSaddleIndexedOuterPerronPrefix
    (K X y : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 2 K,
    smoothSaddleIndexedOuterPerronContribution k X y

/-- Every fixed finite indexed-shell prefix tends to zero. -/
theorem IsTaoCriticalSmoothRegime.tendsto_indexedOuterPerronPrefix_zero
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) (K : ℕ) :
    Tendsto (fun n => smoothSaddleIndexedOuterPerronPrefix
      K (X n) (y n)) atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum (Finset.Icc 2 K) (fun k hk =>
    hregime.tendsto_indexedOuterPerronContribution_zero hα
      (Finset.mem_Icc.mp hk).1)
  simpa only [smoothSaddleIndexedOuterPerronPrefix, Finset.sum_const_zero]
    using hsum

/-- One depth tends to infinity while its entire indexed-shell prefix tends
to zero and every shell in the prefix retains the full cosine-loss bound. -/
theorem IsTaoCriticalSmoothRegime.exists_vanishing_indexedOuterPerronPrefix
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) :
    ∃ K : ℕ → ℕ,
      Tendsto K atTop atTop ∧
      Tendsto (fun n => smoothSaddleIndexedOuterPerronPrefix
        (K n) (X n) (y n)) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ k : ℕ, 2 ≤ k → k ≤ K n →
        IndexedOuterShellLossAt X y n k := by
  let P : ℕ → ℕ → Prop := fun K n =>
    ‖smoothSaddleIndexedOuterPerronPrefix K (X n) (y n)‖ ≤
        1 / (K + 1 : ℝ) ∧
      ∀ k ∈ Finset.Icc 2 K, IndexedOuterShellLossAt X y n k
  have hP : ∀ K, ∀ᶠ n in atTop, P K n := by
    intro K
    have hprefix := hregime.tendsto_indexedOuterPerronPrefix_zero hα K
    have hnorm : Tendsto (fun n =>
        ‖smoothSaddleIndexedOuterPerronPrefix K (X n) (y n)‖)
        atTop (𝓝 0) := by
      simpa using hprefix.norm
    have hsmall : ∀ᶠ n in atTop,
        ‖smoothSaddleIndexedOuterPerronPrefix K (X n) (y n)‖ ≤
          1 / (K + 1 : ℝ) :=
      (hnorm.eventually (eventually_lt_nhds (by positivity))).mono
        (fun _ hn => hn.le)
    filter_upwards [hsmall,
      hregime.eventually_indexedOuterShellLoss_prefix hα K] with n hn hloss
    exact ⟨hn, hloss⟩
  obtain ⟨K, hK, hdiagonal⟩ :=
    GafniTao.exists_tendsto_nat_diagonal P hP
  have hbound : ∀ᶠ n in atTop,
      ‖smoothSaddleIndexedOuterPerronPrefix (K n) (X n) (y n)‖ ≤
        1 / (K n + 1 : ℝ) := hdiagonal.mono fun n hn => hn.1
  have hinv : Tendsto (fun n => 1 / (K n + 1 : ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop.comp hK).atTop_add tendsto_const_nhds)
  have hprefix : Tendsto (fun n => smoothSaddleIndexedOuterPerronPrefix
      (K n) (X n) (y n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
      hbound hinv
  refine ⟨K, hK, hprefix, ?_⟩
  filter_upwards [hdiagonal] with n hn
  intro k hkTwo hkK
  exact hn.2 k (Finset.mem_Icc.mpr ⟨hkTwo, hkK⟩)

end

end Tao2026
