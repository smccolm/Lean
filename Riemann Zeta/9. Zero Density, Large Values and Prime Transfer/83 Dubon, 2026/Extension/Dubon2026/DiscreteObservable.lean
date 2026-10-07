import Dubon2026.OrbitProbability

/-! # Bounded integer observables under weak convergence

A natural-valued function is locally constant at each continuity point. Thus its
level sets have null frontier whenever its discontinuity set is null. A finite
level-set decomposition then extends weak convergence to its integral. These are
explicit regularity hypotheses; the actual zero-count observable needs its own
proof of them.
-/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology ENNReal BigOperators

noncomputable section

theorem notMem_frontier_level_of_continuousAt {X : Type*} [TopologicalSpace X]
    {g : X → ℕ} {x : X} (hg : ContinuousAt g x) (k : ℕ) :
    x ∉ frontier {y | g y = k} := by
  have he : ∀ᶠ y in 𝓝 x, g y = g x := by
    have hh := hg (isOpen_discrete ({g x} : Set ℕ) |>.mem_nhds (Set.mem_singleton _))
    simpa only [Set.mem_singleton_iff] using hh
  by_cases hx : g x = k
  · have hi : x ∈ interior {y | g y = k} :=
      mem_interior_iff_mem_nhds.mpr (he.mono (fun y hy => hy.trans hx))
    exact fun h => h.2 hi
  · have hi : x ∈ interior ({y | g y = k}ᶜ) :=
      mem_interior_iff_mem_nhds.mpr (he.mono (fun y hy h => hx (hy.symm.trans h)))
    rw [← frontier_compl]
    exact fun h => h.2 hi

theorem measure_frontier_level_eq_zero {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] (μ : Measure X) {g : X → ℕ}
    (hg : ∀ᵐ x ∂μ, ContinuousAt g x) (k : ℕ) :
    μ (frontier {x | g x = k}) = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  exact hg.mono (fun _ h => notMem_frontier_level_of_continuousAt h k)

theorem natCast_eq_sum_level_indicators {X : Type*} (g : X → ℕ) (K : ℕ)
    (hK : ∀ x, g x ≤ K) (x : X) :
    (g x : ℝ) = ∑ k ∈ Finset.range (K + 1),
      ({y | g y = k} : Set X).indicator (fun _ => (k : ℝ)) x := by
  classical
  symm
  rw [Finset.sum_eq_single (g x)]
  · simp
  · intro k _ hk
    simp [Set.indicator_of_notMem, Ne.symm hk]
  · intro hx
    exact (hx (Finset.mem_range.mpr (Nat.lt_succ_of_le (hK x)))).elim

theorem integral_natCast_eq_sum_levels {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {g : X → ℕ}
    (hg : Measurable g) (K : ℕ) (hK : ∀ x, g x ≤ K) :
    (∫ x, (g x : ℝ) ∂μ) = ∑ k ∈ Finset.range (K + 1),
      (μ {x | g x = k}).toReal * k := by
  classical
  have hs (k : ℕ) : MeasurableSet {x | g x = k} := hg (measurableSet_singleton k)
  calc
    (∫ x, (g x : ℝ) ∂μ) = ∫ x, ∑ k ∈ Finset.range (K + 1),
        ({y | g y = k} : Set X).indicator (fun _ => (k : ℝ)) x ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (natCast_eq_sum_level_indicators g K hK)
    _ = ∑ k ∈ Finset.range (K + 1),
        ∫ x, ({y | g y = k} : Set X).indicator (fun _ => (k : ℝ)) x ∂μ :=
      integral_finsetSum _ (fun k _ => (integrable_const (k : ℝ)).indicator (hs k))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_indicator_const _ (hs k)]
      rfl

theorem tendsto_integral_bounded_nat_of_ae_continuous {X ι : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {L : Filter ι} {μs : ι → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (hμ : Tendsto μs L (𝓝 μ)) {g : X → ℕ}
    (hg : Measurable g) (hgc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt g x)
    (K : ℕ) (hK : ∀ x, g x ≤ K) :
    Tendsto (fun i => ∫ x, (g x : ℝ) ∂(μs i : Measure X)) L
      (𝓝 (∫ x, (g x : ℝ) ∂(μ : Measure X))) := by
  simp only [integral_natCast_eq_sum_levels _ hg K hK]
  apply tendsto_finsetSum
  intro k _
  have hs := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hμ (measure_frontier_level_eq_zero (μ : Measure X) hgc k)
  exact ((ENNReal.tendsto_toReal (measure_ne_top (μ : Measure X) _)).comp hs).mul_const (k : ℝ)

end

end Dubon2026
