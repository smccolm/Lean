import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tight

/-! # Tightness and weak probability convergence from neighborhood mass concentration -/

namespace Dubon2026

open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- A compact set carrying asymptotically all mass gives tightness of the full sequence. -/
theorem isTightMeasureSet_of_compact_complement_limit
    (μ : ℕ → ProbabilityMeasure ℝ) {K : Set ℝ} (hK : IsCompact K)
    (hlim : Tendsto (fun N => (μ N : Measure ℝ) Kᶜ) atTop (𝓝 0)) :
    IsTightMeasureSet (range (fun N => (μ N : Measure ℝ))) := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  have hsingle (N : ℕ) : ∃ L : Set ℝ, IsCompact L ∧ (μ N : Measure ℝ) Lᶜ ≤ ε := by
    obtain ⟨L, hL, hb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_singleton (μ := (μ N : Measure ℝ))) ε hε
    exact ⟨L, hL, hb _ (mem_singleton _)⟩
  choose L hL hb using hsingle
  refine ⟨K ∪ ⋃ n ∈ Finset.range N₀, L n,
    hK.union ((Finset.range N₀).finite_toSet.isCompact_biUnion (fun n _ => hL n)), ?_⟩
  rintro ν ⟨N, rfl⟩
  by_cases hN : N₀ ≤ N
  · exact (measure_mono (compl_subset_compl.mpr subset_union_left)).trans (hN₀ N hN).le
  · have hs : L N ⊆ K ∪ ⋃ n ∈ Finset.range N₀, L n := by
      intro x hx
      exact Or.inr (mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), hx⟩⟩)
    exact (measure_mono (compl_subset_compl.mpr hs)).trans (hb N)

/-- Weak convergence in the actual probability-measure topology, not only compact-test convergence. -/
theorem tendsto_probability_dirac_of_Ioo (μ : ℕ → ProbabilityMeasure ℝ) (α : ℝ)
    (h : ∀ l u : ℝ, l < α → α < u →
      Tendsto (fun N => (μ N : Measure ℝ) (Ioo l u)) atTop (𝓝 1)) :
    Tendsto μ atTop (𝓝 (⟨Measure.dirac α, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  apply MeasureTheory.tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  change Measure.dirac α G ≤ _
  by_cases hα : α ∈ G
  · rw [Measure.dirac_apply' _ hG.measurableSet, indicator_of_mem hα, Pi.one_apply]
    obtain ⟨l, u, hαlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hG.mem_nhds hα)
    rw [← (h l u hαlu.1 hαlu.2).liminf_eq]
    exact Filter.liminf_le_liminf (Eventually.of_forall fun N => measure_mono hsub)
  · rw [Measure.dirac_apply' _ hG.measurableSet, indicator_of_notMem hα]
    exact bot_le

/-- An interval with mass tending to one supplies a concrete compact set for tightness. -/
theorem isTightMeasureSet_of_Ioo_limit (μ : ℕ → ProbabilityMeasure ℝ) {l u : ℝ}
    (h : Tendsto (fun N => (μ N : Measure ℝ) (Ioo l u)) atTop (𝓝 1)) :
    IsTightMeasureSet (range (fun N => (μ N : Measure ℝ))) := by
  have hc : Tendsto (fun N => (μ N : Measure ℝ) (Ioo l u)ᶜ) atTop (𝓝 0) := by
    have hh := ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl ENNReal.one_ne_top)
    simpa only [measure_compl measurableSet_Ioo (measure_ne_top _ _), measure_univ,
      tsub_self] using hh
  apply isTightMeasureSet_of_compact_complement_limit μ isCompact_Icc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => bot_le)
    (fun _ => measure_mono (compl_subset_compl.mpr Ioo_subset_Icc_self))

end Dubon2026
