import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Tactic

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison -> dimension bound for analytic meromorphic
functions. Native meromorphic normal form fills each removable point.
Analytic transition maps make these local fillings agree, producing a
holomorphic function on the actual compact complex curve downstream.
Adapted from S_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.MeromorphicCompact
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff Topology

theorem exists_analyticAt_eventuallyEq {f : ℂ → ℂ} {c : ℂ} (hf : MeromorphicAt f c)
    (h0 : 0 ≤ meromorphicOrderAt f c) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G c ∧ f =ᶠ[𝓝[≠] c] G := by
  refine ⟨toMeromorphicNFAt f c, ?_, hf.eq_nhdsNE_toMeromorphicNFAt⟩
  apply meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rwa [← meromorphicOrderAt_congr hf.eq_nhdsNE_toMeromorphicNFAt]

theorem eventually_eventually_of_punctured {c : ℂ} {P : ℂ → Prop}
    (h : ∀ᶠ z in 𝓝[≠] c, P z) : ∀ᶠ z in 𝓝[≠] c, ∀ᶠ z' in 𝓝 z, P z' := by
  rw [eventually_nhdsWithin_iff] at h ⊢
  filter_upwards [h.eventually_nhds] with z hz hne
  have hne' : ∀ᶠ z' in 𝓝 z, z' ≠ c := isOpen_compl_singleton.mem_nhds hne
  filter_upwards [hz, hne'] with z' h1 h2
  exact h1 h2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- The actual extended coordinate chart at a manifold point. -/
abbrev φ (x : M) : PartialEquiv M ℂ := extChartAt 𝓘(ℂ, ℂ) x

/-- The coordinate of the actual center of an extended chart. -/
abbrev ctr (x : M) : ℂ := extChartAt 𝓘(ℂ, ℂ) x x

/-- The local coordinate reading of the given function on the manifold. -/
abbrev rd (g : M → ℂ) (x : M) : ℂ → ℂ := fun z => g ((φ x).symm z)

theorem rd_eq_comp (g : M → ℂ) {x y : M} {w : ℂ} (hw : (φ y).symm w ∈ (φ x).source) :
    rd g y w = rd g x (φ x ((φ y).symm w)) := by
  simp only [rd]
  rw [(φ x).left_inv hw]

theorem eventually_symm_mem_source {x y : M} {w : ℂ} (hw : w ∈ (φ y).target)
    (hx : (φ y).symm w ∈ (φ x).source) : ∀ᶠ w' in 𝓝 w, (φ y).symm w' ∈ (φ x).source :=
  (continuousAt_extChartAt_symm'' hw).preimage_mem_nhds (extChartAt_source_mem_nhds' hx)

variable [IsManifold 𝓘(ℂ, ℂ) ω M]

theorem analyticAt_transition (x y : M) {w : ℂ} (hw : w ∈ (φ y).target)
    (hx : (φ y).symm w ∈ (φ x).source) : AnalyticAt ℂ (φ x ∘ (φ y).symm) w := by
  have hcd := contDiffOn_ext_coord_change (I := 𝓘(ℂ, ℂ)) (n := ω) x y
  have hsrc : ((φ y).symm ≫ φ x).source ∈ 𝓝 w := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    refine Filter.inter_mem (extChartAt_target_mem_nhds' hw) ?_
    exact (continuousAt_extChartAt_symm'' hw).preimage_mem_nhds (extChartAt_source_mem_nhds' hx)
  exact (hcd.contDiffAt hsrc).analyticAt

theorem key (g : M → ℂ) (G : M → ℂ → ℂ) (hGan : ∀ x, AnalyticAt ℂ (G x) (ctr x))
    (hGeq : ∀ x, rd g x =ᶠ[𝓝[≠] (ctr x)] G x) (x : M) :
    (fun z => G ((φ x).symm z) (ctr ((φ x).symm z))) =ᶠ[𝓝 (ctr x)] G x := by

  have hoff : ∀ᶠ z in 𝓝[≠] (ctr x), G ((φ x).symm z) (ctr ((φ x).symm z)) = G x z := by
    have h1 := eventually_eventually_of_punctured (hGeq x)
    have h2 : ∀ᶠ z in 𝓝[≠] (ctr x), AnalyticAt ℂ (G x) z :=
      mem_nhdsWithin_of_mem_nhds (hGan x).eventually_analyticAt
    have h3 : ∀ᶠ z in 𝓝[≠] (ctr x), z ∈ (φ x).target :=
      mem_nhdsWithin_of_mem_nhds (extChartAt_target_mem_nhds x)
    filter_upwards [h1, h2, h3] with z hz1 hz2 hzt

    set y : M := (φ x).symm z with hy
    have hysrc : y ∈ (φ x).source := (φ x).map_target hzt
    have hτ0 : (φ x ∘ (φ y).symm) (ctr y) = z := by
      show φ x ((φ y).symm (ctr y)) = z
      rw [extChartAt_to_inv, hy, (φ x).right_inv hzt]
    have hτc : ContinuousAt (φ x ∘ (φ y).symm) (ctr y) :=
      (analyticAt_transition x y (mem_extChartAt_target y)
        (by rw [extChartAt_to_inv]; exact hysrc)).continuousAt

    have hchg : rd g y =ᶠ[𝓝 (ctr y)] (G x ∘ (φ x ∘ (φ y).symm)) := by
      have hs : ∀ᶠ w in 𝓝 (ctr y), (φ y).symm w ∈ (φ x).source :=
        eventually_symm_mem_source (mem_extChartAt_target y)
          (by rw [extChartAt_to_inv]; exact hysrc)
      have hG : ∀ᶠ w in 𝓝 (ctr y), rd g x ((φ x ∘ (φ y).symm) w) = G x ((φ x ∘ (φ y).symm) w) := by
        have : ∀ᶠ w' in 𝓝 ((φ x ∘ (φ y).symm) (ctr y)), rd g x w' = G x w' := by
          rw [hτ0]; exact hz1
        exact hτc.eventually this
      filter_upwards [hs, hG] with w hw hGw
      rw [rd_eq_comp g hw]
      exact hGw

    have hlim1 : Tendsto (rd g y) (𝓝[≠] (ctr y)) (𝓝 (G y (ctr y))) :=
      ((hGan y).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (hGeq y).symm
    have hlim2 : Tendsto (rd g y) (𝓝[≠] (ctr y)) (𝓝 (G x z)) := by
      have hc : ContinuousAt (G x ∘ (φ x ∘ (φ y).symm)) (ctr y) := by
        refine ContinuousAt.comp ?_ hτc
        rw [hτ0]; exact hz2.continuousAt
      have := hc.tendsto
      rw [Function.comp_apply, hτ0] at this
      exact (this.mono_left nhdsWithin_le_nhds).congr'
        (hchg.filter_mono nhdsWithin_le_nhds).symm
    exact tendsto_nhds_unique hlim1 hlim2

  rw [Filter.EventuallyEq, ← nhdsNE_sup_pure, eventually_sup]
  refine ⟨hoff, ?_⟩
  rw [eventually_pure, extChartAt_to_inv]

omit [IsManifold 𝓘(ℂ, ℂ) ω M] in

theorem mdifferentiableAt_of_analyticAt (gt : M → ℂ) (x : M)
    (han : AnalyticAt ℂ (fun z => gt ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x)) :
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) gt x := by
  rw [mdifferentiableAt_iff]
  constructor
  · have hc : ContinuousAt ((fun z => gt ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) ∘ extChartAt 𝓘(ℂ, ℂ) x)
        x := han.continuousAt.comp (continuousAt_extChartAt x)
    refine hc.congr ?_
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) x] with y hy
    simp only [Function.comp_apply]
    rw [(extChartAt 𝓘(ℂ, ℂ) x).left_inv hy]
  · have : writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x gt =
        fun z => gt ((extChartAt 𝓘(ℂ, ℂ) x).symm z) := by
      ext z
      simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
        Function.comp_apply, id_eq]
    rw [this]
    exact han.differentiableAt.differentiableWithinAt

end
end Dubon2026.SourceFunctionField.MeromorphicCompact
