import Dubon2026.SourceMeromorphicRemovableCharts

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable [IsManifold 𝓘(ℂ, ℂ) ω M]

theorem exists_const_germs_of_nonneg_order [CompactSpace M] [ConnectedSpace M] (g : M → ℂ)
    (hg : ∀ x, MeromorphicAt (rd g x) (ctr x)) (hg0 : ∀ x, 0 ≤ meromorphicOrderAt (rd g x) (ctr x)) :
    ∃ C : ℂ, ∀ x, rd g x =ᶠ[𝓝[≠] (ctr x)] fun _ => C := by
  choose G hGan hGeq using fun x => exists_analyticAt_eventuallyEq (hg x) (hg0 x)
  have hkey : ∀ x, (fun z => G ((φ x).symm z) (ctr ((φ x).symm z))) =ᶠ[𝓝 (ctr x)] G x :=
    key g G hGan hGeq
  have han : ∀ x, AnalyticAt ℂ (fun z => (fun y => G y (ctr y)) ((φ x).symm z)) (ctr x) := fun x =>
    (hGan x).congr (hkey x).symm

  have hmd : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun y => G y (ctr y)) := fun x =>
    mdifferentiableAt_of_analyticAt _ x (han x)
  obtain ⟨C, hC⟩ := hmd.exists_eq_const_of_compactSpace
  refine ⟨C, fun x => ?_⟩
  have h1 : G x =ᶠ[𝓝 (ctr x)] fun _ => C := by
    filter_upwards [hkey x] with z hz
    rw [← hz]
    exact congrFun hC ((φ x).symm z)
  exact (hGeq x).trans (h1.filter_mono nhdsWithin_le_nhds)


end
end Dubon2026.SourceFunctionField.MeromorphicCompact
