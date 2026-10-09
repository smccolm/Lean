import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Order.Filter.Pi

/-! # Genuine congruence neighborhoods and continuous discrete quotients -/

namespace Dubon2026

noncomputable section
open Filter Set
open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G]
  {H : ℕ → Type*} [∀ n, Group (H n)] [∀ n, TopologicalSpace (H n)]
  [∀ n, DiscreteTopology (H n)]

/-- An actual embedding in discrete quotient coordinates with decreasing kernels supplies a genuine congruence neighborhood basis. -/
theorem discreteReduction_kernel_neighborhood
    (π : ∀ n, G →* H n)
    (hπ : Topology.IsEmbedding (fun g n => π n g))
    (hmono : Antitone (fun n => (π n).ker))
    (U : Set G) (hU : U ∈ 𝓝 (1 : G)) :
    ∃ N : ℕ, ((π N).ker : Set G) ⊆ U := by
  have hb : (𝓝 (fun n => π n (1 : G))).HasBasis Set.Finite
      (fun S => {g | ∀ n ∈ S, g n = π n (1 : G)}) := by
    simpa only [nhds_pi, nhds_discrete] using
      Filter.hasBasis_pi_pure (fun n => π n (1 : G))
  obtain ⟨S, hS, hs⟩ := (hπ.isInducing.basis_nhds hb).mem_iff.mp hU
  obtain ⟨N, hN⟩ := hS.bddAbove
  refine ⟨N, ?_⟩
  intro g hg
  apply hs
  change ∀ n ∈ S, π n g = π n (1 : G)
  intro n hn
  rw [map_one]
  exact hmono (hN hn) hg

/-- Every continuous map to an original discrete group kills a sufficiently deep genuine congruence kernel. -/
theorem discreteReduction_kernel_le_continuous_kernel
    (π : ∀ n, G →* H n)
    (hπ : Topology.IsEmbedding (fun g n => π n g))
    (hmono : Antitone (fun n => (π n).ker))
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →* Q) (hf : Continuous f) : ∃ N : ℕ, (π N).ker ≤ f.ker := by
  have hker : (f.ker : Set G) ∈ 𝓝 (1 : G) :=
    ((isOpen_discrete ({1} : Set Q)).preimage hf).mem_nhds (by simp)
  exact discreteReduction_kernel_neighborhood π hπ hmono f.ker hker

/-- When the actual reduction images are p-groups, every original continuous discrete quotient is a p-group. -/
theorem discreteReduction_continuous_quotient_isPGroup
    (π : ∀ n, G →* H n)
    (hπ : Topology.IsEmbedding (fun g n => π n g))
    (hmono : Antitone (fun n => (π n).ker)) (p : ℕ)
    (hP : ∀ n, IsPGroup p (π n).range)
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →* Q) (hf : Continuous f) (hsurj : Function.Surjective f) :
    IsPGroup p Q := by
  obtain ⟨N, hN⟩ := discreteReduction_kernel_le_continuous_kernel π hπ hmono f hf
  intro q
  obtain ⟨g, rfl⟩ := hsurj q
  obtain ⟨k, hk⟩ := hP N ((π N).rangeRestrict g)
  refine ⟨k, ?_⟩
  have hg : g ^ (p ^ k) ∈ (π N).ker := by
    change π N (g ^ (p ^ k)) = 1
    rw [map_pow]
    exact congrArg Subtype.val hk
  have hfg : f (g ^ (p ^ k)) = 1 := hN hg
  simpa only [map_pow] using hfg

end
end Dubon2026
