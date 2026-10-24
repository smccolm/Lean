import Dubon2026.SourceEllipticPeriodicLiouville
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

/-! Native covering-space lifting for the actual period lattice. A continuous
lift is holomorphic whenever its quotient map has holomorphic local lifts;
their difference is lattice-valued and hence locally constant. This is used
to identify the already proved odd quotient map with a scalar on complex
uniformizations, required by the DUB-17/18 modular-polynomial product.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex Filter Set
open scoped Topology

theorem isDiscrete_lattice (L : PeriodPair) :
    IsDiscrete (L.lattice.toAddSubgroup : Set ℂ) := by
  rw [Submodule.coe_toAddSubgroup, isDiscrete_iff_discreteTopology]
  exact inferInstanceAs (DiscreteTopology L.lattice)

theorem isCoveringMap_mk_lattice (L : PeriodPair) :
    IsCoveringMap (QuotientAddGroup.mk (s := L.lattice.toAddSubgroup)) :=
  (AddSubgroup.isAddQuotientCoveringMap_of_comm L.lattice.toAddSubgroup
    (isDiscrete_lattice L)).isCoveringMap

theorem differentiable_of_local_lifts (L : PeriodPair) {F : ℂ → ℂ} (hFc : Continuous F)
    (hloc : ∀ z₀ : ℂ, ∃ U ∈ 𝓝 z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, (QuotientAddGroup.mk (s := L.lattice.toAddSubgroup) (F z) :
        ℂ ⧸ L.lattice.toAddSubgroup) = QuotientAddGroup.mk (G z)) :
    Differentiable ℂ F := by
  intro z₀
  obtain ⟨U, hU, G, hGd, heq⟩ := hloc z₀
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  set V := Metric.ball z₀ ε
  have hVnhds : V ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hε
  have hz₀V : z₀ ∈ V := Metric.mem_ball_self hε
  have hmem : Set.MapsTo (fun z => F z - G z) V (L.lattice.toAddSubgroup : Set ℂ) := by
    intro z hz
    have h0 : (QuotientAddGroup.mk (s := L.lattice.toAddSubgroup) (F z - G z)
        : ℂ ⧸ L.lattice.toAddSubgroup) = 0 := by
      rw [QuotientAddGroup.mk_sub, heq z (hεU hz), sub_self]
    exact (QuotientAddGroup.eq_zero_iff _).mp h0
  have hcont : ContinuousOn (fun z => F z - G z) V :=
    hFc.continuousOn.sub (hGd.mono hεU).continuousOn
  have hconst : ∀ z ∈ V, F z - G z = F z₀ - G z₀ := fun z hz =>
    (convex_ball z₀ ε).isPreconnected.constant_of_mapsTo (isDiscrete_lattice L)
      hcont hmem hz hz₀V
  have hFeq : ∀ z ∈ V, F z = F z₀ - G z₀ + G z := fun z hz => by
    rw [← hconst z hz, sub_add_cancel]
  exact (((differentiableOn_const (F z₀ - G z₀)).add (hGd.mono hεU)).congr
    (fun z hz => hFeq z hz)).differentiableAt hVnhds

end Dubon2026.SourceEllipticPeriod
