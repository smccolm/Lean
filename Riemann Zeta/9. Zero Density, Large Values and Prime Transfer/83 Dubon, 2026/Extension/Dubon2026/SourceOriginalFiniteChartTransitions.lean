import Dubon2026.SourceOriginalFiniteCharts

/-! DUB-17/18 -> original torsion cardinality -> compatible actual
complex charts. Every pair of the finite-place charts constructed from
the original function field has open transition source and analytic
transition map. The proved branch-equality theorem is applied to their
actual uniformizers, original place families and pointwise order proofs.
Cusp charts and global compactness/Abel-Jacobi comparison remain open.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter
open scoped Topology
variable {N : ℕ} [NeZero N]
variable (v w : Place ℂ (modularFunctionFieldOver N ℂ))
variable (hv : jOver N ℂ ∈ v.toValuationSubring) (hw : jOver N ℂ ∈ w.toValuationSubring)

theorem finiteChart_trans_source :
    ((finiteChart N v hv).symm.trans (finiteChart N w hw)).source =
      {z | z ∈ Metric.ball 0 (finiteRadius N v hv) ∧
        finiteFamily N v hv z ∈ (finiteChart N w hw).source} := by
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
  rfl

private def overlapData (z z' : ℂ)
    (hz : z ∈ Metric.ball 0 (finiteRadius N v hv))
    (hz' : z' ∈ Metric.ball 0 (finiteRadius N w hw))
    (he : finiteFamily N w hw z' = finiteFamily N v hv z) : ComparisonData N where
  γ := finiteFamily N w hw
  γ' := finiteFamily N v hv
  v := w
  U := Metric.ball 0 (finiteRadius N w hw)
  U' := Metric.ball 0 (finiteRadius N v hv)
  z₀ := z'
  z₀' := z
  hU := Metric.isOpen_ball.mem_nhds hz'
  hU' := Metric.isOpen_ball.mem_nhds hz
  h₀ := he.symm
  ht := (finite_spec N w hw).2.2.2
  hγ := (finite_spec N w hw).2.2.1
  hγ' := (finite_spec N v hv).2.2.1

theorem isOpen_finiteChart_trans_source :
    IsOpen ((finiteChart N v hv).symm.trans (finiteChart N w hw)).source := by
  rw [finiteChart_trans_source, isOpen_iff_mem_nhds]
  rintro z ⟨hz, z', hz', he⟩
  let S := overlapData v w hv hw z z' hz hz' he
  have hB := S.eventually_place_eq
  have hin : ∀ᶠ u in 𝓝 z, S.transition u ∈ Metric.ball 0 (finiteRadius N w hw) :=
    S.tendsto_transition.eventually (Metric.isOpen_ball.mem_nhds hz')
  filter_upwards [hB, hin, Metric.isOpen_ball.mem_nhds hz] with u hu hu' hu''
  exact ⟨hu'', S.transition u, hu', hu.symm⟩

theorem analyticOnNhd_finiteChart_transition :
    AnalyticOnNhd ℂ ((finiteChart N v hv).symm.trans (finiteChart N w hw))
      ((finiteChart N v hv).symm.trans (finiteChart N w hw)).source := by
  intro z hz
  rw [finiteChart_trans_source] at hz
  obtain ⟨hz, z', hz', he⟩ := hz
  let S := overlapData v w hv hw z z' hz hz' he
  exact S.analyticAt_transition

end
end Dubon2026.SourceFunctionField.OriginalChart
