import Dubon2026.SourceOriginalCompactChartCover

/-! DUB-17/18 -> original torsion cardinality -> complex Abel-Jacobi.
The actual original complex place manifold is compact. Finitely many
closed parameter disks cover it, and each inverse chart is continuous.
The finite cover is proved from actual original j fibers and their
principal-divisor multiplicities, with no compactness premise supplied.
Connectedness and the Abel-Jacobi comparison remain separate obligations.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Metric
variable (N : ℕ) [NeZero N]

theorem place_compactSpace :
    @CompactSpace (Place ℂ (modularFunctionFieldOver N ℂ)) (placeTopology N) := by
  letI := placeTopology N
  obtain ⟨S, r, hr, hcov⟩ := exists_original_compact_chart_cover N
  refine ⟨?_⟩
  have hK : IsCompact (⋃ v ∈ S, placeFamily N v '' closedBall (0 : ℂ) (r v)) := by
    refine S.finite_toSet.isCompact_biUnion fun v hv => ?_
    exact (isCompact_closedBall (0 : ℂ) (r v)).image_of_continuousOn
      ((continuousOn_placeFamily N v).mono (closedBall_subset_ball (hr v hv).2))
  refine hK.of_isClosed_subset isClosed_univ fun w _ => ?_
  obtain ⟨v, hv, z, hz, rfl⟩ := hcov w
  exact mem_iUnion₂.mpr ⟨v, hv, z, mem_closedBall_zero_iff.mpr hz, rfl⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
