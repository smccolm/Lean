import Dubon2026.SourceMeromorphicEffectivePoleBound
import Dubon2026.SourceOriginalMeromorphicDimension

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. The finite effective pole divisor is constructed
on the actual original places, with all geometric assumptions discharged.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Topology
open scoped Manifold ContDiff
variable (N : ℕ) [NeZero N]

theorem exists_original_effective_meromorphic_pole_bound
    (g : Place ℂ (modularFunctionFieldOver N ℂ) → ℂ)
    (hg : ∀ v, MeromorphicAt (fun z => g (placeFamily N v z)) 0) :
    ∃ E : Divisor ℂ (modularFunctionFieldOver N ℂ), (∀ v, 0 ≤ E v) ∧
      ∀ v, ((-E v : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun z => g (placeFamily N v z)) 0 := by
  letI := placeTopology N
  letI := placeChartedSpace N
  letI := place_isManifold N
  letI := place_compactSpace N
  letI := place_connectedSpace N
  have hm : ∀ v, MeromorphicAt (MeromorphicCompact.rd g v)
      (MeromorphicCompact.ctr v) := by
    simpa only [MeromorphicCompact.rd, MeromorphicCompact.φ,
      MeromorphicCompact.ctr, extPlaceChart_symm_apply, extPlaceChart_self] using hg
  simpa only [MeromorphicCompact.rd, MeromorphicCompact.φ,
    MeromorphicCompact.ctr, extPlaceChart_symm_apply, extPlaceChart_self] using
      MeromorphicCompact.exists_effective_pole_bound g hm

end
end Dubon2026.SourceFunctionField.OriginalChart
