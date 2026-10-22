import Dubon2026.SourceMeromorphicDimensionBound
import Dubon2026.SourceOriginalComplexConnected

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. The actual original place manifold supplies
compactness, connectedness and analytic charts to the meromorphic dimension
bound. These geometric properties are proved inputs, not theorem premises.
The relation concerns the actual original uniformizer families.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Topology
open scoped Manifold ContDiff
variable (N : ℕ) [NeZero N]

theorem exists_original_meromorphic_relation
    (D : Place ℂ (modularFunctionFieldOver N ℂ) →₀ ℕ)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Place ℂ (modularFunctionFieldOver N ℂ) → ℂ)
    (hψ : ∀ i v, MeromorphicAt (fun z => ψ i (placeFamily N v z)) 0)
    (hord : ∀ i v, ((-(D v : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z => ψ i (placeFamily N v z)) 0)
    (hcard : (D.sum fun _ n => n) + 1 < Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ ∀ v,
      (fun z => ∑ i, c i * ψ i (placeFamily N v z)) =ᶠ[𝓝[≠] 0] 0 := by
  letI := placeTopology N
  letI := placeChartedSpace N
  letI := place_isManifold N
  letI := place_compactSpace N
  letI := place_connectedSpace N
  have hm : ∀ i v, MeromorphicAt
      (fun z => ψ i ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
      (extChartAt 𝓘(ℂ, ℂ) v v) := by
    simpa only [extPlaceChart_symm_apply, extPlaceChart_self] using hψ
  have ho : ∀ i v, ((-(D v : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z => ψ i ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
        (extChartAt 𝓘(ℂ, ℂ) v v) := by
    simpa only [extPlaceChart_symm_apply, extPlaceChart_self] using hord
  simpa only [extPlaceChart_symm_apply, extPlaceChart_self] using
    MeromorphicCompact.exists_relation_of_degree_lt_card D ψ hm ho hcard

theorem exists_original_const_germs_of_nonneg_order
    (g : Place ℂ (modularFunctionFieldOver N ℂ) → ℂ)
    (hg : ∀ v, MeromorphicAt (fun z => g (placeFamily N v z)) 0)
    (hg0 : ∀ v, 0 ≤ meromorphicOrderAt (fun z => g (placeFamily N v z)) 0) :
    ∃ C : ℂ, ∀ v, (fun z => g (placeFamily N v z)) =ᶠ[𝓝[≠] 0] fun _ => C := by
  letI := placeTopology N
  letI := placeChartedSpace N
  letI := place_isManifold N
  letI := place_compactSpace N
  letI := place_connectedSpace N
  have hm : ∀ v, MeromorphicAt (MeromorphicCompact.rd g v)
      (MeromorphicCompact.ctr v) := by
    simpa only [MeromorphicCompact.rd, MeromorphicCompact.φ,
      MeromorphicCompact.ctr, extPlaceChart_symm_apply, extPlaceChart_self] using hg
  have ho : ∀ v, 0 ≤ meromorphicOrderAt (MeromorphicCompact.rd g v)
      (MeromorphicCompact.ctr v) := by
    simpa only [MeromorphicCompact.rd, MeromorphicCompact.φ,
      MeromorphicCompact.ctr, extPlaceChart_symm_apply, extPlaceChart_self] using hg0
  simpa only [MeromorphicCompact.rd, MeromorphicCompact.φ,
    MeromorphicCompact.ctr, extPlaceChart_symm_apply, extPlaceChart_self] using
      MeromorphicCompact.exists_const_germs_of_nonneg_order g hm ho

end
end Dubon2026.SourceFunctionField.OriginalChart
