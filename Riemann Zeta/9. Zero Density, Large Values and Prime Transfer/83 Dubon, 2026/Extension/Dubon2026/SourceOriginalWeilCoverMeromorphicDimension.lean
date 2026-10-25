import Dubon2026.SourceMeromorphicDimensionBound
import Dubon2026.SourceOriginalWeilCoverConnected

/-! DUB-17/18 -> auxiliary point division -> Abel converse -> actual field comparison.
The proved compact connected complex Kummer cover instantiates the existing
native meromorphic-function theorem. Its actual extended charts retain the
constructed residue parameters. No compactness, connectedness or chart-order
hypothesis is supplied to this consumer; field identification remains next.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Topology
open scoped Manifold ContDiff
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C f : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hf : f ≠ 0)
variable (hfA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord f = (n : ℤ) * A v)
include A hf hfA

theorem exists_cover_meromorphic_relation
    (D : Place ℂ (EE) →₀ ℕ)
    {ι : Type*} [Fintype ι]
    (ψ : ι → Place ℂ (EE) → ℂ)
    (hψ : ∀ i v, MeromorphicAt (fun z => ψ i (placeFamily N n f A hf hfA v z)) 0)
    (hord : ∀ i v, ((-(D v : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z => ψ i (placeFamily N n f A hf hfA v z)) 0)
    (hcard : (D.sum fun _ n => n) + 1 < Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ ∀ v,
      (fun z => ∑ i, c i * ψ i (placeFamily N n f A hf hfA v z)) =ᶠ[𝓝[≠] 0] 0 := by
  letI := placeTopology N n f A hf hfA
  letI := placeChartedSpace N n f A hf hfA
  letI := place_isManifold N n f A hf hfA
  letI := place_compactSpace N n f A hf hfA
  letI := place_connectedSpace N n f A hf hfA
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

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
