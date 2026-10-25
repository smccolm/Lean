import Dubon2026.SourceMeromorphicEffectivePoleBound
import Dubon2026.SourceOriginalWeilCoverMeromorphicDimension

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

theorem exists_cover_effective_meromorphic_pole_bound
    (g : Place ℂ (EE) → ℂ)
    (hg : ∀ v, MeromorphicAt (fun z => g (placeFamily N n f A hf hfA v z)) 0) :
    ∃ E : Divisor ℂ (EE), (∀ v, 0 ≤ E v) ∧
      ∀ v, ((-E v : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun z => g (placeFamily N n f A hf hfA v z)) 0 := by
  letI := placeTopology N n f A hf hfA
  letI := placeChartedSpace N n f A hf hfA
  letI := place_isManifold N n f A hf hfA
  letI := place_compactSpace N n f A hf hfA
  letI := place_connectedSpace N n f A hf hfA
  have hm : ∀ v, MeromorphicAt (MeromorphicCompact.rd g v)
      (MeromorphicCompact.ctr v) := by
    simpa only [MeromorphicCompact.rd, MeromorphicCompact.φ,
      MeromorphicCompact.ctr, extPlaceChart_symm_apply, extPlaceChart_self] using hg
  simpa only [MeromorphicCompact.rd, MeromorphicCompact.φ,
    MeromorphicCompact.ctr, extPlaceChart_symm_apply, extPlaceChart_self] using
      MeromorphicCompact.exists_effective_pole_bound g hm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
