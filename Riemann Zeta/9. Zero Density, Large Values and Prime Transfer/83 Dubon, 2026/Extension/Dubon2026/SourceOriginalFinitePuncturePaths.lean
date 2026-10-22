import Dubon2026.SourceChartFinitePuncturePaths
import Dubon2026.SourceOriginalComplexConnected
import Dubon2026.SourceOriginalComplexHausdorff

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
global meromorphic exponential. There are actual original places outside any
finite set, and the complement is path connected in the actual chart topology.
These facts supply the base point and paths for exponentiating the third-kind
differential outside the prescribed divisor support.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set
open scoped Manifold ContDiff Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_place_outside_finite {S : Set (Place ℂ F)} (hS : S.Finite) :
    ∃ v, v ∉ S := by
  letI := placeTopology N
  letI := placeChartedSpace N
  letI := place_t2Space N
  let v := originalAnalyticPlace N UpperHalfPlane.I
  have h := OriginalExpTopology.eventually_pf_of_eventually_nhdsWithin v
    (OriginalExpTopology.eventually_nhdsWithin_compl_not_mem hS v)
  obtain ⟨z, hz⟩ := h.exists
  exact ⟨(extChartAt 𝓘(ℂ, ℂ) v).symm z, hz⟩

theorem original_isPathConnected_compl_finite {S : Set (Place ℂ F)} (hS : S.Finite) :
    letI := placeTopology N
    IsPathConnected Sᶜ := by
  letI := placeTopology N
  letI := placeChartedSpace N
  letI := place_t2Space N
  letI := place_connectedSpace N
  exact OriginalExpTopology.isPathConnected_compl_of_finite hS
    (exists_original_place_outside_finite N hS)

end
end Dubon2026.SourceFunctionField.OriginalChart
