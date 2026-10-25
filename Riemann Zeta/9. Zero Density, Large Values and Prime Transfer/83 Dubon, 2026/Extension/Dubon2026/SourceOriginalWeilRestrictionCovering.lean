import Dubon2026.SourceOriginalWeilRestrictionLocalHomeomorph
import Dubon2026.SourceOriginalWeilCoverCompact
import Mathlib.Topology.Covering.Basic

/-! DUB-17/18 -> cover raw reciprocity -> lift the original cell dissection.
The pinned Mathlib covering criterion consumes the constructed compact
Hausdorff cover and actual local homeomorphism. No covering-map premise is
supplied for the literal place restriction. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial Filter
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])
attribute [local instance] restrictionIntegral
variable (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hf : f ≠ 0)
variable (hfD : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord f = (n : ℤ) * D v)
include D hf hfD

theorem isCoveringMap_restriction :
    letI := placeTopology N n f D hf hfD
    letI := OriginalChart.placeTopology N
    IsCoveringMap (fun w : Place ℂ EE => w.restrict FF) := by
  letI := placeTopology N n f D hf hfD
  letI := OriginalChart.placeTopology N
  letI := place_compactSpace N n f D hf hfD
  letI := place_t2Space N n f D hf hfD
  letI := OriginalChart.place_t2Space N
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply IsCoveringMapOn.of_openPartialHomeomorph (continuous_restriction N n f D hf hfD)
  intro w _
  obtain ⟨e, he, hfe⟩ := isLocalHomeomorph_restriction N n f D hf hfD w
  exact ⟨e, he, hfe.symm⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
