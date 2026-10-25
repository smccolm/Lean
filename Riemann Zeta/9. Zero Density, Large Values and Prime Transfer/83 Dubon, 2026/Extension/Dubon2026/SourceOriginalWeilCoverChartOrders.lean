import Dubon2026.SourceOriginalWeilCoverManifold

/-! DUB-17/18 -> auxiliary cover Abel comparison -> actual manifold readings.
The constructed native extended charts have the actual cover residue values
and exact normalized orders. Inverse chart families are continuous with
open images, providing the local topological inputs to separation and compactness. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial Set
open scoped Manifold ContDiff Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])
variable (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hf : f ≠ 0)
variable (hfD : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord f = (n : ℤ) * D v)
include D hf hfD

theorem extPlaceChart_symm_apply (v : Place ℂ EE) (z : ℂ) :
    (letI := placeTopology N n f D hf hfD; letI := placeChartedSpace N n f D hf hfD;
      (extChartAt 𝓘(ℂ, ℂ) v).symm z) = placeFamily N n f D hf hfD v z := by
  letI := placeTopology N n f D hf hfD
  letI := placeChartedSpace N n f D hf hfD
  rw [extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
  rfl

theorem extPlaceChart_self (v : Place ℂ EE) :
    (letI := placeTopology N n f D hf hfD; letI := placeChartedSpace N n f D hf hfD;
      extChartAt 𝓘(ℂ, ℂ) v v) = 0 := by
  letI := placeTopology N n f D hf hfD
  letI := placeChartedSpace N n f D hf hfD
  rw [extChartAt_coe, modelWithCornersSelf_coe]
  exact placeChart_self N n f D hf hfD v

theorem cover_place_chart_order :
    letI := placeTopology N n f D hf hfD
    letI := placeChartedSpace N n f D hf hfD
    ∀ a : EE, a ≠ 0 → ∀ v : Place ℂ EE,
      MeromorphicAt (fun z : ℂ => ((extChartAt 𝓘(ℂ, ℂ) v).symm z).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) a)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt (fun z : ℂ => ((extChartAt 𝓘(ℂ, ℂ) v).symm z).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) a)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord a : WithTop ℤ) := by
  letI := placeTopology N n f D hf hfD
  letI := placeChartedSpace N n f D hf hfD
  intro a ha v
  have hfun : (fun z : ℂ => ((extChartAt 𝓘(ℂ, ℂ) v).symm z).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) a) =
      (fun z => (placeFamily N n f D hf hfD v z).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f (placeFamily N n f D hf hfD v z)) a) := by
    funext z
    simp only [extPlaceChart_symm_apply]
  rw [hfun, extPlaceChart_self]
  obtain ⟨hm, ho, _⟩ := (place_spec N n f D hf hfD v).2.2.1 0 (Metric.mem_ball_self (place_spec N n f D hf hfD v).1) a ha
  rw [(place_spec N n f D hf hfD v).2.1] at ho
  exact ⟨hm, ho⟩

theorem continuousOn_placeFamily (v : Place ℂ EE) :
    letI := placeTopology N n f D hf hfD
    ContinuousOn (placeFamily N n f D hf hfD v) (Metric.ball 0 (placeRadius N n f D hf hfD v)) := by
  letI := placeTopology N n f D hf hfD
  exact ((placeCore N n f D hf hfD).openPartialHomeomorph (placeChart N n f D hf hfD v) ⟨v, rfl⟩).continuousOn_symm

theorem isOpen_placeFamily_image (v : Place ℂ EE)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ Metric.ball 0 (placeRadius N n f D hf hfD v)) :
    IsOpen[placeTopology N n f D hf hfD] (placeFamily N n f D hf hfD v '' U) := by
  letI := placeTopology N n f D hf hfD
  exact ((placeCore N n f D hf hfD).openPartialHomeomorph (placeChart N n f D hf hfD v) ⟨v, rfl⟩).isOpen_image_symm_of_subset_target
    hU hsub

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
