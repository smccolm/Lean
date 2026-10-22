import Dubon2026.SourceOriginalComplexChartedSpace

/-! DUB-17/18 -> original torsion cardinality -> complex Abel-Jacobi.
The native extended charts of the constructed original complex manifold
have the literal original residue evaluation and exact place orders.
Their inverse coordinate families are continuous and have open images,
as required for global separation and compactness arguments.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set
open scoped Manifold ContDiff Topology
variable (N : ℕ) [NeZero N]

theorem extPlaceChart_symm_apply (v : Place ℂ (modularFunctionFieldOver N ℂ)) (z : ℂ) :
    (letI := placeTopology N; letI := placeChartedSpace N;
      (extChartAt 𝓘(ℂ, ℂ) v).symm z) = placeFamily N v z := by
  letI := placeTopology N
  letI := placeChartedSpace N
  rw [extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
  rfl

theorem extPlaceChart_self (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    (letI := placeTopology N; letI := placeChartedSpace N;
      extChartAt 𝓘(ℂ, ℂ) v v) = 0 := by
  letI := placeTopology N
  letI := placeChartedSpace N
  rw [extChartAt_coe, modelWithCornersSelf_coe]
  exact placeChart_self N v

theorem original_place_chart_order :
    letI := placeTopology N
    letI := placeChartedSpace N
    ∀ f : modularFunctionFieldOver N ℂ, f ≠ 0 → ∀ v : Place ℂ (modularFunctionFieldOver N ℂ),
      MeromorphicAt (fun z : ℂ => originalPlaceEval N ℂ ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt (fun z : ℂ => originalPlaceEval N ℂ ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ) := by
  letI := placeTopology N
  letI := placeChartedSpace N
  intro f hf v
  have hfun : (fun z : ℂ => originalPlaceEval N ℂ ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) =
      (fun z => originalPlaceEval N ℂ (placeFamily N v z) f) := by
    funext z
    rw [extPlaceChart_symm_apply]
  rw [hfun, extPlaceChart_self]
  obtain ⟨hm, ho, _⟩ := (place_spec N v).2.2.1 0 (Metric.mem_ball_self (place_spec N v).1) f hf
  rw [(place_spec N v).2.1] at ho
  exact ⟨hm, ho⟩

theorem continuousOn_placeFamily (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    letI := placeTopology N
    ContinuousOn (placeFamily N v) (Metric.ball 0 (placeRadius N v)) := by
  letI := placeTopology N
  exact ((placeCore N).openPartialHomeomorph (placeChart N v) ⟨v, rfl⟩).continuousOn_symm

theorem isOpen_placeFamily_image (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ Metric.ball 0 (placeRadius N v)) :
    IsOpen[placeTopology N] (placeFamily N v '' U) := by
  letI := placeTopology N
  exact ((placeCore N).openPartialHomeomorph (placeChart N v) ⟨v, rfl⟩).isOpen_image_symm_of_subset_target
    hU hsub

end
end Dubon2026.SourceFunctionField.OriginalChart
