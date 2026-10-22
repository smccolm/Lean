import Dubon2026.SourceOriginalNormalCoordinateShrink

/-! DUB-17/18 -> geometric cell dissection -> branch and pole neighborhoods.
Construct pairwise disjoint normal coordinates at any finite set of actual
zeros, retaining their exact power law and a common positive image scale.
The original curve's proved Hausdorff topology and native finite separation
replace the external topological separation infrastructure.
Adapted from NormalCharts.charts_of_finset in
S_AlgebraicCurve_exists_dissectionScaleData, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
open scoped Manifold
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_finite_original_normal_coordinates {g : F} (hg : g ≠ 0)
    (S : Finset (Place ℂ F))
    (hS : ∀ v ∈ S, g ∈ v.toValuationSubring ∧ originalPlaceEval N ℂ v g = 0) :
    ∃ (A : S → AnalyticCoord N) (r : S → ℝ) (m : ℝ), 0 < m ∧
      (∀ v : S, 0 < r v ∧ (v : Place ℂ F) ∈ (A v).ζ.source ∧ (A v).ζ v = 0 ∧
        (A v).ζ.target = Metric.ball 0 (r v) ∧
        (A v).ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) (v : Place ℂ F)).source ∧
        0 < ((v : Place ℂ F).ord g).toNat ∧
        ∀ P ∈ (A v).ζ.source, g ∈ P.toValuationSubring ∧
          originalPlaceEval N ℂ P g = ((A v).ζ P) ^ ((v : Place ℂ F).ord g).toNat) ∧
      (Pairwise fun v w => Disjoint (A v).ζ.source (A w).ζ.source) ∧
      ∀ v : S, m ≤ r v ^ ((v : Place ℂ F).ord g).toNat := by
  classical
  letI := OriginalChart.place_t2Space N
  have hnormal := fun v : S =>
    exists_original_normal_cell_coordinate (v : Place ℂ F) hg (hS v v.2).1 (hS v v.2).2
  choose A r hr hv hz ht hs he hform using hnormal
  obtain ⟨U, hU, hUd⟩ := S.finite_toSet.t2_separation
  have hsmall := fun v : S => (A v).exists_disk_restriction (hv v) (hz v)
    (hU (v : Place ℂ F)).2 (hU (v : Place ℂ F)).1 (hr v)
  choose B s hpos hle hmem hzero htarget hsub hUsub hagree hinv using hsmall
  let f : S → ℝ := fun v => s v ^ ((v : Place ℂ F).ord g).toNat
  let T := insert (1 : ℝ) (Finset.univ.image f)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  let m := T.min' hT
  have hm : 0 < m := by
    have hmin := T.min'_mem hT
    rcases Finset.mem_insert.mp hmin with h1 | h1
    · rw [show m = 1 from h1]
      exact one_pos
    · obtain ⟨v, _, hvm⟩ := Finset.mem_image.mp h1
      change f v = m at hvm
      rw [← hvm]
      exact pow_pos (hpos v) _
  refine ⟨B, s, m, hm, ?_, ?_, ?_⟩
  · intro v
    refine ⟨hpos v, hmem v, hzero v, htarget v, (hsub v).trans (hs v), he v, ?_⟩
    intro P hP
    rw [hagree v P]
    exact hform v P (hsub v hP)
  · intro v w hne
    have hd := hUd v.2 w.2 (fun hvw => hne (Subtype.ext hvw))
    exact Set.disjoint_of_subset (hUsub v) (hUsub w) hd
  · intro v
    exact T.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ v)))

end
end Dubon2026.SourceFunctionField.CellGeometry
