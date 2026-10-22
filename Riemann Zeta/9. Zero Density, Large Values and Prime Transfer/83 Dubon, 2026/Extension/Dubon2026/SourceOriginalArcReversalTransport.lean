import Dubon2026.SourceCellAffineArcTransports

/-! DUB-17/18 -> original Abel-Jacobi -> C1 reversal on original places.
Transport a proved planar boundary identity through the affine coordinates.
Injectivity of actual j on the paired arc identifies the original places;
native ContDiffOn composition supplies differentiability of the transport.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

/-- The full orientation-reversing C1 parameter identity for actual original-cell arcs. -/
def ArcReversalClause (a b : A.Arc) (ψ : ℝ → ℝ) : Prop :=
  StrictAntiOn ψ ((A.cell b.1).R.arcIcc b.2) ∧
  ContDiffOn ℝ 1 ψ ((A.cell b.1).R.arcIcc b.2) ∧
  ψ ((A.cell b.1).R.φs b.2.castSucc) = (A.cell a.1).R.φs a.2.succ ∧
  ψ ((A.cell b.1).R.φs b.2.succ) = (A.cell a.1).R.φs a.2.castSucc ∧
  ∀ t ∈ (A.cell b.1).R.arcIcc b.2, (A.cell b.1).bdry t = (A.cell a.1).bdry (ψ t)

theorem reversal_of_transport (a b : A.Arc) (hplaces : A.arcPlaces b = A.arcPlaces a)
    {R R' : RadialRegion} {m c m' c' : ℝ} (hm : m ≠ 0)
    (hread : ∀ t ∈ (A.cell a.1).R.arcIcc a.2,
      originalPlaceEval N ℂ ((A.cell a.1).bdry t) (jOver N ℂ) = R.loop (m * t + c))
    {I : Set ℝ} (hinv : MapsTo (fun u : ℝ => (u - c) / m) I ((A.cell a.1).R.arcIcc a.2))
    (hread' : ∀ t ∈ (A.cell b.1).R.arcIcc b.2,
      originalPlaceEval N ℂ ((A.cell b.1).bdry t) (jOver N ℂ) = R'.loop (m' * t + c'))
    {I' : Set ℝ} (hmaps' : MapsTo (fun t : ℝ => m' * t + c') ((A.cell b.1).R.arcIcc b.2) I')
    {ψ₀ : ℝ → ℝ} (hψmaps : MapsTo ψ₀ I' I) (hψC : ContDiffOn ℝ 1 ψ₀ I')
    (hloop : ∀ u ∈ I', R'.loop u = R.loop (ψ₀ u))
    (hanti : StrictAntiOn (fun t => (ψ₀ (m' * t + c') - c) / m) ((A.cell b.1).R.arcIcc b.2))
    (hstart : (ψ₀ (m' * (A.cell b.1).R.φs b.2.castSucc + c') - c) / m = (A.cell a.1).R.φs a.2.succ)
    (hstop : (ψ₀ (m' * (A.cell b.1).R.φs b.2.succ + c') - c) / m = (A.cell a.1).R.φs a.2.castSucc) :
    A.ArcReversalClause a b (fun t => (ψ₀ (m' * t + c') - c) / m) := by
  refine ⟨hanti, ?_, hstart, hstop, ?_⟩
  · exact ((hψC.comp ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffOn hmaps').sub contDiffOn_const).div_const m
  · intro t ht
    have hu := hmaps' ht
    have hs := hinv (hψmaps hu)
    apply (A.arc_side a).2
    · rw [← hplaces]
      exact (A.cell b.1).bdry_mem_arc ht
    · exact (A.cell a.1).bdry_mem_arc hs
    · change originalPlaceEval N ℂ ((A.cell b.1).bdry t) (jOver N ℂ) =
        originalPlaceEval N ℂ ((A.cell a.1).bdry ((ψ₀ (m' * t + c') - c) / m)) (jOver N ℂ)
      rw [hread' t ht, hloop _ hu, hread _ hs, ArcAffine.affine_apply_inv hm]

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
