import Dubon2026.SourceOriginalArcPresentationMaps

/-! DUB-17/18 -> original Abel-Jacobi -> actual C1 arc pairing.
Lift the proved opposite-square planar reversal through the exact positive
affine presentations. Native monotonicity composition proves the sign;
actual j-injectivity in reversal_of_transport proves original-place equality.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem exists_square_square_reversal (a b : A.Arc)
    (hreg : A.regionOf b.1 ≠ A.regionOf a.1) (hplaces : A.arcPlaces b = A.arcPlaces a)
    {p p' : ℤ × ℤ} {k : Fin (A.G.region p).N} {k' : Fin (A.G.region p').N} {m c m' c' : ℝ}
    (h : A.SquareArcPresentation a p k m c) (h' : A.SquareArcPresentation b p' k' m' c')
    (hbit : ArcReversal.sqbit A.planarData p k = true) :
    ∃ ψ : ℝ → ℝ, A.ArcReversalClause a b ψ := by
  have hpp : p ≠ p' := by
    rintro rfl
    exact hreg (h'.region.trans h.region.symm)
  have hZ : (A.G.region p).arcSet k = (A.G.region p').arcSet k' := h.lies.eq (hplaces ▸ h'.lies)
  obtain ⟨ψ₀, hψanti, hψC, hψ0, hψ1, hloop⟩ :=
    ArcReversal.rev_sq_sq A.planarData p p' hpp k k' hZ hbit
  change StrictAntiOn ψ₀ ((A.G.region p').arcIcc k') at hψanti
  change ψ₀ ((A.G.region p').φs k'.castSucc) = (A.G.region p).φs k.succ at hψ0
  change ψ₀ ((A.G.region p').φs k'.succ) = (A.G.region p).φs k.castSucc at hψ1
  have hψmaps : MapsTo ψ₀ ((A.G.region p').arcIcc k') ((A.G.region p).arcIcc k) := by
    simpa only [hψ0, hψ1] using hψanti.antitoneOn.mapsTo_Icc
  refine ⟨_, A.reversal_of_transport a b hplaces h.positive.ne' h.read h.inv_maps
    h'.read h'.maps hψmaps hψC hloop ?_ ?_ ?_⟩
  · have h1 := hψanti.comp_strictMonoOn (ArcAffine.strictMonoOn_affine_pos h'.positive _) h'.maps
    exact ((ArcAffine.strictMono_affine_inv (c := c) h.positive).strictMonoOn _).comp_strictAntiOn
      h1 (fun t ht => hψmaps (h'.maps ht))
  · rw [h'.start, hψ0, ← h.stop, ArcAffine.affine_inv_apply h.positive.ne']
  · rw [h'.stop, hψ1, ← h.start, ArcAffine.affine_inv_apply h.positive.ne']

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
