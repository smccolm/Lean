import Dubon2026.SourceOriginalArcReversalTransport

/-! DUB-17/18 -> original Abel-Jacobi -> C1 parameter reversal.
The proved endpoint identities and slope signs give the exact forward and
inverse interval maps used in the three planar-to-curve reversal cases.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} {A : OriginalGlobalCellCover N Marked}

theorem SquareArcPresentation.maps {a : A.Arc} {p : ℤ × ℤ} {k : Fin (A.G.region p).N} {m c : ℝ}
    (h : A.SquareArcPresentation a p k m c) :
    MapsTo (fun t : ℝ => m * t + c) ((A.cell a.1).R.arcIcc a.2) ((A.G.region p).arcIcc k) := by
  change MapsTo _ (Icc _ _) (Icc _ _)
  rw [← h.start, ← h.stop]
  exact ArcAffine.affine_mapsTo_pos h.positive

theorem SquareArcPresentation.inv_maps {a : A.Arc} {p : ℤ × ℤ} {k : Fin (A.G.region p).N} {m c : ℝ}
    (h : A.SquareArcPresentation a p k m c) :
    MapsTo (fun u : ℝ => (u - c) / m) ((A.G.region p).arcIcc k) ((A.cell a.1).R.arcIcc a.2) := by
  change MapsTo _ (Icc _ _) (Icc _ _)
  rw [← h.start, ← h.stop]
  exact ArcAffine.affine_inv_mapsTo_pos h.positive

theorem ExteriorArcPresentation.maps {a : A.Arc} {k : Fin A.W.R.N} {m c : ℝ}
    (h : A.ExteriorArcPresentation a k m c) :
    MapsTo (fun t : ℝ => m * t + c) ((A.cell a.1).R.arcIcc a.2) (A.W.R.arcIcc k) := by
  change MapsTo _ (Icc _ _) (Icc _ _)
  rw [← h.stop, ← h.start]
  exact ArcAffine.affine_mapsTo_neg h.negative

theorem ExteriorArcPresentation.inv_maps {a : A.Arc} {k : Fin A.W.R.N} {m c : ℝ}
    (h : A.ExteriorArcPresentation a k m c) :
    MapsTo (fun u : ℝ => (u - c) / m) (A.W.R.arcIcc k) ((A.cell a.1).R.arcIcc a.2) := by
  change MapsTo _ (Icc _ _) (Icc _ _)
  rw [← h.stop, ← h.start]
  exact ArcAffine.affine_inv_mapsTo_neg h.negative

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
