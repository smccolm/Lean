import Dubon2026.SourceOriginalExteriorArcPresentations

/-! DUB-17/18 -> original Abel-Jacobi -> oriented actual cell pairing.
Use the already proved planar orientation bits on the full side identified
by an actual arc presentation. Arc-image injectivity makes the choice
independent of the presentation, and partners have opposite orientations.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

open scoped Classical in
/-- The proved planar orientation transported to an actual original-cell arc. -/
def orientArc (a : A.Arc) : Bool :=
  if h : ∃ (p : ℤ × ℤ) (k : Fin (A.G.region p).N) (m c : ℝ), A.SquareArcPresentation a p k m c then
    ArcReversal.sqbit A.planarData h.choose h.choose_spec.choose
  else if h' : ∃ (k : Fin A.W.R.N) (m c : ℝ), A.ExteriorArcPresentation a k m c then
    ArcReversal.perbit A.planarData h'.choose
  else false

theorem square_bit_eq_of_presentation {a : A.Arc} {p p' : ℤ × ℤ}
    {k : Fin (A.G.region p).N} {k' : Fin (A.G.region p').N} {m c m' c' : ℝ}
    (h : A.SquareArcPresentation a p k m c) (h' : A.SquareArcPresentation a p' k' m' c') :
    ArcReversal.sqbit A.planarData p k = ArcReversal.sqbit A.planarData p' k' := by
  have hp : p = p' := Option.some.inj (h.region.symm.trans h'.region)
  subst p'
  have hk : k = k' := GridWindow.arcSet_injective _ (h.lies.eq h'.lies)
  subst k'
  rfl

theorem exterior_index_eq_of_presentation {a : A.Arc} {k k' : Fin A.W.R.N} {m c m' c' : ℝ}
    (h : A.ExteriorArcPresentation a k m c) (h' : A.ExteriorArcPresentation a k' m' c') : k = k' :=
  GridWindow.arcSet_injective _ (h.lies.eq h'.lies)

theorem orientArc_of_square {a : A.Arc} {p : ℤ × ℤ} {k : Fin (A.G.region p).N} {m c : ℝ}
    (h : A.SquareArcPresentation a p k m c) : A.orientArc a = ArcReversal.sqbit A.planarData p k := by
  have hex : ∃ (p : ℤ × ℤ) (k : Fin (A.G.region p).N) (m c : ℝ), A.SquareArcPresentation a p k m c :=
    ⟨p, k, m, c, h⟩
  rw [orientArc, dif_pos hex]
  exact A.square_bit_eq_of_presentation hex.choose_spec.choose_spec.choose_spec.choose_spec h

theorem orientArc_of_exterior {a : A.Arc} {k : Fin A.W.R.N} {m c : ℝ}
    (h : A.ExteriorArcPresentation a k m c) : A.orientArc a = ArcReversal.perbit A.planarData k := by
  have hnot : ¬ ∃ (p : ℤ × ℤ) (k : Fin (A.G.region p).N) (m c : ℝ), A.SquareArcPresentation a p k m c := by
    rintro ⟨p, _, _, _, h'⟩
    exact Option.some_ne_none p (h'.region.symm.trans h.region)
  have hex : ∃ (k : Fin A.W.R.N) (m c : ℝ), A.ExteriorArcPresentation a k m c := ⟨k, m, c, h⟩
  rw [orientArc, dif_neg hnot, dif_pos hex,
    A.exterior_index_eq_of_presentation hex.choose_spec.choose_spec.choose_spec h]

theorem orientArc_partner (a b : A.Arc) (hreg : A.regionOf b.1 ≠ A.regionOf a.1)
    (hplaces : A.arcPlaces b = A.arcPlaces a) : A.orientArc b = !A.orientArc a := by
  have hZ {Z Z' : Set ℂ} (h : LiesOver (A.arcPlaces a) Z) (h' : LiesOver (A.arcPlaces b) Z') : Z = Z' :=
    h.eq (hplaces ▸ h')
  rcases A.exists_arc_presentation a with ⟨p, k, m, c, h⟩ | ⟨k, m, c, h⟩ <;>
    rcases A.exists_arc_presentation b with ⟨p', k', m', c', h'⟩ | ⟨k', m', c', h'⟩
  · have hp : p ≠ p' := by
      rintro rfl
      exact hreg (h'.region.trans h.region.symm)
    rw [A.orientArc_of_square h, A.orientArc_of_square h']
    exact ArcReversal.bit_sq_sq A.planarData p p' hp k k' (hZ h.lies h'.lies)
  · rw [A.orientArc_of_square h, A.orientArc_of_exterior h']
    exact ArcReversal.bit_sq_per A.planarData p k k'
      (A.regionOf_mem_window a.1 h.region) (hZ h.lies h'.lies)
  · rw [A.orientArc_of_exterior h, A.orientArc_of_square h']
    have hb := ArcReversal.bit_sq_per A.planarData p' k' k
      (A.regionOf_mem_window b.1 h'.region) (hZ h.lies h'.lies).symm
    rw [hb, Bool.not_not]
  · exact False.elim (hreg (h'.region.trans h.region.symm))

theorem orientArc_pairArc (a : A.Arc) : A.orientArc (A.pairArc a) = !A.orientArc a :=
  A.orientArc_partner a (A.pairArc a) (A.pairArc_region_ne a) (A.pairArc_places a)

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
