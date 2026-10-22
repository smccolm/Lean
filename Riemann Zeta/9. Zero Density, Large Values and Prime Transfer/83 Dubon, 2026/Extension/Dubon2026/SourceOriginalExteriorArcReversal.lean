import Dubon2026.SourceOriginalSquareArcReversal

/-! DUB-17/18 -> original Abel-Jacobi -> actual C1 arc pairing.
Lift the two proved square/perimeter transports. The pole presentation has
negative slope, so their planar increasing maps become decreasing maps of
the original-cell arc parameters, with exact swapped endpoints.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem exists_square_exterior_reversal (a b : A.Arc) (hplaces : A.arcPlaces b = A.arcPlaces a)
    {p : ℤ × ℤ} {k : Fin (A.G.region p).N} {k' : Fin A.W.R.N} {m c m' c' : ℝ}
    (h : A.SquareArcPresentation a p k m c) (h' : A.ExteriorArcPresentation b k' m' c')
    (hbit : ArcReversal.sqbit A.planarData p k = true) :
    ∃ ψ : ℝ → ℝ, A.ArcReversalClause a b ψ := by
  have hZ : (A.G.region p).arcSet k = A.W.R.arcSet k' := h.lies.eq (hplaces ▸ h'.lies)
  obtain ⟨ψ₀, hψmono, hψC, hψ0, hψ1, hloop⟩ :=
    ArcReversal.rev_per_to_sq A.planarData p k k' (A.regionOf_mem_window a.1 h.region) hZ hbit
  change StrictMonoOn ψ₀ (A.W.R.arcIcc k') at hψmono
  change ψ₀ (A.W.R.φs k'.castSucc) = (A.G.region p).φs k.castSucc at hψ0
  change ψ₀ (A.W.R.φs k'.succ) = (A.G.region p).φs k.succ at hψ1
  have hψmaps : MapsTo ψ₀ (A.W.R.arcIcc k') ((A.G.region p).arcIcc k) := by
    simpa only [hψ0, hψ1] using hψmono.monotoneOn.mapsTo_Icc
  refine ⟨_, A.reversal_of_transport a b hplaces h.positive.ne' h.read h.inv_maps
    h'.read h'.maps hψmaps hψC hloop ?_ ?_ ?_⟩
  · have h1 := hψmono.comp_strictAntiOn (ArcAffine.strictAntiOn_affine_neg h'.negative _) h'.maps
    exact ((ArcAffine.strictMono_affine_inv (c := c) h.positive).strictMonoOn _).comp_strictAntiOn
      h1 (fun t ht => hψmaps (h'.maps ht))
  · rw [h'.start, hψ1, ← h.stop, ArcAffine.affine_inv_apply h.positive.ne']
  · rw [h'.stop, hψ0, ← h.start, ArcAffine.affine_inv_apply h.positive.ne']

theorem exists_exterior_square_reversal (a b : A.Arc) (hplaces : A.arcPlaces b = A.arcPlaces a)
    {k : Fin A.W.R.N} {p' : ℤ × ℤ} {k' : Fin (A.G.region p').N} {m c m' c' : ℝ}
    (h : A.ExteriorArcPresentation a k m c) (h' : A.SquareArcPresentation b p' k' m' c')
    (hbit : ArcReversal.perbit A.planarData k = true) :
    ∃ ψ : ℝ → ℝ, A.ArcReversalClause a b ψ := by
  have hZ : (A.G.region p').arcSet k' = A.W.R.arcSet k := (h.lies.eq (hplaces ▸ h'.lies)).symm
  have hp := A.regionOf_mem_window b.1 h'.region
  have hbit' : ArcReversal.sqbit A.planarData p' k' = false := by
    have hb := ArcReversal.bit_sq_per A.planarData p' k' k hp hZ
    rw [hbit] at hb
    cases hs : ArcReversal.sqbit A.planarData p' k'
    · rfl
    · simp only [hs, Bool.not_true] at hb
      cases hb
  obtain ⟨ψ₀, hψmono, hψC, hψ0, hψ1, hloop⟩ :=
    ArcReversal.rev_sq_to_per A.planarData p' k' k hp hZ hbit'
  change StrictMonoOn ψ₀ ((A.G.region p').arcIcc k') at hψmono
  change ψ₀ ((A.G.region p').φs k'.castSucc) = A.W.R.φs k.castSucc at hψ0
  change ψ₀ ((A.G.region p').φs k'.succ) = A.W.R.φs k.succ at hψ1
  have hψmaps : MapsTo ψ₀ ((A.G.region p').arcIcc k') (A.W.R.arcIcc k) := by
    simpa only [hψ0, hψ1] using hψmono.monotoneOn.mapsTo_Icc
  refine ⟨_, A.reversal_of_transport a b hplaces h.negative.ne h.read h.inv_maps
    h'.read h'.maps hψmaps hψC hloop ?_ ?_ ?_⟩
  · have h1 := hψmono.comp (ArcAffine.strictMonoOn_affine_pos h'.positive _) h'.maps
    exact ((ArcAffine.strictAnti_affine_inv (c := c) h.negative).strictAntiOn _).comp_strictMonoOn
      h1 (fun t ht => hψmaps (h'.maps ht))
  · rw [h'.start, hψ0, ← h.stop, ArcAffine.affine_inv_apply h.negative.ne]
  · rw [h'.stop, hψ1, ← h.start, ArcAffine.affine_inv_apply h.negative.ne]

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
