import Dubon2026.SourceCellPowerArcCoverage

/-! DUB-17/18 -> original Abel-Jacobi -> actual branch/pole arc pairing.
Use the full proved power geometry and finite closed separation to identify
a connected inverse image as one complete lap arc. Its power map remains
injective and maps exactly onto the prescribed base arc.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.PowPullback
noncomputable section
open Set

theorem PowerGeometry.exponent_ne_zero {R R' : RadialRegion} {e : ℕ}
    (h : PowerGeometry R e R') : e ≠ 0 := by
  intro he
  have hN := h.2.1
  have hp := radialRegion_N_pos R'
  rw [he, zero_mul] at hN
  omega

theorem PowerGeometry.exists_arc_of_connected_image {R R' : RadialRegion} {e : ℕ}
    (h : PowerGeometry R e R') (k : Fin R.N) {L : Set ℂ}
    (hL : IsPreconnected L) (hne : L.Nonempty)
    (hover : ∀ u ∈ L, R.q + u ^ e ∈ R.arcSet k)
    (honto : R.arcSet k ⊆ (fun u : ℂ => R.q + u ^ e) '' L) :
    ∃ a : Fin R'.N, L = R'.arcSet a ∧
      InjOn (fun u : ℂ => R.q + u ^ e) (R'.arcSet a) ∧
      (fun u : ℂ => R.q + u ^ e) '' R'.arcSet a = R.arcSet k := by
  have he := h.exponent_ne_zero
  obtain ⟨_, _, _, _, _, lap, _, _, himg, hinj, hsep⟩ := h
  obtain ⟨U, _, hUd, hUsub⟩ := hsep k
  have hd : Pairwise fun i j => Disjoint (R'.arcSet (lap i k)) (R'.arcSet (lap j k)) :=
    fun i j hij => (hUd hij).mono (hUsub i) (hUsub j)
  have hc : L ⊆ ⋃ j, R'.arcSet (lap j k) := by
    intro u hu
    obtain ⟨j, hj⟩ := exists_lap_of_pow_mem he himg hsep (hover u hu)
    exact mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨j, hj⟩ := ArcSelection.exists_subset_of_finite_closed hL hne
    (fun j => (isCompact_arcSet R' (lap j k)).isClosed) hd hc
  refine ⟨lap j k, ?_, hinj j k, himg j k⟩
  apply ArcSelection.eq_of_image_subset_of_injOn hj _ (hinj j k)
  rw [himg j k]
  exact honto

end
end Dubon2026.SourceFunctionField.CellGeometry.PowPullback
