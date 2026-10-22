import Dubon2026.SourceOriginalPoleArcMatching

/-! DUB-17/18 -> original Abel-Jacobi -> actual exterior boundary matching.
Convert a j-image on an outer-window side to the exact inverse-j side using
the proved reciprocal arc equivalence. Boundary values are nonzero, so the
original valuation/evaluation criterion supplies inverse-j regularity.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalPoleRegionFamily
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {W : RadialRegion} (B : OriginalPoleRegionFamily N W)
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_unique_arc_over (hW : W.q = 0) (k : Fin W.N) {L : Set (Place ℂ F)}
    (hL : IsPreconnected L) (hne : L.Nonempty)
    (hover : ∀ P ∈ L, jOver N ℂ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ) ∈ W.arcSet k)
    (honto : W.arcSet k ⊆ (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' L) :
    ∃! a : Σ v, Fin (B.C v).R.N, L = (B.C a.1).arc a.2 := by
  obtain ⟨σ, _, himg⟩ := B.reciprocal.2.2.2.2.2.2
  have hside (z : ℂ) : z ∈ W.arcSet k ↔ z⁻¹ ∈ B.R.arcSet (σ k) := by
    constructor
    · intro hz
      obtain ⟨u, hu, huz⟩ := (himg k).symm ▸ hz
      rw [← huz, inv_inv]
      exact hu
    · intro hz
      rw [← himg k]
      exact ⟨z⁻¹, hz, inv_inv z⟩
  have hi (P : Place ℂ F) (hP : P ∈ L) : (jOver N ℂ)⁻¹ ∈ P.toValuationSubring := by
    have hz : originalPlaceEval N ℂ P (jOver N ℂ) ≠ 0 := by
      obtain ⟨t, _, ht⟩ := (hover P hP).2
      rw [← ht, ← hW]
      exact W.loop_ne_center t
    have hj : jOver N ℂ ≠ 0 := fun h => transcendental_jOver N ℂ (h ▸ isAlgebraic_zero)
    have ho : ¬ 0 < P.ord (jOver N ℂ) := fun h =>
      hz ((originalPlaceEval_eq_zero_iff_ord_pos N ℂ P (hover P hP).1 hj).mpr h)
    apply P.mem_of_ord_nonneg
    rw [Place.ord_inv]
    exact neg_nonneg.mpr (le_of_not_gt ho)
  apply B.exists_unique_inverse_arc_over hW (σ k) hL hne
  · intro P hP
    refine ⟨hi P hP, ?_⟩
    rw [originalPlaceEval_inv]
    exact (hside _).mp (hover P hP).2
  · intro u hu
    have hz : u⁻¹ ∈ W.arcSet k := (hside _).mpr (by simpa only [inv_inv] using hu)
    obtain ⟨P, hP, he⟩ := honto hz
    refine ⟨P, hP, ?_⟩
    change originalPlaceEval N ℂ P (jOver N ℂ) = u⁻¹ at he
    change originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ = u
    rw [originalPlaceEval_inv, he, inv_inv]

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalPoleRegionFamily
