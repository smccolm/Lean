import Dubon2026.SourceCellGridBreakpoints

/-! DUB-17/18 -> original Abel-Jacobi -> actual paired cell dissection.
Use the exact six-arc square and refined-window outputs to identify the two
regions sharing each side, its orientation and C1 reversal, and the finite
intersection chains at every boundary point. These are the planar inputs
to pairing the constructed original-curve cells and to their Euler count.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
The existing rectangle and outer-window constructors provide the geometric
data; no new radial-region existence hypothesis is introduced by consumers.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.GridVertices
noncomputable section
open scoped Real
open Set

variable {o hm : ℝ} {jlo jhi klo khi : ℤ} {ctr : ℤ × ℤ → ℂ}

/-- A point realized as a rectangle boundary breakpoint. -/
def IsBreakOf (o hm : ℝ) (jlo : ℤ) (ctr : ℤ × ℤ → ℂ) (j k : ℤ) (v : ℂ) : Prop :=
  ∀ (R : RadialRegion),
    PlanarRegions.RectClauses (o + j * hm) (o + (j + 1) * hm) (o + k * hm) (o + (k + 1) * hm) (ctr (j, k))
      (yL jlo ctr (j, k)) R →
    ∃ i : Fin (R.N + 1), R.loop (R.φs i) = v

theorem isBreakOf_corner_ll (j k : ℤ) :
    IsBreakOf o hm jlo ctr j k (⟨o + j * hm, o + k * hm⟩ : ℂ) := by
  intro R h
  have D := breakData_of_rectClauses h
  have hN := D.hN
  obtain ⟨i, hi⟩ : ∃ i : Fin (R.N + 1), i.val = 4 := ⟨⟨4, by omega⟩, rfl⟩
  exact ⟨i, D.b4 i hi⟩

theorem isBreakOf_corner_ul (j k : ℤ) :
    IsBreakOf o hm jlo ctr j k (⟨o + j * hm, o + ((k + 1 : ℤ) : ℝ) * hm⟩ : ℂ) := by
  intro R h
  have D := breakData_of_rectClauses h
  have hN := D.hN
  obtain ⟨i, hi⟩ : ∃ i : Fin (R.N + 1), i.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  exact ⟨i, (D.b2 i hi).trans (complex_mk_eq rfl (by push_cast; ring))⟩

theorem isBreakOf_corner_lr (j k : ℤ) :
    IsBreakOf o hm jlo ctr j k (⟨o + ((j + 1 : ℤ) : ℝ) * hm, o + k * hm⟩ : ℂ) := by
  intro R h
  have D := breakData_of_rectClauses h
  have hN := D.hN
  obtain ⟨i, hi⟩ : ∃ i : Fin (R.N + 1), i.val = 5 := ⟨⟨5, by omega⟩, rfl⟩
  exact ⟨i, (D.b5 i hi).trans (complex_mk_eq (by push_cast; ring) rfl)⟩

theorem isBreakOf_corner_ur (j k : ℤ) :
    IsBreakOf o hm jlo ctr j k (⟨o + ((j + 1 : ℤ) : ℝ) * hm, o + ((k + 1 : ℤ) : ℝ) * hm⟩ : ℂ) := by
  intro R h
  have D := breakData_of_rectClauses h
  have hN := D.hN
  obtain ⟨i, hi⟩ : ∃ i : Fin (R.N + 1), i.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  exact ⟨i, (D.b1 i hi).trans (complex_mk_eq (by push_cast; ring) (by push_cast; ring))⟩

theorem isBreakOf_right (j k : ℤ) :
    IsBreakOf o hm jlo ctr j k (⟨o + (j + 1) * hm, (ctr (j, k)).im⟩ : ℂ) := by
  intro R h
  have D := breakData_of_rectClauses h
  have hN := D.hN
  obtain ⟨i, hi⟩ : ∃ i : Fin (R.N + 1), i.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  exact ⟨i, D.b0 i hi⟩

theorem isBreakOf_left (k : ℤ) :
    IsBreakOf o hm jlo ctr jlo k (⟨o + jlo * hm, (ctr (jlo, k)).im⟩ : ℂ) := by
  intro R h
  have D := breakData_of_rectClauses h
  have hN := D.hN
  obtain ⟨i, hi⟩ : ∃ i : Fin (R.N + 1), i.val = 3 := ⟨⟨3, by omega⟩, rfl⟩
  exact ⟨i, (D.b3 i hi).trans (complex_mk_eq rfl (yL_left k))⟩

theorem mem_B₀_iff_break (hj : jlo ≤ jhi) (hk : klo ≤ khi) (v : ℂ) (hv : v ∈ B₀ o hm jlo jhi klo khi ctr) :
    ∃ j k : ℤ, jlo ≤ j ∧ j ≤ jhi ∧ klo ≤ k ∧ k ≤ khi ∧ IsBreakOf o hm jlo ctr j k v := by
  rcases mem_B₀.mp hv with hc | hr | hl
  · obtain ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩ := mem_corners.mp hc
    by_cases hjle : j ≤ jhi
    · by_cases hkle : k ≤ khi
      · exact ⟨j, k, hj₁, hjle, hk₁, hkle, isBreakOf_corner_ll j k⟩
      · obtain rfl : k = khi + 1 := by omega
        exact ⟨j, khi, hj₁, hjle, hk, le_rfl, isBreakOf_corner_ul j khi⟩
    · obtain rfl : j = jhi + 1 := by omega
      by_cases hkle : k ≤ khi
      · exact ⟨jhi, k, hj, le_rfl, hk₁, hkle, isBreakOf_corner_lr jhi k⟩
      · obtain rfl : k = khi + 1 := by omega
        exact ⟨jhi, khi, hj, le_rfl, hk, le_rfl, isBreakOf_corner_ur jhi khi⟩
  · obtain ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩ := mem_rights.mp hr
    exact ⟨j, k, hj₁, hj₂, hk₁, hk₂, isBreakOf_right j k⟩
  · obtain ⟨k, hk₁, hk₂, rfl⟩ := mem_lefts.mp hl
    exact ⟨jlo, k, le_rfl, hj, hk₁, hk₂, isBreakOf_left k⟩

theorem B₀_off_lines (v : ℂ) (hv : v ∈ B₀ o hm jlo jhi klo khi ctr) : ∃ j : ℤ, v.re - o = j * hm := by
  rcases mem_B₀.mp hv with hc | hr | hl
  · obtain ⟨j, k, -, -, -, -, rfl⟩ := mem_corners.mp hc
    refine ⟨j, ?_⟩
    show o + (j : ℝ) * hm - o = (j : ℝ) * hm
    ring
  · obtain ⟨j, k, -, -, -, -, rfl⟩ := mem_rights.mp hr
    refine ⟨j + 1, ?_⟩
    show o + ((j : ℝ) + 1) * hm - o = ((j + 1 : ℤ) : ℝ) * hm
    push_cast
    ring
  · obtain ⟨k, -, -, rfl⟩ := mem_lefts.mp hl
    refine ⟨jlo, ?_⟩
    show o + (jlo : ℝ) * hm - o = (jlo : ℝ) * hm
    ring


end
end Dubon2026.SourceFunctionField.CellGeometry.GridVertices
