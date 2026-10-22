import Dubon2026.SourceCellWindowPerimeterPoints

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite paired dissection.
Refine the outer window at exactly its grid perimeter vertices. The unchanged
radial region retains the pole-cell scale, while exact side intervals and
arc counts supply the boundary pairing and Euler calculation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing normalized argument, radial periodicity, loop injectivity and
six-arc rectangles are reused; no external Lean module is imported.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData
noncomputable section
open scoped Real
open Set

variable (D : WinData)

/-- Bottom grid vertices. -/
abbrev pB : Finset ℂ :=
  (Finset.Icc D.jlo (D.jhi + 1)).image fun j : ℤ => (⟨D.o + j * D.hm, D.Y₀⟩ : ℂ)
/-- Top grid vertices. -/
abbrev pT : Finset ℂ :=
  (Finset.Icc D.jlo (D.jhi + 1)).image fun j : ℤ => (⟨D.o + j * D.hm, D.Y₁⟩ : ℂ)

/-- Left interior grid vertices. -/
abbrev pL : Finset ℂ :=
  (Finset.Icc (D.klo + 1) D.khi).image fun k : ℤ => (⟨D.X₀, D.o + k * D.hm⟩ : ℂ)
/-- Right interior grid vertices. -/
abbrev pR : Finset ℂ :=
  (Finset.Icc (D.klo + 1) D.khi).image fun k : ℤ => (⟨D.X₁, D.o + k * D.hm⟩ : ℂ)
/-- Left prescribed side splits. -/
abbrev pCL : Finset ℂ :=
  (Finset.Icc D.klo D.khi).image fun k : ℤ => (⟨D.X₀, D.cy (D.jlo, k)⟩ : ℂ)
/-- Right prescribed side splits. -/
abbrev pCR : Finset ℂ :=
  (Finset.Icc D.klo D.khi).image fun k : ℤ => (⟨D.X₁, D.cy (D.jhi, k)⟩ : ℂ)

theorem perimPts_eq :
    D.perimPts = (pB D ∪ pT D ∪ (pL D ∪ pCL D)) ∪ (pR D ∪ pCR D) := by
  apply Finset.Subset.antisymm
  · intro z hz
    rcases D.perimPts_cases hz with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ |
        ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ hj)))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ hj)))
    ·
      rw [Finset.mem_Icc] at hk
      rcases eq_or_lt_of_le hk.1 with h0 | h0
      ·
        have hmem : (⟨D.o + D.jlo * D.hm, D.Y₀⟩ : ℂ) ∈ pB D :=
          Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨le_refl _, by have := D.hj; omega⟩)
        have heq : (⟨D.X₀, D.o + k * D.hm⟩ : ℂ) = ⟨D.o + D.jlo * D.hm, D.Y₀⟩ := by
          rw [← h0]
          rfl
        rw [heq]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
      rcases eq_or_lt_of_le hk.2 with h1 | h1
      ·
        have hmem : (⟨D.o + D.jlo * D.hm, D.Y₁⟩ : ℂ) ∈ pT D :=
          Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨le_refl _, by have := D.hj; omega⟩)
        have heq : (⟨D.X₀, D.o + k * D.hm⟩ : ℂ) = ⟨D.o + D.jlo * D.hm, D.Y₁⟩ := by
          rw [h1]
          unfold X₀ Y₁
          simp only [Int.cast_add, Int.cast_one]
        rw [heq]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hmem))
      · have hmem : (⟨D.X₀, D.o + k * D.hm⟩ : ℂ) ∈ pL D :=
          Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _ hmem))
    ·
      rw [Finset.mem_Icc] at hk
      rcases eq_or_lt_of_le hk.1 with h0 | h0
      · have hmem : (⟨D.o + (D.jhi + 1 : ℤ) * D.hm, D.Y₀⟩ : ℂ) ∈ pB D :=
          Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by have := D.hj; omega, le_refl _⟩)
        have heq : (⟨D.X₁, D.o + k * D.hm⟩ : ℂ) = ⟨D.o + (D.jhi + 1 : ℤ) * D.hm, D.Y₀⟩ := by
          rw [← h0]
          unfold X₁ Y₀
          simp only [Int.cast_add, Int.cast_one]
        rw [heq]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
      rcases eq_or_lt_of_le hk.2 with h1 | h1
      · have hmem : (⟨D.o + (D.jhi + 1 : ℤ) * D.hm, D.Y₁⟩ : ℂ) ∈ pT D :=
          Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by have := D.hj; omega, le_refl _⟩)
        have heq : (⟨D.X₁, D.o + k * D.hm⟩ : ℂ) = ⟨D.o + (D.jhi + 1 : ℤ) * D.hm, D.Y₁⟩ := by
          rw [h1]
          unfold X₁ Y₁
          simp only [Int.cast_add, Int.cast_one]
        rw [heq]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hmem))
      · have hmem : (⟨D.X₁, D.o + k * D.hm⟩ : ℂ) ∈ pR D :=
          Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        exact Finset.mem_union_right _ (Finset.mem_union_left _ hmem)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ hk)))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk))
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
          exact D.bottom_mem_perimPts hj
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
          exact D.top_mem_perimPts hj
      · rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
          rw [Finset.mem_Icc] at hk
          exact D.left_mem_perimPts (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
          exact D.leftC_mem_perimPts hk
    · rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_Icc] at hk
        exact D.right_mem_perimPts (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
        exact D.rightC_mem_perimPts hk

theorem im_of_mem_pBT {z : ℂ} (hz : z ∈ pB D ∪ pT D) : z.im = D.Y₀ ∨ z.im = D.Y₁ := by
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
    exact Or.inl rfl
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
    exact Or.inr rfl

theorem of_mem_pL_pCL {z : ℂ} (hz : z ∈ pL D ∪ pCL D) :
    z.re = D.X₀ ∧ z.im ∈ Set.Ioo D.Y₀ D.Y₁ := by
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_Icc] at hk
    refine ⟨rfl, ?_, ?_⟩
    · show D.Y₀ < D.o + k * D.hm
      unfold Y₀
      exact D.grid_lt (by exact_mod_cast (show D.klo < k by omega))
    · show D.o + k * D.hm < D.Y₁
      unfold Y₁
      exact D.grid_lt (by exact_mod_cast (show k < D.khi + 1 by omega))
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨rfl, D.cy_mem_Ioo D.jlo hk⟩

theorem of_mem_pR_pCR {z : ℂ} (hz : z ∈ pR D ∪ pCR D) :
    z.re = D.X₁ ∧ z.im ∈ Set.Ioo D.Y₀ D.Y₁ := by
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_Icc] at hk
    refine ⟨rfl, ?_, ?_⟩
    · show D.Y₀ < D.o + k * D.hm
      unfold Y₀
      exact D.grid_lt (by exact_mod_cast (show D.klo < k by omega))
    · show D.o + k * D.hm < D.Y₁
      unfold Y₁
      exact D.grid_lt (by exact_mod_cast (show k < D.khi + 1 by omega))
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨rfl, D.cy_mem_Ioo D.jhi hk⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData
