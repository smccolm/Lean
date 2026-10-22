import Dubon2026.SourceCellWindowData

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

/-- All grid vertices and side splits on the outer window. -/
def perimPts : Finset ℂ :=
  ((Finset.Icc D.jlo (D.jhi + 1)).image fun j : ℤ => (⟨D.o + j * D.hm, D.Y₀⟩ : ℂ)) ∪
  ((Finset.Icc D.jlo (D.jhi + 1)).image fun j : ℤ => (⟨D.o + j * D.hm, D.Y₁⟩ : ℂ)) ∪
  ((Finset.Icc D.klo (D.khi + 1)).image fun k : ℤ => (⟨D.X₀, D.o + k * D.hm⟩ : ℂ)) ∪
  ((Finset.Icc D.klo (D.khi + 1)).image fun k : ℤ => (⟨D.X₁, D.o + k * D.hm⟩ : ℂ)) ∪
  ((Finset.Icc D.klo D.khi).image fun k : ℤ => (⟨D.X₀, D.cy (D.jlo, k)⟩ : ℂ)) ∪
  ((Finset.Icc D.klo D.khi).image fun k : ℤ => (⟨D.X₁, D.cy (D.jhi, k)⟩ : ℂ))

theorem bottom_mem_perimPts {j : ℤ} (hj : j ∈ Finset.Icc D.jlo (D.jhi + 1)) :
    (⟨D.o + j * D.hm, D.Y₀⟩ : ℂ) ∈ D.perimPts := by
  unfold perimPts
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj)))))

theorem top_mem_perimPts {j : ℤ} (hj : j ∈ Finset.Icc D.jlo (D.jhi + 1)) :
    (⟨D.o + j * D.hm, D.Y₁⟩ : ℂ) ∈ D.perimPts := by
  unfold perimPts
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)))))

theorem left_mem_perimPts {k : ℤ} (hk : k ∈ Finset.Icc D.klo (D.khi + 1)) :
    (⟨D.X₀, D.o + k * D.hm⟩ : ℂ) ∈ D.perimPts := by
  unfold perimPts
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk))))

theorem right_mem_perimPts {k : ℤ} (hk : k ∈ Finset.Icc D.klo (D.khi + 1)) :
    (⟨D.X₁, D.o + k * D.hm⟩ : ℂ) ∈ D.perimPts := by
  unfold perimPts
  exact Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)))

theorem leftC_mem_perimPts {k : ℤ} (hk : k ∈ Finset.Icc D.klo D.khi) :
    (⟨D.X₀, D.cy (D.jlo, k)⟩ : ℂ) ∈ D.perimPts := by
  unfold perimPts
  exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk))

theorem rightC_mem_perimPts {k : ℤ} (hk : k ∈ Finset.Icc D.klo D.khi) :
    (⟨D.X₁, D.cy (D.jhi, k)⟩ : ℂ) ∈ D.perimPts := by
  unfold perimPts
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)

theorem perimPts_cases {z : ℂ} (hz : z ∈ D.perimPts) :
    (∃ j ∈ Finset.Icc D.jlo (D.jhi + 1), z = ⟨D.o + j * D.hm, D.Y₀⟩) ∨
    (∃ j ∈ Finset.Icc D.jlo (D.jhi + 1), z = ⟨D.o + j * D.hm, D.Y₁⟩) ∨
    (∃ k ∈ Finset.Icc D.klo (D.khi + 1), z = ⟨D.X₀, D.o + k * D.hm⟩) ∨
    (∃ k ∈ Finset.Icc D.klo (D.khi + 1), z = ⟨D.X₁, D.o + k * D.hm⟩) ∨
    (∃ k ∈ Finset.Icc D.klo D.khi, z = ⟨D.X₀, D.cy (D.jlo, k)⟩) ∨
    (∃ k ∈ Finset.Icc D.klo D.khi, z = ⟨D.X₁, D.cy (D.jhi, k)⟩) := by
  unfold perimPts at hz
  rcases Finset.mem_union.mp hz with hz | hz
  · rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · rcases Finset.mem_union.mp hz with hz | hz
        · rcases Finset.mem_union.mp hz with hz | hz
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
            exact Or.inl ⟨j, hj, rfl⟩
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
            exact Or.inr (Or.inl ⟨j, hj, rfl⟩)
        · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
          exact Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩))
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩))))
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, hk, rfl⟩))))

theorem perimPts_mem_closed {z : ℂ} (hz : z ∈ D.perimPts) :
    z.re ∈ Set.Icc D.X₀ D.X₁ ∧ z.im ∈ Set.Icc D.Y₀ D.Y₁ := by
  have hX := D.X₀_lt_X₁
  have hY := D.Y₀_lt_Y₁
  rcases D.perimPts_cases hz with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ |
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact ⟨D.gridx_mem hj, ⟨le_refl _, hY.le⟩⟩
  · exact ⟨D.gridx_mem hj, ⟨hY.le, le_refl _⟩⟩
  · exact ⟨⟨le_refl _, hX.le⟩, D.gridy_mem hk⟩
  · exact ⟨⟨hX.le, le_refl _⟩, D.gridy_mem hk⟩
  · exact ⟨⟨le_refl _, hX.le⟩, D.cy_mem_Icc D.jlo hk⟩
  · exact ⟨⟨hX.le, le_refl _⟩, D.cy_mem_Icc D.jhi hk⟩

theorem perimPts_not_mem_open {z : ℂ} (hz : z ∈ D.perimPts) :
    ¬ (z.re ∈ Set.Ioo D.X₀ D.X₁ ∧ z.im ∈ Set.Ioo D.Y₀ D.Y₁) := by
  rcases D.perimPts_cases hz with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ |
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact fun h => lt_irrefl _ h.2.1
  · exact fun h => lt_irrefl _ h.2.2
  · exact fun h => lt_irrefl _ h.1.1
  · exact fun h => lt_irrefl _ h.1.2
  · exact fun h => lt_irrefl _ h.1.1
  · exact fun h => lt_irrefl _ h.1.2


end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData
