import Dubon2026.SourceCellWindowBaseArcs

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

/-- One bottom perimeter segment. -/
def botSeg (j : ℤ) : Set ℂ :=
  {z : ℂ | z.im = D.Y₀ ∧ z.re ∈ Set.Icc (D.o + j * D.hm) (D.o + (j + 1) * D.hm)}

/-- One top perimeter segment. -/
def topSeg (j : ℤ) : Set ℂ :=
  {z : ℂ | z.im = D.Y₁ ∧ z.re ∈ Set.Icc (D.o + j * D.hm) (D.o + (j + 1) * D.hm)}

/-- One upper part of a left perimeter side. -/
def leftUpSeg (k₀ : ℤ) : Set ℂ :=
  {z : ℂ | z.re = D.X₀ ∧ z.im ∈ Set.Icc (D.cy (D.jlo, k₀)) (D.o + (k₀ + 1) * D.hm)}

/-- One lower part of a left perimeter side. -/
def leftLowSeg (k₀ : ℤ) : Set ℂ :=
  {z : ℂ | z.re = D.X₀ ∧ z.im ∈ Set.Icc (D.o + k₀ * D.hm) (D.cy (D.jlo, k₀))}

/-- One lower part of a right perimeter side. -/
def rightLowSeg (k₀ : ℤ) : Set ℂ :=
  {z : ℂ | z.re = D.X₁ ∧ z.im ∈ Set.Icc (D.o + k₀ * D.hm) (D.cy (D.jhi, k₀))}

/-- One upper part of a right perimeter side. -/
def rightUpSeg (k₀ : ℤ) : Set ℂ :=
  {z : ℂ | z.re = D.X₁ ∧ z.im ∈ Set.Icc (D.cy (D.jhi, k₀)) (D.o + (k₀ + 1) * D.hm)}

/-- One of the exact grid perimeter segments. -/
def IsPerimSeg (A : Set ℂ) : Prop :=
  (∃ j ∈ Finset.Icc D.jlo D.jhi, A = D.botSeg j) ∨
  (∃ j ∈ Finset.Icc D.jlo D.jhi, A = D.topSeg j) ∨
  (∃ k₀ ∈ Finset.Icc D.klo D.khi, A = D.leftUpSeg k₀) ∨
  (∃ k₀ ∈ Finset.Icc D.klo D.khi, A = D.leftLowSeg k₀) ∨
  (∃ k₀ ∈ Finset.Icc D.klo D.khi, A = D.rightLowSeg k₀) ∨
  (∃ k₀ ∈ Finset.Icc D.klo D.khi, A = D.rightUpSeg k₀)

theorem card_six_union_le {α : Type} [DecidableEq α] (I₁ I₂ I₃ I₄ I₅ I₆ : Finset α) {a b : ℕ}
    (h1 : I₁.card ≤ a) (h2 : I₂.card ≤ a) (h3 : I₃.card ≤ b) (h4 : I₄.card ≤ b) (h5 : I₅.card ≤ b)
    (h6 : I₆.card ≤ b) : (I₁ ∪ I₂ ∪ I₃ ∪ I₄ ∪ I₅ ∪ I₆).card ≤ 2 * a + 4 * b := by
  have u12 := Finset.card_union_le I₁ I₂
  have u123 := Finset.card_union_le (I₁ ∪ I₂) I₃
  have u1234 := Finset.card_union_le (I₁ ∪ I₂ ∪ I₃) I₄
  have u12345 := Finset.card_union_le (I₁ ∪ I₂ ∪ I₃ ∪ I₄) I₅
  have uall := Finset.card_union_le (I₁ ∪ I₂ ∪ I₃ ∪ I₄ ∪ I₅) I₆
  omega

theorem exists_finset_perimSegs : ∃ S : Finset (Set ℂ),
    S.card ≤ 2 * D.J + 4 * D.K ∧ ∀ A : Set ℂ, D.IsPerimSeg A → A ∈ S := by
  classical
  refine ⟨(Finset.Icc D.jlo D.jhi).image D.botSeg ∪ (Finset.Icc D.jlo D.jhi).image D.topSeg ∪
    (Finset.Icc D.klo D.khi).image D.leftUpSeg ∪ (Finset.Icc D.klo D.khi).image D.leftLowSeg ∪
    (Finset.Icc D.klo D.khi).image D.rightLowSeg ∪ (Finset.Icc D.klo D.khi).image D.rightUpSeg,
    ?_, ?_⟩
  · refine card_six_union_le _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Finset.card_image_le.trans D.card_Icc_cols'.le
    · exact Finset.card_image_le.trans D.card_Icc_cols'.le
    · exact Finset.card_image_le.trans D.card_Icc_rows'.le
    · exact Finset.card_image_le.trans D.card_Icc_rows'.le
    · exact Finset.card_image_le.trans D.card_Icc_rows'.le
    · exact Finset.card_image_le.trans D.card_Icc_rows'.le
  · intro A hA
    rcases hA with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ |
        ⟨m, hm, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem D.botSeg hj)))))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem D.topSeg hj)))))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem D.leftUpSeg hm))))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem D.leftLowSeg hm)))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem D.rightLowSeg hm))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem D.rightUpSeg hm)


end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData
