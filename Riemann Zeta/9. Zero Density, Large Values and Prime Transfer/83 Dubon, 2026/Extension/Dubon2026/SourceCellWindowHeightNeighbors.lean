import Dubon2026.SourceCellWindowPointCounts

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

/-- A window endpoint, grid height or prescribed split in a column. -/
def IsHt (j : ℤ) (h : ℝ) : Prop :=
  (∃ m ∈ Finset.Icc D.klo (D.khi + 1), h = D.o + m * D.hm) ∨
    (∃ m ∈ Finset.Icc D.klo D.khi, h = D.cy (j, m))

theorem isHt_Y₀ (j : ℤ) : D.IsHt j D.Y₀ :=
  Or.inl ⟨D.klo, Finset.mem_Icc.mpr ⟨le_refl _, by have := D.hk; omega⟩, rfl⟩

theorem isHt_Y₁ (j : ℤ) : D.IsHt j D.Y₁ := by
  refine Or.inl ⟨D.khi + 1, Finset.mem_Icc.mpr ⟨by have := D.hk; omega, le_refl _⟩, ?_⟩
  unfold Y₁
  simp only [Int.cast_add, Int.cast_one]

theorem isHt_left_of_mem {z : ℂ} (hz : z ∈ D.perimPts) (hre : z.re = D.X₀) : D.IsHt D.jlo z.im := by
  have hX := D.X₀_lt_X₁
  rcases D.perimPts_cases hz with ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, -, rfl⟩ |
      ⟨k, hk, rfl⟩ | ⟨k, -, rfl⟩
  · exact D.isHt_Y₀ _
  · exact D.isHt_Y₁ _
  · exact Or.inl ⟨k, hk, rfl⟩
  · exact absurd (hre : D.X₁ = D.X₀) hX.ne'
  · exact Or.inr ⟨k, hk, rfl⟩
  · exact absurd (hre : D.X₁ = D.X₀) hX.ne'

theorem isHt_right_of_mem {z : ℂ} (hz : z ∈ D.perimPts) (hre : z.re = D.X₁) :
    D.IsHt D.jhi z.im := by
  have hX := D.X₀_lt_X₁
  rcases D.perimPts_cases hz with ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩ | ⟨k, -, rfl⟩ | ⟨k, hk, rfl⟩ |
      ⟨k, -, rfl⟩ | ⟨k, hk, rfl⟩
  · exact D.isHt_Y₀ _
  · exact D.isHt_Y₁ _
  · exact absurd (hre : D.X₀ = D.X₁) hX.ne
  · exact Or.inl ⟨k, hk, rfl⟩
  · exact absurd (hre : D.X₀ = D.X₁) hX.ne
  · exact Or.inr ⟨k, hk, rfl⟩

theorem left_pt_mem_perimPts {h : ℝ} (hh : D.IsHt D.jlo h) : (⟨D.X₀, h⟩ : ℂ) ∈ D.perimPts := by
  rcases hh with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
  · exact D.left_mem_perimPts hm
  · exact D.leftC_mem_perimPts hm

theorem right_pt_mem_perimPts {h : ℝ} (hh : D.IsHt D.jhi h) : (⟨D.X₁, h⟩ : ℂ) ∈ D.perimPts := by
  rcases hh with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
  · exact D.right_mem_perimPts hm
  · exact D.rightC_mem_perimPts hm

theorem consec_abscissae {m m' : ℤ} (hm : m ∈ Finset.Icc D.jlo (D.jhi + 1))
    (hm' : m' ∈ Finset.Icc D.jlo (D.jhi + 1)) (hlt : D.o + m * D.hm < D.o + m' * D.hm)
    (hno : ∀ n ∈ Finset.Icc D.jlo (D.jhi + 1),
      ¬ (D.o + m * D.hm < D.o + n * D.hm ∧ D.o + n * D.hm < D.o + m' * D.hm)) :
    m' = m + 1 := by
  rw [Finset.mem_Icc] at hm hm'
  have h1 : m < m' := D.intZ_lt_of_grid_lt hlt
  by_contra hne
  have h2 : m + 1 < m' := by omega
  exact hno (m + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    ⟨D.grid_lt (by exact_mod_cast (show m < m + 1 by omega)), D.grid_lt (by exact_mod_cast h2)⟩

theorem consec_heights (j : ℤ) {lo hi : ℝ} (hlo : D.IsHt j lo) (hhi : D.IsHt j hi) (hlt : lo < hi)
    (hno : ∀ h : ℝ, D.IsHt j h → ¬ (lo < h ∧ h < hi)) :
    ∃ k₀ : ℤ, D.klo ≤ k₀ ∧ k₀ ≤ D.khi ∧
      ((lo = D.o + k₀ * D.hm ∧ hi = D.cy (j, k₀)) ∨
        (lo = D.cy (j, k₀) ∧ hi = D.o + (k₀ + 1) * D.hm)) := by
  rcases hlo with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ <;> rcases hhi with ⟨m', hm', rfl⟩ | ⟨m', hm', rfl⟩
  ·
    exfalso
    rw [Finset.mem_Icc] at hm hm'
    have hmm' : m < m' := D.intZ_lt_of_grid_lt hlt
    have h1 := D.cy_gt j m
    have h2 := D.cy_lt j m
    have h3 : D.o + (m + 1) * D.hm ≤ D.o + m' * D.hm :=
      D.grid_le (by exact_mod_cast (show m + 1 ≤ m' by omega))
    exact hno (D.cy (j, m)) (Or.inr ⟨m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩)
      ⟨h1, by linarith⟩
  ·
    rw [Finset.mem_Icc] at hm hm'
    have h1 := D.cy_lt j m'
    have h2 := D.cy_gt j m'
    have h3 : (m : ℝ) < m' + 1 := D.lt_of_grid_lt (by linarith)
    have h3' : m < m' + 1 := by exact_mod_cast h3
    rcases eq_or_lt_of_le (show m ≤ m' by omega) with heq | hmlt
    · refine ⟨m', by omega, hm'.2, Or.inl ⟨?_, rfl⟩⟩
      rw [heq]
    · exfalso
      have h4 : D.o + m * D.hm < D.o + m' * D.hm := D.grid_lt (by exact_mod_cast hmlt)
      exact hno (D.o + m' * D.hm) (Or.inl ⟨m', Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩)
        ⟨h4, h2⟩
  ·
    rw [Finset.mem_Icc] at hm hm'
    have h1 := D.cy_gt j m
    have h2 := D.cy_lt j m
    have h3 : m < m' := D.intZ_lt_of_grid_lt (by linarith)
    rcases eq_or_lt_of_le (show m + 1 ≤ m' by omega) with heq | hmlt
    · refine ⟨m, hm.1, hm.2, Or.inr ⟨rfl, ?_⟩⟩
      rw [← heq]
      simp only [Int.cast_add, Int.cast_one]
    · exfalso
      have h4 : D.o + (m + 1) * D.hm < D.o + m' * D.hm := D.grid_lt (by exact_mod_cast hmlt)
      refine hno (D.o + (m + 1 : ℤ) * D.hm)
        (Or.inl ⟨m + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩) ⟨?_, ?_⟩
      · push_cast
        linarith
      · push_cast
        linarith
  ·
    exfalso
    rw [Finset.mem_Icc] at hm hm'
    have h1 := D.cy_lt j m
    have h2 := D.cy_gt j m'
    have hmm' : m < m' := by
      by_contra hcon
      rcases eq_or_lt_of_le (show m' ≤ m by omega) with h6 | h6
      · rw [h6] at hlt
        exact lt_irrefl _ hlt
      · have h7 := D.cy_lt j m'
        have h8 := D.cy_gt j m
        have h9 : D.o + (m' + 1) * D.hm ≤ D.o + m * D.hm :=
          D.grid_le (by exact_mod_cast (show m' + 1 ≤ m by omega))
        linarith
    have h3 : D.o + (m + 1) * D.hm ≤ D.o + m' * D.hm :=
      D.grid_le (by exact_mod_cast (show m + 1 ≤ m' by omega))
    refine hno (D.o + (m + 1 : ℤ) * D.hm)
      (Or.inl ⟨m + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩) ⟨?_, ?_⟩
    · push_cast
      linarith
    · push_cast
      linarith


end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData
