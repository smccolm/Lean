import Dubon2026.SourceCellWindowPointPartition

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

theorem card_pB : (pB D).card = D.J + 1 := by
  unfold pB
  rw [Finset.card_image_of_injective _ ?_, D.card_Icc_cols]
  intro a b h
  have h' : D.o + a * D.hm = D.o + b * D.hm := congrArg Complex.re h
  exact D.intZ_eq_of_grid_eq h'

theorem card_pT : (pT D).card = D.J + 1 := by
  unfold pT
  rw [Finset.card_image_of_injective _ ?_, D.card_Icc_cols]
  intro a b h
  have h' : D.o + a * D.hm = D.o + b * D.hm := congrArg Complex.re h
  exact D.intZ_eq_of_grid_eq h'

theorem card_Icc_mid : (Finset.Icc (D.klo + 1) D.khi).card + 1 = D.K := by
  rw [Int.card_Icc]
  unfold K
  have := D.hk
  omega

theorem card_pL : (pL D).card + 1 = D.K := by
  unfold pL
  rw [Finset.card_image_of_injective _ ?_, card_Icc_mid D]
  intro a b h
  have h' : D.o + a * D.hm = D.o + b * D.hm := congrArg Complex.im h
  exact D.intZ_eq_of_grid_eq h'

theorem card_pR : (pR D).card + 1 = D.K := by
  unfold pR
  rw [Finset.card_image_of_injective _ ?_, card_Icc_mid D]
  intro a b h
  have h' : D.o + a * D.hm = D.o + b * D.hm := congrArg Complex.im h
  exact D.intZ_eq_of_grid_eq h'

theorem card_pCL : (pCL D).card = D.K := by
  unfold pCL
  rw [Finset.card_image_of_injective _ ?_, D.card_Icc_rows']
  intro a b h
  have h' : D.cy (D.jlo, a) = D.cy (D.jlo, b) := congrArg Complex.im h
  exact D.cy_injective_row _ h'

theorem card_pCR : (pCR D).card = D.K := by
  unfold pCR
  rw [Finset.card_image_of_injective _ ?_, D.card_Icc_rows']
  intro a b h
  have h' : D.cy (D.jhi, a) = D.cy (D.jhi, b) := congrArg Complex.im h
  exact D.cy_injective_row _ h'

theorem disj_pB_pT : Disjoint (pB D) (pT D) := by
  rw [Finset.disjoint_left]
  intro z hzB hzT
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hzB
  obtain ⟨j', -, h⟩ := Finset.mem_image.mp hzT
  have h' : D.Y₁ = D.Y₀ := congrArg Complex.im h
  exact absurd h' D.Y₀_lt_Y₁.ne'

theorem disj_pL_pCL : Disjoint (pL D) (pCL D) := by
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz1
  obtain ⟨k', -, h⟩ := Finset.mem_image.mp hz2
  have h' : D.cy (D.jlo, k') = D.o + k * D.hm := congrArg Complex.im h
  exact D.cy_ne_grid _ _ _ h'

theorem disj_pR_pCR : Disjoint (pR D) (pCR D) := by
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz1
  obtain ⟨k', -, h⟩ := Finset.mem_image.mp hz2
  have h' : D.cy (D.jhi, k') = D.o + k * D.hm := congrArg Complex.im h
  exact D.cy_ne_grid _ _ _ h'

theorem disj_pBT_pLCL : Disjoint (pB D ∪ pT D) (pL D ∪ pCL D) := by
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  have h1 := im_of_mem_pBT D hz1
  obtain ⟨-, h2lo, h2hi⟩ := of_mem_pL_pCL D hz2
  rcases h1 with h1 | h1 <;> linarith

theorem disj_left_right : Disjoint (pB D ∪ pT D ∪ (pL D ∪ pCL D)) (pR D ∪ pCR D) := by
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  obtain ⟨h2re, h2lo, h2hi⟩ := of_mem_pR_pCR D hz2
  rcases Finset.mem_union.mp hz1 with hz1 | hz1
  · rcases im_of_mem_pBT D hz1 with h1 | h1 <;> linarith
  · have h1 := (of_mem_pL_pCL D hz1).1
    have hX := D.X₀_lt_X₁
    linarith

theorem perimPts_card : D.perimPts.card = 2 * D.J + 4 * D.K := by
  rw [perimPts_eq D, Finset.card_union_of_disjoint (disj_left_right D),
    Finset.card_union_of_disjoint (disj_pBT_pLCL D), Finset.card_union_of_disjoint (disj_pB_pT D),
    Finset.card_union_of_disjoint (disj_pL_pCL D), Finset.card_union_of_disjoint (disj_pR_pCR D),
    card_pB D, card_pT D, card_pCL D, card_pCR D]
  have h1 := card_pL D
  have h2 := card_pR D
  omega

theorem right_zero_mem_perimPts : (⟨D.X₁, 0⟩ : ℂ) ∈ D.perimPts := by
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, D.o + k * D.hm ≤ 0 ∧ 0 < D.o + (k + 1) * D.hm := by
    refine ⟨⌊-D.o / D.hm⌋, ?_, ?_⟩
    · have h1 : ((⌊-D.o / D.hm⌋ : ℤ) : ℝ) ≤ -D.o / D.hm := Int.floor_le _
      rw [le_div_iff₀ D.hhm] at h1
      linarith
    · have h2 : -D.o / D.hm < ((⌊-D.o / D.hm⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
      rw [div_lt_iff₀ D.hhm] at h2
      linarith
  have hklo : D.klo ≤ k := by
    have h0 := D.hy₀
    have h1 : (D.klo : ℝ) < k + 1 := D.lt_of_grid_lt (by linarith)
    have h2 : D.klo < k + 1 := by exact_mod_cast h1
    omega
  have hkhi : k ≤ D.khi := by
    have h0 := D.hy₁
    have h1 : (k : ℝ) < D.khi + 1 := D.lt_of_grid_lt (by linarith)
    have h2 : k < D.khi + 1 := by exact_mod_cast h1
    omega
  rcases eq_or_lt_of_le hk1 with h0 | h0
  · have hmem : (⟨D.X₁, D.o + k * D.hm⟩ : ℂ) ∈ D.perimPts :=
      D.right_mem_perimPts (k := k) (Finset.mem_Icc.mpr ⟨hklo, by omega⟩)
    rw [h0] at hmem
    exact hmem
  · have hc : D.cy (D.jhi, k) = 0 := D.hcy0 k h0 hk2
    have hmem : (⟨D.X₁, D.cy (D.jhi, k)⟩ : ℂ) ∈ D.perimPts :=
      D.rightC_mem_perimPts (k := k) (Finset.mem_Icc.mpr ⟨hklo, hkhi⟩)
    rw [hc] at hmem
    exact hmem

theorem re_grid_of_mem {z : ℂ} (hz : z ∈ D.perimPts) :
    ∃ j ∈ Finset.Icc D.jlo (D.jhi + 1), z.re = D.o + j * D.hm := by
  have hj0 : D.jlo ∈ Finset.Icc D.jlo (D.jhi + 1) :=
    Finset.mem_Icc.mpr ⟨le_refl _, by have := D.hj; omega⟩
  have hj1 : D.jhi + 1 ∈ Finset.Icc D.jlo (D.jhi + 1) :=
    Finset.mem_Icc.mpr ⟨by have := D.hj; omega, le_refl _⟩
  have hX₁ : D.X₁ = D.o + ((D.jhi + 1 : ℤ) : ℝ) * D.hm := by
    unfold X₁
    simp only [Int.cast_add, Int.cast_one]
  rcases D.perimPts_cases hz with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩ |
      ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩
  · exact ⟨j, hj, rfl⟩
  · exact ⟨j, hj, rfl⟩
  · exact ⟨D.jlo, hj0, rfl⟩
  · exact ⟨D.jhi + 1, hj1, hX₁⟩
  · exact ⟨D.jlo, hj0, rfl⟩
  · exact ⟨D.jhi + 1, hj1, hX₁⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData
