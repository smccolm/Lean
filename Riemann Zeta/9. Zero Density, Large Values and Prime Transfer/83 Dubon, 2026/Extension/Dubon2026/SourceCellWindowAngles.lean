import Dubon2026.SourceCellWindowHeightNeighbors

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

/-- Normalized angles of every perimeter vertex. -/
def angles : Finset ℝ := D.perimPts.image ang

theorem angles_bdd : ∀ t ∈ D.angles, 0 ≤ t ∧ t ≤ 2 * π := by
  intro t ht
  unfold angles at ht
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp ht
  exact ⟨(ang_mem z).1, (ang_mem z).2.le⟩

theorem mem_angles_iff (t : ℝ) : t ∈ D.angles ↔ ∃ z ∈ D.perimPts, ang z = t := by
  unfold angles
  exact Finset.mem_image

theorem ang_mem_angles {z : ℂ} (hz : z ∈ D.perimPts) : ang z ∈ D.angles :=
  (D.mem_angles_iff _).mpr ⟨z, hz, rfl⟩

theorem corner_X₀Y₀_mem : (⟨D.X₀, D.Y₀⟩ : ℂ) ∈ D.perimPts :=
  D.bottom_mem_perimPts (j := D.jlo) (Finset.mem_Icc.mpr ⟨le_refl _, by have := D.hj; omega⟩)

theorem corner_X₀Y₁_mem : (⟨D.X₀, D.Y₁⟩ : ℂ) ∈ D.perimPts :=
  D.top_mem_perimPts (j := D.jlo) (Finset.mem_Icc.mpr ⟨le_refl _, by have := D.hj; omega⟩)

theorem corner_X₁Y₀_mem : (⟨D.X₁, D.Y₀⟩ : ℂ) ∈ D.perimPts :=
  D.right_mem_perimPts (k := D.klo) (Finset.mem_Icc.mpr ⟨le_refl _, by have := D.hk; omega⟩)

theorem corner_X₁Y₁_mem : (⟨D.X₁, D.Y₁⟩ : ℂ) ∈ D.perimPts := by
  have h := D.top_mem_perimPts (j := D.jhi + 1)
    (Finset.mem_Icc.mpr ⟨by have := D.hj; omega, le_refl _⟩)
  have e : (⟨D.o + ((D.jhi + 1 : ℤ) : ℝ) * D.hm, D.Y₁⟩ : ℂ) = ⟨D.X₁, D.Y₁⟩ := by
    unfold X₁
    simp only [Int.cast_add, Int.cast_one]
  rw [e] at h
  exact h

theorem split_X₀_mem : (⟨D.X₀, D.cy (D.jlo, D.klo)⟩ : ℂ) ∈ D.perimPts :=
  D.leftC_mem_perimPts (k := D.klo) (Finset.mem_Icc.mpr ⟨le_refl _, D.hk⟩)

theorem two_pi_not_mem_angles : (2 * π) ∉ D.angles := by
  intro h
  rw [D.mem_angles_iff] at h
  obtain ⟨z, -, hz⟩ := h
  have h2 := (ang_mem z).2
  rw [hz] at h2
  exact lt_irrefl _ h2

theorem horizontal_finish {y : ℝ}
    (hvert : ∀ n ∈ Finset.Icc D.jlo (D.jhi + 1), (⟨D.o + n * D.hm, y⟩ : ℂ) ∈ D.perimPts)
    {zl zr : ℂ} (hzl : zl ∈ D.perimPts) (hzr : zr ∈ D.perimPts) (hne : zl ≠ zr)
    (hyl : zl.im = y) (hyr : zr.im = y) (hdir : zl.re ≤ zr.re)
    (hno : ∀ z ∈ D.perimPts, z ∈ segment ℝ zl zr → z = zl ∨ z = zr) :
    ∃ j : ℤ, D.jlo ≤ j ∧ j ≤ D.jhi ∧
      segment ℝ zl zr =
        {z : ℂ | z.im = y ∧ z.re ∈ Set.Icc (D.o + j * D.hm) (D.o + (j + 1) * D.hm)} ∧
      zl = ⟨D.o + j * D.hm, y⟩ ∧ zr = ⟨D.o + (j + 1) * D.hm, y⟩ := by
  have him : zl.im = zr.im := hyl.trans hyr.symm
  have hseg := segment_horizontal him hdir
  have hlt : zl.re < zr.re := by
    rcases eq_or_lt_of_le hdir with h | h
    · exact absurd (Complex.ext h him) hne
    · exact h
  obtain ⟨m, hm, hml⟩ := D.re_grid_of_mem hzl
  obtain ⟨m', hm', hmr⟩ := D.re_grid_of_mem hzr
  have hlt' : D.o + m * D.hm < D.o + m' * D.hm := by
    rw [← hml, ← hmr]
    exact hlt
  have hcons : m' = m + 1 := by
    refine D.consec_abscissae hm hm' hlt' ?_
    intro n hn ⟨h1, h2⟩
    have hv : (⟨D.o + n * D.hm, y⟩ : ℂ) ∈ segment ℝ zl zr := by
      rw [hseg, Set.mem_setOf_eq]
      refine ⟨hyl.symm, ?_, ?_⟩
      · rw [hml]
        exact h1.le
      · rw [hmr]
        exact h2.le
    rcases hno _ (hvert n hn) hv with h | h
    · have h' : D.o + n * D.hm = zl.re := congrArg Complex.re h
      rw [hml] at h'
      linarith
    · have h' : D.o + n * D.hm = zr.re := congrArg Complex.re h
      rw [hmr] at h'
      linarith
  subst hcons
  rw [Finset.mem_Icc] at hm hm'
  have hmr' : zr.re = D.o + (m + 1) * D.hm := by
    rw [hmr]
    simp only [Int.cast_add, Int.cast_one]
  have e1 : zl = ⟨D.o + m * D.hm, y⟩ := Complex.ext hml hyl
  have e2 : zr = ⟨D.o + (m + 1) * D.hm, y⟩ := Complex.ext hmr' hyr
  refine ⟨m, hm.1, by omega, ?_, e1, e2⟩
  rw [hseg, hyl, hml, hmr']

theorem vertical_finish {x : ℝ} (j : ℤ)
    (hvert : ∀ h : ℝ, D.IsHt j h → (⟨x, h⟩ : ℂ) ∈ D.perimPts)
    {zlo zhi : ℂ} (hlo : D.IsHt j zlo.im) (hhi : D.IsHt j zhi.im) (hne : zlo ≠ zhi)
    (hxlo : zlo.re = x) (hxhi : zhi.re = x) (hdir : zlo.im ≤ zhi.im)
    (hno : ∀ z ∈ D.perimPts, z ∈ segment ℝ zlo zhi → z = zlo ∨ z = zhi) :
    ∃ k₀ : ℤ, D.klo ≤ k₀ ∧ k₀ ≤ D.khi ∧
      ((segment ℝ zlo zhi = {z : ℂ | z.re = x ∧ z.im ∈ Set.Icc (D.o + k₀ * D.hm) (D.cy (j, k₀))} ∧
          zlo = ⟨x, D.o + k₀ * D.hm⟩ ∧ zhi = ⟨x, D.cy (j, k₀)⟩) ∨
        (segment ℝ zlo zhi =
            {z : ℂ | z.re = x ∧ z.im ∈ Set.Icc (D.cy (j, k₀)) (D.o + (k₀ + 1) * D.hm)} ∧
          zlo = ⟨x, D.cy (j, k₀)⟩ ∧ zhi = ⟨x, D.o + (k₀ + 1) * D.hm⟩)) := by
  have hre : zlo.re = zhi.re := hxlo.trans hxhi.symm
  have hseg := segment_vertical hre hdir
  have hlt : zlo.im < zhi.im := by
    rcases eq_or_lt_of_le hdir with h | h
    · exact absurd (Complex.ext hre h) hne
    · exact h
  have hno' : ∀ h : ℝ, D.IsHt j h → ¬ (zlo.im < h ∧ h < zhi.im) := by
    intro h hh ⟨h1, h2⟩
    have hv : (⟨x, h⟩ : ℂ) ∈ segment ℝ zlo zhi := by
      rw [hseg, Set.mem_setOf_eq]
      exact ⟨hxlo.symm, h1.le, h2.le⟩
    rcases hno _ (hvert h hh) hv with h' | h'
    · have h'' : h = zlo.im := congrArg Complex.im h'
      linarith
    · have h'' : h = zhi.im := congrArg Complex.im h'
      linarith
  obtain ⟨k₀, hk1, hk2, hcase⟩ := D.consec_heights j hlo hhi hlt hno'
  refine ⟨k₀, hk1, hk2, ?_⟩
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have p1 : zlo = ⟨x, D.o + k₀ * D.hm⟩ := Complex.ext hxlo e1
    have p2 : zhi = ⟨x, D.cy (j, k₀)⟩ := Complex.ext hxhi e2
    refine Or.inl ⟨?_, p1, p2⟩
    rw [hseg, hxlo, e1, e2]
  · have p1 : zlo = ⟨x, D.cy (j, k₀)⟩ := Complex.ext hxlo e1
    have p2 : zhi = ⟨x, D.o + (k₀ + 1) * D.hm⟩ := Complex.ext hxhi e2
    refine Or.inr ⟨?_, p1, p2⟩
    rw [hseg, hxlo, e1, e2]


end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData
