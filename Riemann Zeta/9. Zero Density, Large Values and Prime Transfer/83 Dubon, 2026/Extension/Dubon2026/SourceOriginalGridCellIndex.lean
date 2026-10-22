import Dubon2026.SourceOriginalJFiniteGrid

/-! DUB-17/18 -> original Abel-Jacobi -> finite original cell family.
Index the ordinary cells by the actual finite window and the branch cells
by their actual finite j fibers. This retains the exact cells constructed
from the original map and proves that the family is finite.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalJFiniteGrid
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (G : OriginalJFiniteGrid N Marked)

/-- The closed base window of the finite original grid. -/
def window : Set ℂ := {z | z.re ∈ Icc (G.D.o + G.D.lo * G.D.h) (G.D.o + (G.D.hi + 1) * G.D.h) ∧
  z.im ∈ Icc (G.D.o + G.D.lo * G.D.h) (G.D.o + (G.D.hi + 1) * G.D.h)}

/-- The actual finite set of square indices in the window. -/
def squares : Finset (ℤ × ℤ) := (Finset.Icc G.D.lo G.D.hi).product (Finset.Icc G.D.lo G.D.hi)

/-- Ordinary squares in the window. -/
def PlainIndex := {p : G.squares // G.D.capAt p = none}

instance : Fintype G.PlainIndex := by
  classical
  unfold PlainIndex
  infer_instance

/-- The unique square index of a prescribed branch value. -/
def branchSquare (b : ℂ) : ℤ × ℤ := (⌊(b.re - G.D.o) / G.D.h⌋, ⌊(b.im - G.D.o) / G.D.h⌋)

theorem branch_cap (b : ({0, 1728} : Finset ℂ)) : G.D.capAt (G.branchSquare b) = some b :=
  (G.D.cap_exact _ _).mpr ⟨b.2, rfl, rfl⟩

theorem branchSquare_mem (b : ({0, 1728} : Finset ℂ)) : G.branchSquare b ∈ G.squares := by
  have hb : b.val ∈ insert 0 (insert 1728 Marked) := by
    have h := b.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    tauto
  have hi := G.D.marked_inner hb
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hi.1.le, hi.2.1.le⟩,
    Finset.mem_Icc.mpr ⟨hi.2.2.1.le, hi.2.2.2.le⟩⟩

/-- Exact finite index set of all ordinary and ramified cells over the window. -/
def InteriorIndex := (G.PlainIndex × Fin (SourceLevelProjective.dedekindPsi N)) ⊕
  (Σ b : ({0, 1728} : Finset ℂ), ↥(originalPositiveFiber N (jOver N ℂ) b))

instance : Fintype G.InteriorIndex := by
  classical
  unfold InteriorIndex
  infer_instance

/-- The actual original analytic cell at a finite interior index. -/
def interiorCell : G.InteriorIndex → Cell N
  | .inl p => (G.ordinary p.1.1 p.1.2).C p.2
  | .inr p => (G.branch (G.branchSquare p.1) p.1 (G.branch_cap p.1)).C p.2

theorem square_subset_window {p : ℤ × ℤ} (hp : p ∈ G.squares) :
    SquareGrid.gridSquare G.D.o G.D.h p.1 p.2 ⊆ G.window := by
  obtain ⟨hj, hk⟩ := Finset.mem_product.mp hp
  obtain ⟨hj0, hj1⟩ := Finset.mem_Icc.mp hj
  obtain ⟨hk0, hk1⟩ := Finset.mem_Icc.mp hk
  intro z hz
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
  have hcast : (G.D.lo : ℝ) ≤ p.1 ∧ (p.1 : ℝ) ≤ G.D.hi ∧
      (G.D.lo : ℝ) ≤ p.2 ∧ (p.2 : ℝ) ≤ G.D.hi :=
    ⟨by exact_mod_cast hj0, by exact_mod_cast hj1, by exact_mod_cast hk0, by exact_mod_cast hk1⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith [G.D.mesh_pos, hcast.1, hcast.2.1, hcast.2.2.1, hcast.2.2.2]

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalJFiniteGrid
