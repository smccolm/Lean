import Dubon2026.SourceRadialWordPeriodMatrix
import Dubon2026.SourceCellPolygonWordAntisymmetry

/-! DUB-17/18 -> cover Abel converse -> exact integer reciprocity matrix.
Restrict the same actual word matrix to complementary edges. Reuse native
cyclic-word antisymmetry unchanged; no intersection pairing is assumed. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
noncomputable section
variable {X : Type*} [TopologicalSpace X] {D : RadialCellDissection X}

/-- The exact polygon word matrix restricted to the complementary geometric edges. -/
def complementaryWordMatrix (T Ts : Finset D.ιE) {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : D.ιE × Bool // q.1 ∉ Ts}) :
    Matrix {l // l ∈ (T ∪ Ts)ᶜ} {l // l ∈ (T ∪ Ts)ᶜ} ℤ :=
  fun j l => wordMatrix wd j.1 l.1

theorem complementaryWordMatrix_transpose (T Ts : Finset D.ιE) {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : D.ιE × Bool // q.1 ∉ Ts}) :
    (complementaryWordMatrix T Ts wd).transpose = -complementaryWordMatrix T Ts wd := by
  funext j l
  have hj : j.1 ∉ Ts := fun h => (Finset.mem_compl.mp j.2) (Finset.mem_union_right T h)
  have hl : l.1 ∉ Ts := fun h => (Finset.mem_compl.mp l.2) (Finset.mem_union_right T h)
  simp only [Matrix.transpose_apply, Matrix.neg_apply, complementaryWordMatrix,
    wordMatrix_of_not_mem wd hj, wordMatrix_of_not_mem wd hl]
  exact DissectionPeriods.wordChain_antisymm wd j.1 l.1 hj hl


end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
