import Dubon2026.SourceOriginalAnalyticJSheets
import Dubon2026.SourceCellSheetCollar
import Dubon2026.SourceCellGridSeparation

/-! DUB-17/18 -> geometric cell dissection -> actual j grid scale.
The proved ordinary analytic sheet neighborhoods form a uniform cover on
each bounded region separated from the branch values. Choose a finer grid
avoiding and separating all selected values. The analytic cover is derived
from the actual j map; only the geometric region and marked values are inputs.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_j_sheet_collar (R : ℝ) (s : ℂ → ℝ)
    (hs : ∀ b ∈ ({0, 1728} : Finset ℂ), 0 < s b) :
    ∃ δ > 0, ∀ t : ℂ, ‖t‖ ≤ R + 1 →
      (∀ b ∈ ({0, 1728} : Finset ℂ), s b ≤ dist t b) →
      ∃ (V : Set ℂ) (A : Fin (SourceLevelProjective.dedekindPsi N) → AnalyticCoord N),
        IsOpen V ∧ (0 : ℂ) ∉ V ∧ (1728 : ℂ) ∉ V ∧
        IsOriginalSheetFamily (jOver N ℂ) V (fun i => (A i).ζ) ∧ Metric.ball t δ ⊆ V := by
  classical
  let Good := fun V : Set ℂ => IsOpen V ∧ (0 : ℂ) ∉ V ∧ (1728 : ℂ) ∉ V ∧
    ∃ A : Fin (SourceLevelProjective.dedekindPsi N) → AnalyticCoord N,
      IsOriginalSheetFamily (jOver N ℂ) V (fun i => (A i).ζ)
  have hcover : ∀ t : ℂ, ‖t‖ ≤ R + 1 →
      (∀ b ∈ ({0, 1728} : Finset ℂ), s b ≤ dist t b) →
      ∃ V, IsOpen V ∧ t ∈ V ∧ Good V := by
    intro t _ hd
    have hne : ∀ b ∈ ({0, 1728} : Finset ℂ), t ≠ b := by
      intro b hb he
      have hbd := hd b hb
      rw [he, dist_self] at hbd
      exact not_le_of_gt (hs b hb) hbd
    obtain ⟨V, A, hV, ht, h0, h1728, hA⟩ := exists_original_j_analytic_sheet_neighborhood (N := N) t
      (hne 0 (by simp)) (hne 1728 (by simp))
    exact ⟨V, hV, ht, hV, h0, h1728, A, hA⟩
  obtain ⟨δ, hδ, hcollar⟩ := SquareGrid.exists_lebesgue_collar {0, 1728} s Good hcover
  refine ⟨δ, hδ, ?_⟩
  intro t ht hd
  obtain ⟨V, ⟨hV, h0, h1728, A, hA⟩, hball⟩ := hcollar t ht hd
  exact ⟨V, A, hV, h0, h1728, hA, hball⟩

theorem exists_original_j_separating_grid (R : ℝ) (s : ℂ → ℝ)
    (hs : ∀ b ∈ ({0, 1728} : Finset ℂ), 0 < s b) (Marked : Finset ℂ) :
    ∃ δ o h : ℝ, 0 < δ ∧ 0 < h ∧ h < δ ∧
      (∀ b ∈ insert 0 (insert 1728 Marked), ∀ k : ℤ,
        b.re - o ≠ k * h ∧ b.im - o ≠ k * h) ∧
      (∀ b ∈ insert 0 (insert 1728 Marked), ∀ b' ∈ insert 0 (insert 1728 Marked), b ≠ b' →
        ⌊(b.re - o) / h⌋ = ⌊(b'.re - o) / h⌋ →
        ⌊(b.im - o) / h⌋ = ⌊(b'.im - o) / h⌋ → False) ∧
      ∀ t : ℂ, ‖t‖ ≤ R + 1 →
        (∀ b ∈ ({0, 1728} : Finset ℂ), s b ≤ dist t b) →
        ∃ (V : Set ℂ) (A : Fin (SourceLevelProjective.dedekindPsi N) → AnalyticCoord N),
          IsOpen V ∧ (0 : ℂ) ∉ V ∧ (1728 : ℂ) ∉ V ∧
          IsOriginalSheetFamily (jOver N ℂ) V (fun i => (A i).ζ) ∧ Metric.ball t δ ⊆ V := by
  classical
  obtain ⟨δ, hδ, hcollar⟩ := exists_original_j_sheet_collar N R s hs
  obtain ⟨o, h, hh, hhδ, hav, hsep⟩ :=
    SquareGrid.exists_separating_grid (insert 0 (insert 1728 Marked)) hδ
  exact ⟨δ, o, h, hδ, hh, hhδ, hav, hsep, hcollar⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
