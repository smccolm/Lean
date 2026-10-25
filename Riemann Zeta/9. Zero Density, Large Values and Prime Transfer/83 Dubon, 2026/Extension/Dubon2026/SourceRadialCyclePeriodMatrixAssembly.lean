import Dubon2026.SourceRadialCyclePeriodPolygonData

/-! DUB-17/18 -> cover period generation -> jump-to-period matrix.
The existing integer subword and cycle calculations give the exact matrix
rows and subgroup containment. The actual cover consumer supplies the edge
integrals and their identification with the already constructed cycle loops. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
universe u
noncomputable section
open Set
variable {X : Type*} [TopologicalSpace X] {κ : Type*}

theorem period_matrix_of_primitive_word (D : RadialCellDissection X)
    (I : D.ιE → κ → ℂ) (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ)
    (J z : D.ιE → κ → ℂ)
    (hdec : ∀ f : D.ιE → ULift.{u} ℤ,
      (∀ w, (∑ e with (D.ends e).2 = w, f e) = ∑ e with (D.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j)
    (hzv : ∀ l, zv Z I l = z l)
    (hgen : AddSubgroup.closure (range J) ≤ AddSubgroup.closure (J '' ((T ∪ Ts)ᶜ : Finset D.ιE)))
    (hW : PrimitivePolygonConclusion D I Ts J) : CyclePeriodPolygonConclusion D I T Ts J z := by
  obtain ⟨hm, wd, hw₁, hw₃, hwjump⟩ := hW
  letI := hm
  have hZd := integer_decomposition_of_lift D (T := T) (Z := Z) hdec
  have hJF := jump_formula_of_word T Ts Z I J hZd wd hw₃ hwjump
  have hrow : ∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ, (wordMatrix wd j l : ℂ) • z l := by
    intro j hj
    rw [hJF j hj]
    simp_rw [hzv]
  have hcl := closure_generated_jumps_le_periods D T Ts J z (wordMatrix wd) hgen hrow
  unfold CyclePeriodPolygonConclusion
  intro Cside startV endV L m
  exact ⟨hm, wd, hw₁, hw₃, hwjump, hrow, hcl⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
