import Dubon2026.SourceRadialResiduePeriodQuotient
import Dubon2026.SourceOriginalQuotientArcGeometry

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Radial loop injectivity identifies the starting arc at a cell vertex.
The existing cyclic-index lemmas are reused unchanged. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialArcPeriods
noncomputable section
open Set
variable {X : Type*} [TopologicalSpace X]

theorem sv_injective (D : RadialCellDissection X) (C : D.ιC) :
    Function.Injective fun k : Fin (D.cell C).R.N => sv D ⟨C, k⟩ := by
  intro k k' h
  have h1 : (D.cell C).bdry ((D.cell C).R.φs k.castSucc) = D.vert (sv D ⟨C, k⟩) :=
    (D.arc_ends C k).1
  have h2 : (D.cell C).bdry ((D.cell C).R.φs k'.castSucc) = D.vert (sv D ⟨C, k'⟩) :=
    (D.arc_ends C k').1
  change sv D ⟨C, k⟩ = sv D ⟨C, k'⟩ at h
  rw [h] at h1
  have hb := h1.trans h2.symm
  have ht : ∀ s, (D.cell C).R.loop s ∈ (D.cell C).ζ.target :=
    fun s => (D.cell C).hKt ((D.cell C).R.loop_mem_K s)
  have hl := (D.cell C).ζ.symm.injOn (ht _) (ht _) hb
  have hm : ∀ j : Fin (D.cell C).R.N, (D.cell C).R.φs j.castSucc ∈ Ico 0 (2 * Real.pi) := by
    intro j
    refine ⟨GridWindow.φs_nonneg _ _, ?_⟩
    rw [← (D.cell C).R.hφN]
    exact (D.cell C).R.hmono (Fin.castSucc_lt_last j)
  have he := GridWindow.loop_injOn_Ico (D.cell C).R (hm k) (hm k') hl
  exact Fin.castSucc_injective _ ((D.cell C).R.hmono.injective he)

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialArcPeriods
