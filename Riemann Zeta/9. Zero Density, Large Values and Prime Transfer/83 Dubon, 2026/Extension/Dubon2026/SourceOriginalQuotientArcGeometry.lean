import Dubon2026.SourceOriginalResiduePeriodQuotient

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
Use the existing cyclic arc successor, actual polygon corners and radial loop
injectivity. These supply the vertex and rotation clauses needed to apply
the additive arc-value theorem to residue-quotient boundary primitives.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.ArcPeriods
noncomputable section
open Set DissectionTrees
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

theorem castSucc_nxt_of_lt {n : ℕ} (k : Fin n) (h : k.val + 1 < n) :
    (nxt k).castSucc = k.succ := by
  apply Fin.ext
  simp [nxt, h]

theorem castSucc_nxt_of_not_lt {n : ℕ} (k : Fin n) (h : ¬ k.val + 1 < n) :
    (nxt k).castSucc = 0 ∧ k.succ = Fin.last n := by
  refine ⟨Fin.ext (by simp [nxt, h]), Fin.ext ?_⟩
  simp only [Fin.val_succ, Fin.val_last]
  have := k.2
  omega

theorem sv_injective (D : CellDissection N) (C : D.ιC) :
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
end Dubon2026.SourceFunctionField.CellGeometry.ArcPeriods
