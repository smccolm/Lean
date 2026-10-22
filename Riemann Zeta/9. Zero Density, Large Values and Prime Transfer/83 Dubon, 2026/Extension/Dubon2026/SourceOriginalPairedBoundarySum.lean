import Dubon2026.SourceOriginalCellArcPartition
import Dubon2026.SourceOriginalPairedArcOverlap

/-! DUB-17/18 -> raw reciprocity -> global residue-jump summation.
The actual dissection's side bijection reindexes the finite cell boundary sum
as the sum of its oriented edge pairs. Native interval additivity supplies the
per-cell partition, so no boundary-sum identity is assumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open Set MeasureTheory
open scoped Real
variable {N : ℕ} [NeZero N]

theorem CellDissection.arcOf_side (𝒟 : CellDissection N)
    (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) : 𝒟.arcOf (𝒟.side p.1 p.2) = p :=
  Function.leftInverse_surjInv 𝒟.side_bij p

theorem CellDissection.sum_cell_integrals_eq_sum_paired (𝒟 : CellDissection N)
    (H : 𝒟.ιC → ℝ → ℂ)
    (hint : ∀ C (k : Fin (𝒟.cell C).R.N), IntervalIntegrable (H C) volume
      ((𝒟.cell C).R.φs k.castSucc) ((𝒟.cell C).R.φs k.succ)) :
    (∑ C : 𝒟.ιC, ∫ s in (0 : ℝ)..(2 * π), H C s) =
      ∑ e : 𝒟.ιE, (𝒟.arcInt H (𝒟.arcOf (e, true)) + 𝒟.arcInt H (𝒟.arcOf (e, false))) := by
  simp_rw [𝒟.integral_eq_sum_arcInt H _ (hint _)]
  rw [← Fintype.sum_sigma (𝒟.arcInt H)]
  have hbij : ∑ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), 𝒟.arcInt H p =
      ∑ q : 𝒟.ιE × Bool, 𝒟.arcInt H (𝒟.arcOf q) := by
    rw [← 𝒟.side_bij.sum_comp (fun q => 𝒟.arcInt H (𝒟.arcOf q))]
    exact Finset.sum_congr rfl fun p _ => congrArg (𝒟.arcInt H) (𝒟.arcOf_side p).symm
  rw [hbij, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun e _ => Fintype.sum_bool _

end
end Dubon2026.SourceFunctionField.CellGeometry
