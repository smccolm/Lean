import Dubon2026.SourceCuspTaylorFieldStability
import Dubon2026.SourceOriginalCuspFamily

/-! DUB-17/18 -> original torsion cardinality -> cusp parameters.
Every element of each actual original cusp embedding is a quotient of
convergent analytic Taylor germs. The already proved two-generator
description of the original field and exact cusp embedding values derive
this for all functions from the literal twisted/substituted j generators.
No convergence or analytic-realization hypothesis is supplied. Normalized
orders and the cusp place parameter still have to be constructed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField ConjugateSlots PrimeDegreeAux CuspTaylor

theorem original_slot_embedding_mem_realizedField (N : ℕ) [NeZero N]
    (ζ : ℂˣ) (s : Σ _ : ℕ, ℕ) (hs : s ∈ indices N)
    (ι : modularFunctionFieldOver N ℂ →ₐ[ℂ] LaurentSeries ℂ)
    (hj : ι (jOver N ℂ) = TS ℂ N 1) (hjN : ι (jNOver N ℂ) = slotValue ζ s.1 s.2)
    (f : modularFunctionFieldOver N ℂ) : ι f ∈ realizedField := by
  haveI : NeZero s.1 := ⟨index_fst_ne_zero hs⟩
  have hx : f ∈ IntermediateField.adjoin ℂ
      ({jOver N ℂ, jNOver N ℂ} : Set (modularFunctionFieldOver N ℂ)) := by
    rw [original_internal_pair_adjoin_top]
    exact IntermediateField.mem_top
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · rw [hj]
      exact TS_mem_realizedField N 1
    · rcases hy with rfl
      rw [hjN, slotValue_eq]
      exact TS_mem_realizedField _ _
  | algebraMap c =>
    rw [ι.commutes]
    exact realizedField.algebraMap_mem c
  | add y z _ _ hy hz =>
    rw [map_add]
    exact add_mem hy hz
  | inv y _ hy =>
    rw [map_inv₀]
    exact inv_mem hy
  | mul y z _ _ hy hz =>
    rw [map_mul]
    exact mul_mem hy hz

theorem original_cusp_embedding_analytic_quotient (N : ℕ) [NeZero N]
    (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N)
    (s : {s // s ∈ CuspLabels.labels N}) (f : modularFunctionFieldOver N ℂ) :
    ∃ g h : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ AnalyticAt ℂ h 0 ∧
      (CuspTaylor.series h : LaurentSeries ℂ) ≠ 0 ∧
      CuspLabels.embedding N ℂ ζ hζ s f =
        (CuspTaylor.series g : LaurentSeries ℂ) / (CuspTaylor.series h : LaurentSeries ℂ) := by
  have h := CuspLabels.embedding_spec N ℂ ζ hζ s
  exact original_slot_embedding_mem_realizedField N ζ s.1
    (CuspLabels.label_mem_indices N s.1 s.2) (CuspLabels.embedding N ℂ ζ hζ s) h.1 h.2.1 f

end
end Dubon2026.SourceFunctionField
