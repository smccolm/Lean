import Dubon2026.SourceConstantFieldRationalDescent
import Dubon2026.SourceOriginalComplexCoordinateTrace
import Dubon2026.SourceOriginalJFiberDegree
import Dubon2026.SourceLevelPsiPrimeStep

/-! DUB-17/18 -> original Qbar Picard torsion -> principal-divisor descent.
The existing positive j-fiber degree supplies a place over every finite value.
Thus coordinate functions regular over constants outside Qbar lie in the
complex linear span of the original arithmetic field. Applied to the proved
trace regularity, this descends the actual coordinate trace coefficients.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower originalFieldScalarTower

theorem exists_original_j_fiber_place (c : ℂ) :
    ∃ v : Place ℂ FC, 0 < v.ord (jOver N ℂ - algebraMap ℂ FC c) := by
  by_contra h
  have he : IsEmpty {v : Place ℂ FC // 0 < v.ord (jOver N ℂ - algebraMap ℂ FC c)} :=
    ⟨fun v => h ⟨v.val, v.property⟩⟩
  letI := he
  have hs := sum_original_j_fiber_orders_eq_psi N ℂ c
  simp only [finsum_of_isEmpty] at hs
  have hp := SourceLevelProjective.dedekindPsi_pos (NeZero.ne N)
  omega

theorem original_coordinate_mem_span_of_regular {t : FC}
    (ht : t ∈ IntermediateField.adjoin ℂ (Set.singleton (jOver N ℂ)))
    (hreg : ∀ c : ℂ, c ∉ Set.range sigma → ∀ v : Place ℂ FC,
      0 < v.ord (jOver N ℂ - algebraMap ℂ FC c) → 0 ≤ v.ord t) :
    t ∈ Submodule.span ℂ (Set.range (fieldMap N)) := by
  apply ConstantField.mem_span_of_coordinate_regular (K := Qbar) (K' := ℂ)
    (F := FQ) (F' := FC) (x := jOver N Qbar)
  · intro c
    change ∃ v : Place ℂ FC, 0 < v.ord (fieldMap N (jOver N Qbar) - algebraMap ℂ FC c)
    rw [fieldMap_j]
    exact exists_original_j_fiber_place N c
  · change t ∈ IntermediateField.adjoin ℂ (Set.singleton (fieldMap N (jOver N Qbar)))
    rwa [fieldMap_j]
  · intro c hc v hv
    apply hreg c hc v
    change 0 < v.ord (fieldMap N (jOver N Qbar) - algebraMap ℂ FC c) at hv
    rwa [fieldMap_j] at hv

theorem original_coordinate_trace_mem_span (w : FC)
    (hw : ∀ W : Place ℂ FC, (∀ v, W ≠ liftPlace N v) → w ∈ W.toValuationSubring) :
    ((Algebra.trace (IntermediateField.adjoin ℂ (Set.singleton (jOver N ℂ))) FC w :
      IntermediateField.adjoin ℂ (Set.singleton (jOver N ℂ))) : FC) ∈
        Submodule.span ℂ (Set.range (fieldMap N)) := by
  apply original_coordinate_mem_span_of_regular N
  · exact Subtype.property _
  · intro c hc v hv
    exact v.ord_nonneg_of_mem (original_coordinate_trace_mem N hc v hv w hw)

end
end Dubon2026.SourceFunctionField.OriginalConstantField
