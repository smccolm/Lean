import Dubon2026.SourceConstantFieldRationalDescent
import Dubon2026.SourceGammaOneComplexCoordinateTrace
import Dubon2026.SourceGammaOneJFiberDegree

/-! DUB-17/18 -> original Qbar Picard torsion -> principal-divisor descent.
The existing positive j-fiber degree supplies a place over every finite value.
Thus coordinate functions regular over constants outside Qbar lie in the
complex linear span of the original arithmetic field. Applied to the proved
trace regularity, this descends the actual coordinate trace coefficients.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => functionFieldOver (Gamma1 N) Qbar
local notation "FC" => functionFieldOver (Gamma1 N) ℂ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower arithmeticFieldScalarTower

theorem exists_j_fiber_place (c : ℂ) :
    ∃ v : Place ℂ FC, 0 < v.ord (jCoordinateOver (Gamma1 N) ℂ - algebraMap ℂ FC c) := by
  by_contra h
  have he : IsEmpty {v : Place ℂ FC // 0 < v.ord (jCoordinateOver (Gamma1 N) ℂ - algebraMap ℂ FC c)} :=
    ⟨fun v => h ⟨v.val, v.property⟩⟩
  letI := he
  have hT : ModularGroup.T ∈ Gamma1 N := by simp [Gamma1_mem, ModularGroup.T]
  have hs := sum_j_fiber_orders_eq_finrank hT c
  simp only [finsum_of_isEmpty] at hs
  letI := finiteDimensional_jCoordinateOver hT ℂ
  have hp : 0 < Module.finrank
      (IntermediateField.adjoin ℂ {jCoordinateOver (Gamma1 N) ℂ}) FC := Module.finrank_pos
  omega

theorem coordinate_mem_span_of_regular {t : FC}
    (ht : t ∈ IntermediateField.adjoin ℂ (Set.singleton (jCoordinateOver (Gamma1 N) ℂ)))
    (hreg : ∀ c : ℂ, c ∉ Set.range OriginalConstantField.sigma → ∀ v : Place ℂ FC,
      0 < v.ord (jCoordinateOver (Gamma1 N) ℂ - algebraMap ℂ FC c) → 0 ≤ v.ord t) :
    t ∈ Submodule.span ℂ (Set.range (fieldMap N)) := by
  apply SourceCurve.ConstantField.mem_span_of_coordinate_regular (K := Qbar) (K' := ℂ)
    (F := FQ) (F' := FC) (x := jCoordinateOver (Gamma1 N) Qbar)
  · intro c
    change ∃ v : Place ℂ FC, 0 < v.ord (fieldMap N (jCoordinateOver (Gamma1 N) Qbar) - algebraMap ℂ FC c)
    rw [fieldMap_j]
    exact exists_j_fiber_place N c
  · change t ∈ IntermediateField.adjoin ℂ (Set.singleton (fieldMap N (jCoordinateOver (Gamma1 N) Qbar)))
    rwa [fieldMap_j]
  · intro c hc v hv
    apply hreg c hc v
    change 0 < v.ord (fieldMap N (jCoordinateOver (Gamma1 N) Qbar) - algebraMap ℂ FC c) at hv
    rwa [fieldMap_j] at hv

theorem coordinate_trace_mem_span (w : FC)
    (hw : ∀ W : Place ℂ FC, (∀ v, W ≠ liftPlace N v) → w ∈ W.toValuationSubring) :
    ((Algebra.trace (IntermediateField.adjoin ℂ (Set.singleton (jCoordinateOver (Gamma1 N) ℂ))) FC w :
      IntermediateField.adjoin ℂ (Set.singleton (jCoordinateOver (Gamma1 N) ℂ))) : FC) ∈
        Submodule.span ℂ (Set.range (fieldMap N)) := by
  apply coordinate_mem_span_of_regular N
  · exact Subtype.property _
  · intro c hc v hv
    exact v.ord_nonneg_of_mem (coordinate_trace_mem N hc v hv w hw)

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
