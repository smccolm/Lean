import Dubon2026.SourceOriginalComplexCoordinateBasis
import Dubon2026.SourceOriginalCoordinateDescent
import Dubon2026.SourceConstantFieldTraceReconstruction

/-! DUB-17/18 -> original arithmetic Picard injectivity -> principal-divisor
descent. Trace reconstruction now shows that every original complex function
regular outside the arithmetic place image is a finite complex linear
combination of original arithmetic functions. The actual constant-field map,
coordinate degree, place orders and coordinate trace descent discharge all
geometric and basis-comparison inputs.
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

theorem original_mem_span_of_regular_off_image (z : FC)
    (hz : ∀ W : Place ℂ FC, (∀ v, W ≠ liftPlace N v) → z ∈ W.toValuationSubring) :
    z ∈ Submodule.span ℂ (Set.range (fieldMap N)) := by
  classical
  let kx : IntermediateField Qbar FQ := IntermediateField.adjoin Qbar {jOver N Qbar}
  let kx' : IntermediateField ℂ FC := IntermediateField.adjoin ℂ {algebraMap FQ FC (jOver N Qbar)}
  letI := finiteDimensional_original N Qbar
  letI : CharZero kx := charZero_of_injective_algebraMap (algebraMap Qbar kx).injective
  letI : Algebra.IsSeparable kx FQ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let y := Module.finBasis kx FQ
  obtain ⟨y', hy⟩ := exists_original_complex_coordinate_basis N y
  let yd := (Algebra.traceForm kx FQ).dualBasis (traceForm_nondegenerate kx FQ) y
  have ht : ∀ i, ((Algebra.trace kx' FC (z * fieldMap N (yd i)) : kx') : FC) ∈
      Submodule.span ℂ (Set.range (fieldMap N)) := by
    intro i
    change ((Algebra.trace (IntermediateField.adjoin ℂ
      (Set.singleton (fieldMap N (jOver N Qbar)))) FC (z * fieldMap N (yd i)) :
        IntermediateField.adjoin ℂ (Set.singleton (fieldMap N (jOver N Qbar)))) : FC) ∈ _
    rw [fieldMap_j]
    apply original_coordinate_trace_mem_span N
    intro W hW
    exact mul_mem (hz W hW) (W.mem_of_ord_nonneg (by rw [ord_phi_of_forall_ne N hW]))
  have hA : ∀ t, t ∈ Submodule.span ℂ (Set.range (fieldMap N)) → ∀ f : FQ,
      t * fieldMap N f ∈ Submodule.span ℂ (Set.range (fieldMap N)) := by
    intro t ht f
    have he : Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (fieldMap N))) =
        Submodule.span ℂ (Set.range (fieldMap N)) := ConstantField.span_range_eq_adjoin FQ FC ℂ
    rw [← he] at ht ⊢
    exact (Algebra.adjoin ℂ _).mul_mem ht (Algebra.subset_adjoin ⟨f, rfl⟩)
  rw [ConstantField.eq_sum_trace_mul (K := Qbar) (K' := ℂ) y y' hy z]
  exact Submodule.sum_mem _ fun i _ => hA _ (ht i) _

end
end Dubon2026.SourceFunctionField.OriginalConstantField
