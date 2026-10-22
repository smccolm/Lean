import Dubon2026.SourceOriginalNewCoordinatePlaces
import Dubon2026.SourceConstantFieldTraceRegularity

/-! DUB-17/18 -> arithmetic Picard injectivity -> principal-divisor descent.
For a function regular at every complex place outside the original arithmetic
image, its trace to the actual complex j-coordinate field is regular over
every constant outside Qbar. Actual finite degree, transcendence, residue values and
place extension discharge the generic trace-regularity premises.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]
local notation "FC" => modularFunctionFieldOver N ℂ

theorem original_coordinate_trace_mem {c : ℂ} (hc : c ∉ Set.range sigma)
    (v' : Place ℂ FC) (hv' : 0 < v'.ord (jOver N ℂ - algebraMap ℂ FC c))
    (w : FC) (hw : ∀ W : Place ℂ FC, (∀ v, W ≠ liftPlace N v) → w ∈ W.toValuationSubring) :
    ((Algebra.trace (IntermediateField.adjoin ℂ (Set.singleton (jOver N ℂ))) FC w :
      IntermediateField.adjoin ℂ (Set.singleton (jOver N ℂ))) : FC) ∈ v'.toValuationSubring := by
  letI := finiteDimensional_original N ℂ
  apply ConstantField.trace_mem_of_forall_place (jOver N ℂ) (transcendental_jOver N ℂ)
  intro W hW
  exact hw W (new_of_mem_coordinate_localRing N hc v' hv' W hW)

end
end Dubon2026.SourceFunctionField.OriginalConstantField
