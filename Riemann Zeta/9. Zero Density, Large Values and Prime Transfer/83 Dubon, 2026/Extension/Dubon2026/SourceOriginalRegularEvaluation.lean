import Dubon2026.SourceOriginalPrescribedFiberCover

/-! DUB-17/18 -> geometric cell dissection -> ordinary sheets of the actual j map.
The existing finite divisor support makes the original regular locus open.
Exact residue evaluation identifies its fibers with the already constructed
finite positive-order fibers. These supply the native covering-map inputs.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set
attribute [local instance] placeTopology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem isOpen_original_regular_locus (f : F) :
    IsOpen {v : Place ℂ F | f ∈ v.toValuationSubring} := by
  letI := place_t2Space N
  have hfin : {v : Place ℂ F | v.ord f < 0}.Finite :=
    (finite_original_divisor_support N ℂ f).subset fun _ hv => ne_of_lt hv
  have he : {v : Place ℂ F | f ∈ v.toValuationSubring} =
      {v : Place ℂ F | v.ord f < 0}ᶜ := by
    ext v
    exact ⟨fun hv => not_lt.mpr (v.ord_nonneg_of_mem hv),
      fun hv => v.mem_of_ord_nonneg (not_lt.mp hv)⟩
  rw [he]
  exact hfin.isClosed.isOpen_compl

theorem mem_originalPositiveFiber_iff_regular_eval {f : F} {c : ℂ}
    (hne : f - algebraMap ℂ F c ≠ 0) (v : Place ℂ F) :
    v ∈ originalPositiveFiber N f c ↔
      f ∈ v.toValuationSubring ∧ originalPlaceEval N ℂ v f = c := by
  rw [mem_originalPositiveFiber]
  constructor
  · intro hv
    exact ⟨(original_sub_const_mem_iff N v f c).mp (v.mem_of_ord_nonneg hv.le),
      originalPlaceEval_eq_of_ord_sub_pos N ℂ v f c hv⟩
  · rintro ⟨hv, he⟩
    apply (originalPlaceEval_eq_zero_iff_ord_pos N ℂ v (sub_mem hv (v.algebraMap_mem' c)) hne).mp
    rw [originalPlaceEval_sub_algebraMap N ℂ v hv, he, sub_self]

theorem finite_original_regular_eval_fiber {f : F} {c : ℂ}
    (hne : f - algebraMap ℂ F c ≠ 0) :
    {v : Place ℂ F | f ∈ v.toValuationSubring ∧ originalPlaceEval N ℂ v f = c}.Finite := by
  have he : {v : Place ℂ F | f ∈ v.toValuationSubring ∧ originalPlaceEval N ℂ v f = c} =
      (originalPositiveFiber N f c : Set (Place ℂ F)) := by
    ext v
    exact (mem_originalPositiveFiber_iff_regular_eval N hne v).symm
  rw [he]
  exact Finset.finite_toSet _

end
end Dubon2026.SourceFunctionField.OriginalChart
