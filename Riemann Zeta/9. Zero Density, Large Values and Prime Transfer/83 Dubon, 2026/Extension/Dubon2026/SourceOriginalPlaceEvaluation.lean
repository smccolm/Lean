import Dubon2026.SourceOriginalResidueFinite
import Dubon2026.SourceCurvePlaceCenters

/-! DUB-17/18 -> modular Galois association -> original Tate module
-> exact original torsion cardinality -> complex Abel--Jacobi comparison
-> analytic charts on the actual original places. Their coordinate values
must agree with the algebraic residue, including at removable singularities.
Use the already proved bijection from constants to each original residue
field. This gives the actual evaluation and its exact vanishing/order test;
no rational-place, residue identification or evaluation premise is supplied.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve IsLocalRing
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (v : Place L (modularFunctionFieldOver N L))

/-- The proved identification of the original residue field with its constants. -/
def originalPlaceResidueEquiv : L ≃+* v.ResidueField :=
  RingEquiv.ofBijective (algebraMap L v.ResidueField)
    (original_place_residue_algebraMap_bijective N L v)

/-- Evaluation of a regular original function by its actual residue. -/
def originalPlaceRegularEval : v.toValuationSubring →+* L :=
  (originalPlaceResidueEquiv N L v).symm.toRingHom.comp (residue v.toValuationSubring)

theorem originalPlaceRegularEval_algebraMap (c : L) :
    originalPlaceRegularEval N L v (algebraMap L v.toValuationSubring c) = c := by
  change (originalPlaceResidueEquiv N L v).symm
    (algebraMap L v.ResidueField c) = c
  exact (originalPlaceResidueEquiv N L v).symm_apply_apply c

/-- The original place value, with value zero assigned at poles. -/
def originalPlaceEval (f : modularFunctionFieldOver N L) : L := by
  classical
  exact if hf : f ∈ v.toValuationSubring then originalPlaceRegularEval N L v ⟨f, hf⟩ else 0

theorem originalPlaceEval_of_mem {f : modularFunctionFieldOver N L}
    (hf : f ∈ v.toValuationSubring) :
    originalPlaceEval N L v f = originalPlaceRegularEval N L v ⟨f, hf⟩ := by
  classical
  exact dif_pos hf

theorem originalPlaceEval_algebraMap (c : L) :
    originalPlaceEval N L v (algebraMap L (modularFunctionFieldOver N L) c) = c := by
  rw [originalPlaceEval_of_mem N L v (v.algebraMap_mem' c)]
  exact originalPlaceRegularEval_algebraMap N L v c

theorem originalPlaceEval_sub_algebraMap {f : modularFunctionFieldOver N L}
    (hf : f ∈ v.toValuationSubring) (c : L) :
    originalPlaceEval N L v (f - algebraMap L (modularFunctionFieldOver N L) c) =
      originalPlaceEval N L v f - c := by
  rw [originalPlaceEval_of_mem N L v (sub_mem hf (v.algebraMap_mem' c)),
    originalPlaceEval_of_mem N L v hf]
  change originalPlaceRegularEval N L v
    (⟨f, hf⟩ - algebraMap L v.toValuationSubring c) = _
  rw [map_sub, originalPlaceRegularEval_algebraMap]

theorem originalPlaceEval_eq_zero_iff_ord_pos {f : modularFunctionFieldOver N L}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    originalPlaceEval N L v f = 0 ↔ 0 < v.ord f := by
  rw [originalPlaceEval_of_mem N L v hf]
  change (originalPlaceResidueEquiv N L v).symm (residue v.toValuationSubring ⟨f, hf⟩) = 0 ↔ _
  rw [map_eq_zero_iff _ (originalPlaceResidueEquiv N L v).symm.injective,
    residue_eq_zero_iff, v.mem_maximalIdeal_iff_ord_pos hf0 hf]

theorem originalPlaceEval_eq_of_ord_sub_pos (f : modularFunctionFieldOver N L) (c : L)
    (h : 0 < v.ord (f - algebraMap L (modularFunctionFieldOver N L) c)) :
    originalPlaceEval N L v f = c := by
  have hmem := v.mem_of_ord_nonneg h.le
  have hf : f ∈ v.toValuationSubring := by
    simpa only [sub_add_cancel] using add_mem hmem (v.algebraMap_mem' c)
  have hne : f - algebraMap L (modularFunctionFieldOver N L) c ≠ 0 := by
    intro he
    rw [he, v.ord_zero] at h
    exact (lt_irrefl 0) h
  have hz := (originalPlaceEval_eq_zero_iff_ord_pos N L v hmem hne).mpr h
  rw [originalPlaceEval_sub_algebraMap N L v hf] at hz
  exact sub_eq_zero.mp hz

end
end Dubon2026.SourceFunctionField
