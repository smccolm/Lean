import Dubon2026.SourceOriginalDifferentialResidues
import Dubon2026.SourceOriginalChartReadFieldLaws

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
meromorphic exponential. Subtracting the actual residue divided by the
original uniformizer removes a simple pole. This gives the regular local
coefficient used to construct the exponential model with the prescribed order.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_simple_pole_regular_part (v : Place ℂ F) (η : Ω[F⁄ℂ])
    (hη : -1 ≤ v.ordDifferential η) (c : ℂ)
    (hc : originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = c) :
    v.differentialCoeff η - algebraMap ℂ F c * v.uniformizer⁻¹ ∈ v.toValuationSubring := by
  let a := v.uniformizer * v.differentialCoeff η - algebraMap ℂ F c
  have ha : a ∈ v.toValuationSubring :=
    sub_mem ((original_simple_pole_bound_iff N v η).mp hη) (v.algebraMap_mem' c)
  have hzero : originalPlaceEval N ℂ v a = 0 := by
    rw [originalPlaceEval_sub_algebraMap N ℂ v
      ((original_simple_pole_bound_iff N v η).mp hη), hc, sub_self]
  have he : v.differentialCoeff η - algebraMap ℂ F c * v.uniformizer⁻¹ = a * v.uniformizer⁻¹ := by
    dsimp [a]
    field_simp [v.uniformizer_ne_zero]
  rw [he]
  by_cases ha0 : a = 0
  · rw [ha0, zero_mul]
    exact zero_mem _
  · have hp := (originalPlaceEval_eq_zero_iff_ord_pos N ℂ v ha ha0).mp hzero
    apply v.mem_of_ord_nonneg
    rw [v.ord_mul ha0 (inv_ne_zero v.uniformizer_ne_zero), v.ord_inv, v.ord_uniformizer]
    omega

end
end Dubon2026.SourceFunctionField
