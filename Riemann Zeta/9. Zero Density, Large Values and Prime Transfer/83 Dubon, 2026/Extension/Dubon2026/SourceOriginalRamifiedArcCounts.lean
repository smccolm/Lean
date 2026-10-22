import Dubon2026.SourceOriginalDissectionGenusCount

/-! DUB-17/18 -> original Abel-Jacobi -> the ramified arc count.
The actual power charts multiply each base arc count by its original order.
The previously proved j-fiber and pole degree sums total these multiplicities.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem OriginalBranchRegionFamily.sum_arcs {b : ℂ} {R : RadialRegion}
    (B : OriginalBranchRegionFamily N b R) :
    (∑ v, ((B.C v).R.N : ℤ)) = (SourceLevelProjective.dedekindPsi N : ℤ) * R.N := by
  have he (v : originalPositiveFiber N (jOver N ℂ) b) :
      ((B.C v).R.N : ℤ) = v.val.ord (jOver N ℂ - algebraMap ℂ F b) * (R.N : ℤ) := by
    rw [(B.geometry v).2.2.1.2.1, Nat.cast_mul]
    rw [Int.toNat_of_nonneg ((mem_originalPositiveFiber N (jOver N ℂ) b v.val).mp v.property).le]
  simp_rw [he]
  rw [← Finset.sum_mul, Finset.sum_coe_sort _
      (fun v : Place ℂ F => v.ord (jOver N ℂ - algebraMap ℂ F b)),
    sum_original_j_fiber_orders_finset N ℂ b _ (mem_originalPositiveFiber N (jOver N ℂ) b)]

theorem OriginalPoleRegionFamily.sum_arcs {W : RadialRegion}
    (B : OriginalPoleRegionFamily N W) :
    (∑ v, ((B.C v).R.N : ℤ)) = (SourceLevelProjective.dedekindPsi N : ℤ) * W.N := by
  have he (v : originalPositiveFiber N (jOver N ℂ)⁻¹ 0) :
      ((B.C v).R.N : ℤ) = -v.val.ord (jOver N ℂ) * (W.N : ℤ) := by
    have hv : 0 < v.val.ord (jOver N ℂ)⁻¹ := by
      simpa only [map_zero, sub_zero] using
        (mem_originalPositiveFiber N (jOver N ℂ)⁻¹ 0 v.val).mp v.property
    rw [(B.geometry v).2.2.1.2.1, Nat.cast_mul, Int.toNat_of_nonneg hv.le,
      B.reciprocal.2.1, v.val.ord_inv]
  simp_rw [he]
  rw [← Finset.sum_mul, Finset.sum_coe_sort _ (fun v : Place ℂ F => -v.ord (jOver N ℂ)),
    sum_original_j_pole_orders_finset N ℂ _ (fun v => by
      rw [mem_originalPositiveFiber, map_zero, sub_zero, v.ord_inv, neg_pos])]

end
end Dubon2026.SourceFunctionField.CellGeometry
