import Dubon2026.SourceLaurentCoefficientIndependence

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> original constant-field map. The existing literal coefficient-coordinate proof applies
to the Qbar-to-complex extension as well. This avoids the external general
function-field linear-disjointness development. The same basis-coordinate
argument is retained; no hypothesis of preserved independence is assumed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]

theorem linearIndependent_coeffMap_algebraMap {ι : Type*} {v : ι → LaurentSeries K}
    (hv : LinearIndependent K v) : LinearIndependent L (fun i => coeffMap (algebraMap K L) (v i)) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  let b := Module.Free.chooseBasis K L
  refine b.forall_coord_eq_zero_iff.mp fun k => ?_
  have hk : ∑ j ∈ s, (b.coord k (g j)) • v j = 0 := by
    ext n
    have hn := congrArg (fun x : LaurentSeries L => b.coord k (x.coeff n)) hg
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul,
      HahnSeries.coeff_zero, map_zero] at hn
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_zero]
    rw [← hn, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (g j), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  exact hv s (fun j => b.coord k (g j)) hk i hi


end
end Dubon2026.SourceFunctionField
