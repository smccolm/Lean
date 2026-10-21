import Dubon2026.SourceLaurentCoefficientMap
import Mathlib.Tactic

/-! DUB-17/18 -> numerical modular genus -> exact all-level j-map degree
-> transport from the rational original field to its geometric coefficient
extension. Literal Laurent coefficients preserve linear independence.
Polynomial denominator clearing and the existing finite original extension
then preserve the coordinate degree, allowing rational prime-power proofs
to serve the actual algebraically closed coefficient field.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_GeometricBaseChange.lean and
P2M/Sol/S_ModularCurve_relfinrank_laurentBaseChange.lean.
Only the finite degree-transport chain is selected; external global instance
changes, proof options and the infinite-dimensional generalization are omitted.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField Polynomial

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem linearIndependent_coeffEmb {ι : Type*} {v : ι → LaurentSeries ℚ}
    (hv : LinearIndependent ℚ v) : LinearIndependent L (fun i => coeffEmb L (v i)) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  let b := Module.Free.chooseBasis ℚ L
  refine b.forall_coord_eq_zero_iff.mp fun k => ?_
  have hk : ∑ j ∈ s, (b.coord k (g j)) • v j = 0 := by
    ext n
    have hn := congrArg (fun x : LaurentSeries L => b.coord k (x.coeff n)) hg
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul,
      HahnSeries.coeff_zero, map_zero] at hn
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_zero]
    rw [← hn, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (g j), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  exact hv s (fun j => b.coord k (g j)) hk i hi

end
end Dubon2026.SourceFunctionField
