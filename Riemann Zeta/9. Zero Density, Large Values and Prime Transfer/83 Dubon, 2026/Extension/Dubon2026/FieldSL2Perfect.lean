import Dubon2026.RingSL2Elementary
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs

/-! Native elementary matrices make the residual SL2 image perfect in
characteristic different from two and three. This is the cyclotomic-kernel
step for higher symmetric-power auxiliary primes in DUB-17. -/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable {K : Type*} [Field K]

/-- Over a field the native elementary matrices generate the actual SL2. -/
theorem fieldSL2_mem_of_unipotents (H : Subgroup SL(2, K))
    (hU : ∀ t : K, ringUpperUnipotent t ∈ H)
    (hL : ∀ t : K, ringLowerUnipotent t ∈ H) (g : SL(2, K)) : g ∈ H := by
  by_cases h : g 0 0 = 0
  · have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using g.property
    have hc : g 1 0 ≠ 0 := by intro hc; simp [h, hc] at hd
    apply ringSL2_mem_of_elementary_unit_pivot H hU hL g 1
    apply isUnit_iff_ne_zero.mpr
    simpa [ringUpperUnipotent, coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h] using hc
  · exact ringSL2_mem_of_unit_pivot H hU hL g (isUnit_iff_ne_zero.mpr h)

variable [NeZero (2 : K)] [NeZero (3 : K)]

/-- The native upper elementary matrix is an actual commutator. -/
theorem fieldUpperUnipotent_commutator (t : K) :
    ringSL2UnitDiagonal (Units.mk0 2 (NeZero.ne _)) * ringUpperUnipotent (t / 3) *
      (ringSL2UnitDiagonal (Units.mk0 2 (NeZero.ne _)))⁻¹ *
      (ringUpperUnipotent (t / 3))⁻¹ = ringUpperUnipotent t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ringUpperUnipotent, ringSL2UnitDiagonal, coe_mul, coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [NeZero.ne (2 : K), NeZero.ne (3 : K)]
  all_goals ring

/-- The native lower elementary matrix is an actual commutator. -/
theorem fieldLowerUnipotent_commutator (t : K) :
    ringSL2UnitDiagonal (Units.mk0 2 (NeZero.ne _)) * ringLowerUnipotent (-4 * t / 3) *
      (ringSL2UnitDiagonal (Units.mk0 2 (NeZero.ne _)))⁻¹ *
      (ringLowerUnipotent (-4 * t / 3))⁻¹ = ringLowerUnipotent t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ringLowerUnipotent, ringSL2UnitDiagonal, coe_mul, coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [NeZero.ne (2 : K), NeZero.ne (3 : K)]
  all_goals ring

/-- The literal special linear group is perfect at the allowed auxiliary characteristics. -/
theorem fieldSL2_isPerfect : Group.IsPerfect SL(2, K) := by
  constructor
  apply top_unique
  intro g _
  apply fieldSL2_mem_of_unipotents
  · intro t
    rw [← fieldUpperUnipotent_commutator t]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · intro t
    rw [← fieldLowerUnipotent_commutator t]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end
end Dubon2026
