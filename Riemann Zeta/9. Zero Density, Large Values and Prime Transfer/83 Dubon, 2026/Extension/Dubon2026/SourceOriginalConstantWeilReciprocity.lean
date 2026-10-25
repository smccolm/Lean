import Dubon2026.SourceOriginalWeilEvaluation
import Dubon2026.SourceOriginalPrincipalDivisors
import Mathlib.FieldTheory.AlgebraicClosure

/-! DUB-17/18 -> original Weil reciprocity -> constant second function.
Native principal-divisor degree zero and actual rational residues prove
evaluation of a nonzero constant on a principal divisor is one. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
open scoped Classical BigOperators
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L] (N : ℕ) [NeZero N]

omit [IsAlgClosed L] in
theorem originalPrincipalDivisor_algebraMap (c : L) :
    originalPrincipalDivisor N L (algebraMap L (modularFunctionFieldOver N L) c) = 0 := by
  ext v
  exact v.ord_algebraMap c

theorem originalDivisorEval_constant_principal (c : L) (hc : c ≠ 0)
    (f : modularFunctionFieldOver N L) :
    originalDivisorEval N L (algebraMap L (modularFunctionFieldOver N L) c)
      (originalPrincipalDivisor N L f) = 1 := by
  let D := originalPrincipalDivisor N L f
  have hs : ∑ v ∈ D.support, D v = 0 := by
    have hd := degree_originalPrincipalDivisor N L f
    rw [Divisor.degree_eq_sum_support] at hd
    have hr (v : Place L (modularFunctionFieldOver N L)) : Module.finrank L v.ResidueField = 1 :=
      Module.finrank_of_bijective_algebraMap (original_place_residue_algebraMap_bijective N L v)
    simpa only [hr, Nat.cast_one, mul_one] using hd
  have hp : (∏ v ∈ D.support, c ^ D v) = c ^ (∑ v ∈ D.support, D v) := by
    induction D.support using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]
  change (∏ v ∈ D.support, originalPlaceEval N L v
    (algebraMap L (modularFunctionFieldOver N L) c) ^ D v) = 1
  simp_rw [originalPlaceEval_algebraMap]
  rw [hp, hs, zpow_zero]

theorem original_weil_reciprocity_constant (f : modularFunctionFieldOver N L) (c : L) (hc : c ≠ 0) :
    originalDivisorEval N L f
      (originalPrincipalDivisor N L (algebraMap L (modularFunctionFieldOver N L) c)) =
    originalDivisorEval N L (algebraMap L (modularFunctionFieldOver N L) c)
      (originalPrincipalDivisor N L f) := by
  rw [originalPrincipalDivisor_algebraMap, originalDivisorEval_zero,
    originalDivisorEval_constant_principal L N c hc f]

end
end Dubon2026.SourceFunctionField
