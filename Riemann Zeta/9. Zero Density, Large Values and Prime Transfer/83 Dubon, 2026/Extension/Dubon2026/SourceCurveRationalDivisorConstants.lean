import Dubon2026.SourceCurveRationalDivisorEvaluation
import Dubon2026.SourceCurvePicardGroup

/-! DUB-17/18 -> Kummer detection -> the constant case of cover reciprocity.
Closed residue values and the actual degree-zero divisor prove the constant
evaluation formula. No reciprocity assertion is supplied as an input. -/
namespace Dubon2026.SourceCurve
noncomputable section
open scoped Classical BigOperators
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (hres : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))

theorem rationalDivisorEval_zero (f : F) : rationalDivisorEval hres f 0 = 1 :=
  Finsupp.prod_zero_index

theorem rationalDivisorEval_constant_degree_zero (c : K) (hc : c ≠ 0)
    (D : Divisor K F) (hD : Divisor.degree D = 0) :
    rationalDivisorEval hres (algebraMap K F c) D = 1 := by
  have hs : ∑ v ∈ D.support, D v = 0 := by
    rw [Divisor.degree_eq_sum_support] at hD
    have hr (v : Place K F) : Module.finrank K v.ResidueField = 1 :=
      Module.finrank_of_bijective_algebraMap (hres v)
    simpa only [hr, Nat.cast_one, mul_one] using hD
  have hp : (∏ v ∈ D.support, c ^ D v) = c ^ (∑ v ∈ D.support, D v) := by
    induction D.support using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]
  change (∏ v ∈ D.support, v.rationalEval (hres v) (algebraMap K F c) ^ D v) = 1
  simp_rw [Place.rationalEval_algebraMap]
  rw [hp, hs, zpow_zero]

end
end Dubon2026.SourceCurve
