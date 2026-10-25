import Dubon2026.SourceCurveRationalEvaluationLaws
import Dubon2026.SourceCurveDivisorDegree
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! DUB-17/18 -> Kummer detecting class -> actual divisor evaluations.
The specified residue bijections are geometric inputs; the actual cover
consumer supplies them from its proved finite-coordinate geometry. -/
namespace Dubon2026.SourceCurve
noncomputable section
open scoped BigOperators
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (hres : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))

/-- Product of actual rational residue values with the literal divisor multiplicities. -/
def rationalDivisorEval (f : F) (D : Divisor K F) : K :=
  D.prod fun v n => v.rationalEval (hres v) f ^ n

theorem rationalDivisorEval_single (f : F) (v : Place K F) (n : ℤ) :
    rationalDivisorEval hres f (Finsupp.single v n) = v.rationalEval (hres v) f ^ n :=
  Finsupp.prod_single_index (zpow_zero _)

theorem rationalDivisorEval_ne_zero (f : F) (hf : f ≠ 0) (D : Divisor K F)
    (hD : ∀ v ∈ D.support, v.ord f = 0) : rationalDivisorEval hres f D ≠ 0 := by
  classical
  apply Finsupp.prod_ne_zero_iff.mpr
  intro v hv
  exact zpow_ne_zero _ (v.rationalEval_ne_zero_of_ord_eq_zero (hres v) hf (hD v hv))

theorem rationalDivisorEval_mul (f g : F) (D : Divisor K F)
    (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring)
    (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) :
    rationalDivisorEval hres (f * g) D =
      rationalDivisorEval hres f D * rationalDivisorEval hres g D := by
  classical
  simp only [rationalDivisorEval, Finsupp.prod]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v hv => by
    rw [v.rationalEval_mul_of_mem (hres v) (hf v hv) (hg v hv), mul_zpow]

theorem rationalDivisorEval_add (f : F) (D E : Divisor K F)
    (h : ∀ v, v ∈ D.support ∨ v ∈ E.support → v.rationalEval (hres v) f ≠ 0) :
    rationalDivisorEval hres f (D + E) =
      rationalDivisorEval hres f D * rationalDivisorEval hres f E := by
  classical
  exact Finsupp.prod_add_index (fun _ _ => zpow_zero _)
    (fun v hv a b => zpow_add₀ (h v (Finset.mem_union.mp hv)) a b)

theorem rationalDivisorEval_pow (f : F) (D : Divisor K F)
    (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring) (n : ℕ) :
    rationalDivisorEval hres (f ^ n) D = rationalDivisorEval hres f D ^ n := by
  classical
  simp only [rationalDivisorEval, Finsupp.prod]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro v hv
  rw [v.rationalEval_pow_of_mem (hres v) (hf v hv)]
  simpa only [zpow_natCast] using zpow_comm (v.rationalEval (hres v) f) (n : ℤ) (D v)

theorem rationalDivisorEval_nsmul (f : F) (D : Divisor K F) (n : ℕ) :
    rationalDivisorEval hres f (n • D) = rationalDivisorEval hres f D ^ n := by
  classical
  unfold rationalDivisorEval
  rw [Finsupp.prod_of_support_subset (n • D) Finsupp.support_smul _ (fun _ _ => zpow_zero _)]
  change (∏ v ∈ D.support, v.rationalEval (hres v) f ^ ((n • D) v)) = _
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  simp_rw [mul_comm (n : ℤ), zpow_mul, zpow_natCast]
  exact Finset.prod_pow D.support n (fun v => v.rationalEval (hres v) f ^ D v)

end
end Dubon2026.SourceCurve
