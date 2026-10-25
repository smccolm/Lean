import Dubon2026.SourceCurveResidueNormFactors
import Dubon2026.SourceCurveRationalEvaluation
import Dubon2026.SourceCurveFiberDegrees

/-! DUB-17/18 -> original Frobenius determinant -> Weil reciprocity and
Hecke adjointness -> norm evaluation. Identify every ramified factor with
the existing actual prime place. Rational residue fields discharge its
inertia degree and determine its scalar residue; no norm-evaluation identity
or prime/place comparison is assumed. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain IsLocalRing UniqueFactorizationMonoid
open scoped Classical
attribute [local instance] residueRamifiedFactorAlgebra
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem rationalRegularEval_norm_eq_prod_factors (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (c : integralClosureAt E v) :
    v.rationalRegularEval hbase (Algebra.norm v.toValuationSubring c) =
      ∏ P : (factors (residueFiberIdeal E v)).toFinset,
        let H := (fiberPrimeFinsetEquiv E v).symm P
        let w := fiberPrimePlace E v H
        (w.rationalRegularEval (htop w)
          ⟨algebraMap (integralClosureAt E v) E c,
            integralClosureAt_mem_of_restrict_eq (restrict_fiberPrimePlace v H) c⟩) ^
          (maximalIdeal v.toValuationSubring).ramificationIdx P.val := by
  apply hbase.injective
  rw [residue_rationalRegularEval, residue_norm_eq_prod_ramified_factors, map_prod]
  apply Finset.prod_congr rfl
  intro P _
  let H := (fiberPrimeFinsetEquiv E v).symm P
  let w := fiberPrimePlace E v H
  let a := w.rationalRegularEval (htop w)
    ⟨algebraMap (integralClosureAt E v) E c,
      integralClosureAt_mem_of_restrict_eq (restrict_fiberPrimePlace v H) c⟩
  have hr : c - algebraMap v.toValuationSubring (integralClosureAt E v)
      (algebraMap K v.toValuationSubring a) ∈ P.val := by
    change c - algebraMap K (integralClosureAt E v) a ∈ H.asIdeal
    rw [← fiberCenter_fiberPrimePlace v H]
    exact sub_rationalRegularEval_mem_center w (htop w)
      (integralClosureAt_mem_of_restrict_eq (restrict_fiberPrimePlace v H)) c
  have hn := norm_ramified_factor_eq_residue_pow (maximalIdeal v.toValuationSubring)
    P c (algebraMap K v.toValuationSubring a) hr
  have hi : (maximalIdeal v.toValuationSubring).inertiaDeg P.val = 1 :=
    fiberPrime_inertiaDeg_eq_one v hbase H (htop w)
  rw [hi, mul_one] at hn
  rw [map_pow]
  exact hn

end
end Dubon2026.SourceCurve.Place
