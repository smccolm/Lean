import Dubon2026.SourceCurveRationalNormEvaluation
import Mathlib.Algebra.BigOperators.Finprod

/-! DUB-17/18 -> Weil reciprocity and Hecke adjointness -> evaluation
of norms. Reindex the proved ramified-factor calculation over the actual
place fiber, using the already proved prime/place equivalence and normalized
ramification order. This is the fiber formula needed by divisor pullback. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain IsLocalRing UniqueFactorizationMonoid
open scoped Classical
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem rationalRegularEval_norm_eq_finprod_fiber (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (c : integralClosureAt E v) :
    v.rationalRegularEval hbase (Algebra.norm v.toValuationSubring c) =
      ∏ᶠ w : {w : Place K E // w.restrict F = v},
        (w.val.rationalRegularEval (htop w.val)
          ⟨algebraMap (integralClosureAt E v) E c,
            integralClosureAt_mem_of_restrict_eq w.property c⟩) ^
          (w.val.ord (algebraMap F E v.uniformizer)).toNat := by
  let e := (fiberPrimeEquiv E v).trans (fiberPrimeFinsetEquiv E v)
  let f : {w : Place K E // w.restrict F = v} → K := fun w =>
    (w.val.rationalRegularEval (htop w.val)
      ⟨algebraMap (integralClosureAt E v) E c,
        integralClosureAt_mem_of_restrict_eq w.property c⟩) ^
      (w.val.ord (algebraMap F E v.uniformizer)).toNat
  rw [rationalRegularEval_norm_eq_prod_factors v hbase htop]
  change _ = ∏ᶠ w, f w
  calc
    _ = ∏ᶠ P, f (e.symm P) := by
      rw [finprod_eq_prod_of_fintype]
      apply Finset.prod_congr rfl
      intro P _
      change _ = _ ^ ((fiberPrimePlace E v ((fiberPrimeFinsetEquiv E v).symm P)).ord
        (algebraMap F E v.uniformizer)).toNat
      rw [fiberPrime_order_eq_ramificationIdx, Int.toNat_natCast]
      rfl
    _ = _ := finprod_comp_equiv e.symm

end
end Dubon2026.SourceCurve.Place
