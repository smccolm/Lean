import Dubon2026.SourceCurveFiberPrimes
import Dubon2026.SourceCurveUniformizerResidue

/-! DUB-17/18 -> original global residue identity -> descent degree.
The normalized place order is the native ramification index. Bijectivity of
the constant maps to the actual residue fields makes the native inertia degree
one; neither comparison is assumed in the subsequent fiber sum.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain IsLocalRing
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem fiberPrime_order_eq_ramificationIdx (v : Place K F)
    (P : HeightOneSpectrum (integralClosureAt E v)) :
    (fiberPrimePlace E v P).ord (algebraMap F E v.uniformizer) =
      ((maximalIdeal v.toValuationSubring).ramificationIdx P.asIdeal : ℤ) := by
  have ha : algebraMap v.toValuationSubring (integralClosureAt E v)
      v.uniformizerSubring ≠ 0 := by
    exact (map_ne_zero_iff _ (algebraMap_integralClosureAt_injective v)).mpr
      v.irreducible_uniformizerSubring.ne_zero
  have h := ord_ofHeightOneSpectrum_eq_ramificationIdx (K := K) (F := E) P ha
  rw [← v.maximalIdeal_eq_span_uniformizer,
    ← IsScalarTower.algebraMap_apply v.toValuationSubring (integralClosureAt E v) E,
    IsScalarTower.algebraMap_apply v.toValuationSubring F E] at h
  exact h

theorem fiberPrime_inertiaDeg_eq_finrank (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (P : HeightOneSpectrum (integralClosureAt E v)) :
    (maximalIdeal v.toValuationSubring).inertiaDeg P.asIdeal =
      Module.finrank K (fiberPrimePlace E v P).ResidueField := by
  haveI := fiberPrime_liesOver v P
  let e : K ≃ₐ[K] (v.toValuationSubring ⧸ maximalIdeal v.toValuationSubring) :=
    AlgEquiv.ofBijective (Algebra.ofId K _) hbase
  rw [show (fiberPrimePlace E v P) = ofHeightOneSpectrum P from rfl,
    finrank_primeResidue, Ideal.inertiaDeg_algebraMap]
  symm
  apply Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv
    (RingEquiv.refl (integralClosureAt E v ⧸ P.asIdeal))
  ext a
  change algebraMap (v.toValuationSubring ⧸ maximalIdeal v.toValuationSubring)
    (integralClosureAt E v ⧸ P.asIdeal) (e a) =
      algebraMap K (integralClosureAt E v ⧸ P.asIdeal) a
  rw [show e a = algebraMap K v.ResidueField a from e.commutes a]
  change algebraMap (v.toValuationSubring ⧸ maximalIdeal v.toValuationSubring)
    (integralClosureAt E v ⧸ P.asIdeal)
    (Ideal.Quotient.mk _ (algebraMap K v.toValuationSubring a)) = _
  exact (IsScalarTower.algebraMap_apply v.toValuationSubring
    (v.toValuationSubring ⧸ maximalIdeal v.toValuationSubring)
    (integralClosureAt E v ⧸ P.asIdeal) (algebraMap K v.toValuationSubring a)).symm.trans
      (IsScalarTower.algebraMap_apply K v.toValuationSubring
        (integralClosureAt E v ⧸ P.asIdeal) a).symm

theorem fiberPrime_inertiaDeg_eq_one (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (P : HeightOneSpectrum (integralClosureAt E v))
    (htop : Function.Bijective (algebraMap K (fiberPrimePlace E v P).ResidueField)) :
    (maximalIdeal v.toValuationSubring).inertiaDeg P.asIdeal = 1 := by
  rw [fiberPrime_inertiaDeg_eq_finrank v hbase P]
  let e := AlgEquiv.ofBijective (Algebra.ofId K (fiberPrimePlace E v P).ResidueField) htop
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

end
end Dubon2026.SourceCurve.Place
