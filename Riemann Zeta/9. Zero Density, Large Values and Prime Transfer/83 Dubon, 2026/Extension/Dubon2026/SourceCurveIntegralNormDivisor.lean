import Dubon2026.SourceCurvePrimeNormOrders

/-! DUB-17/18 -> original Picard Hecke correspondence -> pushforward of
principal divisors. Native finite prime factorization and the proved
prime norms give the exact norm/order sum for functions integral at the
base place. The fraction-field step for arbitrary functions follows next.
This uses the actual integral closure and its original prime places.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain IsLocalRing
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E] [CharZero F]

omit [CharZero F] in
private theorem finite_integralClosureAt_primes (v : Place K F) :
    Finite (HeightOneSpectrum (integralClosureAt E v)) :=
  Finite.of_equiv _ (fiberPrimeFinsetEquiv E v).symm

theorem relNorm_span_eq_maximal_pow_sum (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {c : integralClosureAt E v} (hc : c ≠ 0) :
    Ideal.relNorm v.toValuationSubring (Ideal.span {c}) =
      maximalIdeal v.toValuationSubring ^
        (∑ᶠ P : HeightOneSpectrum (integralClosureAt E v),
          ((fiberPrimePlace E v P).ord (algebraMap (integralClosureAt E v) E c)).toNat) := by
  classical
  haveI := finite_integralClosureAt_primes (E := E) v
  letI := Fintype.ofFinite (HeightOneSpectrum (integralClosureAt E v))
  have hspan : (Ideal.span {c} : Ideal (integralClosureAt E v)) ≠ ⊥ := by simpa using hc
  have hf := Ideal.finprod_heightOneSpectrum_pow_multiplicity hspan
  rw [finprod_eq_prod_of_fintype] at hf
  calc
    _ = Ideal.relNorm v.toValuationSubring
        (∏ P : HeightOneSpectrum (integralClosureAt E v),
          P.asIdeal ^ multiplicity P.asIdeal (Ideal.span {c})) := congrArg _ hf.symm
    _ = ∏ P : HeightOneSpectrum (integralClosureAt E v),
        maximalIdeal v.toValuationSubring ^ multiplicity P.asIdeal (Ideal.span {c}) := by
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro P _
      rw [map_pow, relNorm_fiberPrime_eq_maximal v hbase htop P]
    _ = maximalIdeal v.toValuationSubring ^
        (∑ P : HeightOneSpectrum (integralClosureAt E v),
          multiplicity P.asIdeal (Ideal.span {c})) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = _ := by
      rw [finsum_eq_sum_of_fintype]
      congr 1
      apply Finset.sum_congr rfl
      intro P _
      rw [← HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hspan,
        fiberPrime_count_eq_order v P hc]

theorem ord_norm_integralClosureAt (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {c : integralClosureAt E v} (hc : c ≠ 0) :
    v.ord (Algebra.norm F (algebraMap (integralClosureAt E v) E c)) =
      ∑ᶠ P : HeightOneSpectrum (integralClosureAt E v),
        (fiberPrimePlace E v P).ord (algebraMap (integralClosureAt E v) E c) := by
  classical
  haveI := finite_integralClosureAt_primes (E := E) v
  letI := Fintype.ofFinite (HeightOneSpectrum (integralClosureAt E v))
  rw [← Algebra.algebraMap_intNorm (A := v.toValuationSubring) (K := F) (L := E)
    (B := integralClosureAt E v)]
  have hrel := relNorm_span_eq_maximal_pow_sum v hbase htop hc
  rw [Ideal.relNorm_singleton] at hrel
  rw [ValuationSubring.algebraMap_apply, ord_coe_of_span_eq_maximal_pow v hrel]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  push_cast
  apply Finset.sum_congr rfl
  intro P _
  exact Int.toNat_of_nonneg ((fiberPrimePlace E v P).ord_nonneg_of_mem
    (integralClosureAt_mem_of_restrict_eq (restrict_fiberPrimePlace v P) c))

end
end Dubon2026.SourceCurve.Place
