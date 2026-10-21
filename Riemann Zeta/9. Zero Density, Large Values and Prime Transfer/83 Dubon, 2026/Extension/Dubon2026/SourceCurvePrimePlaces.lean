import Dubon2026.SourceCurveChartOrders

/-! DUB-17/18 -> principal-divisor product formula. Actual prime ideals on
the integral-closure chart and actual places containing the chart correspond
in both directions. The normalized orders agree with the original prime
valuation, so pinned prime-factor and norm identities can be transported.
The prime-place construction follows Def_AlgebraicCurve_DivisorClassGroup in
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain WithZero IsLocalRing
open IsDedekindDomain.HeightOneSpectrum

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

theorem isPrincipalIdealRing_valuationSubring (P : HeightOneSpectrum R) :
    IsPrincipalIdealRing ((P.valuation F).valuationSubring) := by
  rw [← valuationSubringAtPrime_eq_valuationSubring]
  infer_instance

variable [Algebra K R] [IsScalarTower K R F]

/-- The actual place given by the prime-adic valuation on a Dedekind chart. -/
def ofHeightOneSpectrum (P : HeightOneSpectrum R) : Place K F where
  toValuationSubring := (P.valuation F).valuationSubring
  algebraMap_mem' a := by
    rw [Valuation.mem_valuationSubring_iff, IsScalarTower.algebraMap_apply K R F]
    exact P.valuation_le_one (algebraMap K R a)
  ne_top' := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' := isPrincipalIdealRing_valuationSubring P

theorem algebraMap_mem_ofHeightOneSpectrum (P : HeightOneSpectrum R) (r : R) :
    algebraMap R F r ∈ (ofHeightOneSpectrum (K := K) (F := F) P).toValuationSubring :=
  P.valuation_le_one r

theorem center_ofHeightOneSpectrum (P : HeightOneSpectrum R) :
    center R (ofHeightOneSpectrum (K := K) (F := F) P)
      (algebraMap_mem_ofHeightOneSpectrum P) = P.asIdeal := by
  ext r
  rw [mem_center_iff]
  change (⟨algebraMap R F r, P.valuation_le_one r⟩ : (P.valuation F).valuationSubring) ∈
      maximalIdeal (P.valuation F).valuationSubring ↔ r ∈ P.asIdeal
  rw [Valuation.mem_maximalIdeal_iff]
  exact P.valuation_lt_one_iff_mem r

theorem centerHeightOneSpectrum_ofHeightOneSpectrum (P : HeightOneSpectrum R) :
    centerHeightOneSpectrum R (ofHeightOneSpectrum (K := K) (F := F) P)
      (algebraMap_mem_ofHeightOneSpectrum P) = P := by
  apply HeightOneSpectrum.ext
  exact center_ofHeightOneSpectrum P

theorem ofHeightOneSpectrum_center (v : Place K F)
    (hR : ∀ r : R, algebraMap R F r ∈ v.toValuationSubring) :
    ofHeightOneSpectrum (centerHeightOneSpectrum R v hR) = v := by
  apply Place.ext
  exact (valuationSubringAtPrime_eq_valuationSubring (K := F) _).symm.trans
    (toValuationSubring_eq_of_forall_mem v hR).symm

theorem ord_ofHeightOneSpectrum (P : HeightOneSpectrum R) {x : F} (hx : x ≠ 0) :
    (ofHeightOneSpectrum (K := K) (F := F) P).ord x = -log (P.valuation F x) := by
  rw [ord_eq_neg_log_center_valuation _ (algebraMap_mem_ofHeightOneSpectrum P) hx,
    centerHeightOneSpectrum_ofHeightOneSpectrum]

end
end Dubon2026.SourceCurve.Place
