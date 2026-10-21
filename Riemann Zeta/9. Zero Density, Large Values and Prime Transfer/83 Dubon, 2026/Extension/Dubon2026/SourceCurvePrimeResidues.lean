import Dubon2026.SourceCurvePrimePlaces
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! DUB-17/18 -> principal-divisor degree zero -> actual prime/place
comparison. Pinned localization preserves the residue field. This identifies
the literal chart quotient with the actual place residue, including its base
scalar structure; no residue-degree comparison is assumed.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain IsLocalRing
open IsDedekindDomain.HeightOneSpectrum

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable [Algebra K R] [IsScalarTower K R F]

/-- Identity on field elements between the actual prime localization and prime place ring. -/
def primeLocalizationRingEquiv (P : HeightOneSpectrum R) :
    valuationSubringAtPrime F P ≃+* (ofHeightOneSpectrum (K := K) (F := F) P).toValuationSubring :=
  RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
    (valuationSubringAtPrime_eq_valuationSubring (K := F) P))

/-- Pinned localization identifies the chart quotient with the actual place residue over the base. -/
def primeResidueEquiv (P : HeightOneSpectrum R) :
    (R ⧸ P.asIdeal) ≃ₐ[K] (ofHeightOneSpectrum (K := K) (F := F) P).ResidueField := by
  haveI : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  refine AlgEquiv.ofRingEquiv (f :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal (valuationSubringAtPrime F P)).trans
      (IsLocalRing.ResidueField.mapEquiv (primeLocalizationRingEquiv (K := K) (F := F) P))) ?_
  intro a
  rw [show algebraMap K (R ⧸ P.asIdeal) a =
    Ideal.Quotient.mk P.asIdeal (algebraMap K R a) from rfl]
  rw [RingEquiv.trans_apply, IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
  letI : IsLocalHom (primeLocalizationRingEquiv (K := K) (F := F) P).toRingHom :=
    ⟨fun x hx => by
      have h := hx.map (primeLocalizationRingEquiv (K := K) (F := F) P).symm.toRingHom
      simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply] using h⟩
  change IsLocalRing.ResidueField.map
    (primeLocalizationRingEquiv (K := K) (F := F) P).toRingHom
    (IsLocalRing.residue _ (algebraMap R (valuationSubringAtPrime F P) (algebraMap K R a))) = _
  rw [IsLocalRing.ResidueField.map_residue]
  apply congrArg (IsLocalRing.residue _)
  apply Subtype.ext
  change algebraMap R F (algebraMap K R a) = algebraMap K F a
  exact (IsScalarTower.algebraMap_apply K R F a).symm

theorem finrank_primeResidue (P : HeightOneSpectrum R) :
    Module.finrank K (ofHeightOneSpectrum (K := K) (F := F) P).ResidueField =
      Module.finrank K (R ⧸ P.asIdeal) :=
  (primeResidueEquiv (K := K) (F := F) P).toLinearEquiv.finrank_eq.symm

end
end Dubon2026.SourceCurve.Place
