import Dubon2026.SourceCurveFiniteValuePlace
import Dubon2026.SourceCurveClosedConstantResidue
import Dubon2026.SourceRatFuncGaloisCoordinate

/-! An actual place over every prescribed value in a finite Galois
rational-function extension, together with its actual residue-field
identification and inertia group. These are the local inputs for the
faithful torsion model and exceptional-fiber count needed by DUB-17/18
through reverse genus and good reduction. No place-existence or residue-
rationality assumption is supplied. -/
namespace Dubon2026.SourceCurve
open IntermediateField IsLocalRing
noncomputable section

theorem exists_rational_specialization_place
    (K : Type*) [Field K] [IsAlgClosed K] {M : Type*} [Field M]
    [Algebra (RatFunc K) M] [Algebra K M] [IsScalarTower K (RatFunc K) M]
    [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M] (a : K) :
    ∃ (v : Place K M)
      (htv : algebraMap (RatFunc K) M RatFunc.X ∈ v.toValuationSubring),
      0 < v.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a) ∧
      ∃ e : v.ResidueField ≃ₐ[K] K,
        (∀ c : K, (e.toRingHom.comp (residue v.toValuationSubring))
          (algebraMap K v.toValuationSubring c) = c) ∧
        e (residue v.toValuationSubring ⟨algebraMap (RatFunc K) M RatFunc.X, htv⟩) = a ∧
        ∀ (σ : M ≃ₐ[RatFunc K] M) (hσ : σ ∈ v.toValuationSubring.decompositionSubgroup (RatFunc K)),
          (⟨σ, hσ⟩ : v.toValuationSubring.decompositionSubgroup (RatFunc K)) ∈
            v.toValuationSubring.inertiaSubgroup (RatFunc K) := by
  let t := algebraMap (RatFunc K) M RatFunc.X
  have ht : Transcendental K t := rationalCoordinate_transcendental K
  obtain ⟨hfd, hgal⟩ := finite_galois_coordinateField K (M := M)
  haveI := hfd
  haveI := hgal
  obtain ⟨v, hv⟩ := exists_place_over_finite_value t ht a
  have htv : t ∈ v.toValuationSubring := by
    have h := add_mem (v.mem_of_ord_nonneg (le_of_lt hv)) (v.algebraMap_mem' a)
    simpa only [sub_add_cancel] using h
  refine ⟨v, htv, hv, Place.residueConstantEquiv t v, ?_, ?_, ?_⟩
  · exact Place.residueConstantMap_algebraMap t v
  · exact Place.residueConstantMap_coordinate t v ht htv a hv
  · exact fun σ hσ => Place.mem_inertia_of_decomposition_of_finite_coordinate t v hσ

end
end Dubon2026.SourceCurve
