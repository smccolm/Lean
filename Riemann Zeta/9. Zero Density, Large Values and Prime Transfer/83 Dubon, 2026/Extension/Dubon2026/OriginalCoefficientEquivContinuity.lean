import Dubon2026.OriginalCoefficientAutomaticContinuity

/-! The original residue-preserving algebra equivalence is an
isomorphism of the actual adic coefficient topologies in both directions.
This applies the existing automatic-continuity theorem to the inverse
ring maps in the original-support comparison. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

/-- Preserving the genuine residue maps in one direction forces the
inverse identity and continuity in both original maximal-adic topologies. -/
theorem originalCoefficientEquiv_continuous_both
    {O R S : Type*} [CommRing O] [IsLocalRing O]
    [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
    [CommRing S] [IsLocalRing S] [Algebra O S] [TopologicalSpace S]
    (hR : (inferInstance : TopologicalSpace R) = (maximalIdeal R).adicTopology)
    (hS : (inferInstance : TopologicalSpace S) = (maximalIdeal S).adicTopology)
    (eR : ResidueField R ≃ₐ[O] ResidueField O)
    (eS : ResidueField S ≃ₐ[O] ResidueField O)
    (e : S ≃ₐ[O] R)
    (hres : (localCoefficientReduction eR).comp e.toAlgHom = localCoefficientReduction eS) :
    Continuous e ∧ Continuous e.symm := by
  have hi : (localCoefficientReduction eS).comp e.symm.toAlgHom = localCoefficientReduction eR := by
    ext r
    have h := DFunLike.congr_fun hres (e.symm r)
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply] using h.symm
  exact ⟨originalCoefficientMap_continuous_of_topology_eq hS hR eS eR e.toAlgHom hres,
    originalCoefficientMap_continuous_of_topology_eq hR hS eR eS e.symm.toAlgHom hi⟩

end
end Dubon2026
