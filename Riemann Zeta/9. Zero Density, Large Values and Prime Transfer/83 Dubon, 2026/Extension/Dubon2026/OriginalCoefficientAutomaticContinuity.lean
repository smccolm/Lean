import Dubon2026.LocalCoefficientReduction
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-! # Automatic original adic continuity of genuine residue-preserving coefficient maps -/

namespace Dubon2026

noncomputable section

variable {O R A : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]
  [CommRing A] [IsLocalRing A] [Algebra O A]

/-- A genuine residue-preserving original coefficient map sends the actual source maximal ideal into the actual target maximal ideal. -/
theorem originalCoefficientMap_maximalIdeal_le
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : R →ₐ[O] A)
    (hres : (localCoefficientReduction eA).comp f = localCoefficientReduction eR) :
    (IsLocalRing.maximalIdeal R).map f.toRingHom ≤ IsLocalRing.maximalIdeal A := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  apply (localCoefficientReduction_eq_zero_iff eA (f r)).mp
  exact (DFunLike.congr_fun hres r).trans ((localCoefficientReduction_eq_zero_iff eR r).mpr hr)

/-- A genuine residue-preserving coefficient map is automatically continuous for the original maximal-adic topologies. -/
theorem originalCoefficientMap_continuous [WithIdeal R] [WithIdeal A]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : R →ₐ[O] A)
    (hres : (localCoefficientReduction eA).comp f = localCoefficientReduction eR) :
    Continuous f := by
  apply (WithIdeal.uniformContinuous_of_map_le (f := f.toRingHom) ?_).continuous
  rw [hR, hA]
  exact originalCoefficientMap_maximalIdeal_le eR eA f hres

/-- Automatic continuity is valid in the original coefficient topologies whenever those actual topologies are proved maximal-adic. -/
theorem originalCoefficientMap_continuous_of_topology_eq
    [TopologicalSpace R] [TopologicalSpace A]
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (hA : (inferInstance : TopologicalSpace A) = (IsLocalRing.maximalIdeal A).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : R →ₐ[O] A)
    (hres : (localCoefficientReduction eA).comp f = localCoefficientReduction eR) :
    Continuous f := by
  have h : @Continuous R A (IsLocalRing.maximalIdeal R).adicTopology
      (IsLocalRing.maximalIdeal A).adicTopology f := by
    letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
    letI : WithIdeal A := ⟨IsLocalRing.maximalIdeal A⟩
    exact originalCoefficientMap_continuous rfl rfl eR eA f hres
  rw [← hR, ← hA] at h
  exact h

end
end Dubon2026
