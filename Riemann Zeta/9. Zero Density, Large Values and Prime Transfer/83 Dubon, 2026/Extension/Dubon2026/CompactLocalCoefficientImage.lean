import Dubon2026.CompactAdicQuotients
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! The original topology on a continuous image of compact local
coefficients is its own maximal-adic topology. This transfers completeness
to the actual CM trace algebra from the existing universal trace ring. -/

namespace Dubon2026
open Filter Set Topology
noncomputable section

variable {R A : Type*} [CommRing R] [IsLocalRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]

/-- A continuous surjective map from compact local coefficients preserves
the literal maximal-adic topology on the original target. -/
theorem compactLocalCoefficientImage_isAdic
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (f : R →+* A) (hf : Continuous f) (hs : Function.Surjective f) :
    IsAdic (IsLocalRing.maximalIdeal A) := by
  have hq : IsQuotientMap f := hf.isClosedMap.isQuotientMap hf hs
  have ho : IsOpenMap f := (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap hq).isOpenMap
  have himage (n : ℕ) :
      ((IsLocalRing.maximalIdeal A ^ n : Ideal A) : Set A) =
        f '' ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective f hs, ← Ideal.map_pow]
    ext x
    exact Ideal.mem_map_iff_of_surjective f hs
  apply isAdic_iff.mpr
  constructor
  · intro n
    rw [himage]
    exact ho _ ((isAdic_iff.mp hR).1 n)
  · intro U hU
    have hpre : f ⁻¹' U ∈ 𝓝 (0 : R) := by
      exact hf.continuousAt.preimage_mem_nhds (by simpa only [map_zero] using hU)
    obtain ⟨n, hn⟩ := (isAdic_iff.mp hR).2 _ hpre
    refine ⟨n, ?_⟩
    rw [himage]
    exact Set.image_subset_iff.mpr hn

/-- The same original target is complete for its own maximal ideal;
compactness is supplied by the actual surjective coefficient map. -/
theorem compactLocalCoefficientImage_isAdicComplete
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (f : R →+* A) (hf : Continuous f) (hs : Function.Surjective f) :
    IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
  letI : CompactSpace A := ⟨by
    simpa only [Set.image_univ, hs.range_eq] using isCompact_univ.image hf⟩
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  exact (IsAdic.isAdicComplete_iff (compactLocalCoefficientImage_isAdic hR f hf hs)).mpr
    ⟨inferInstance, inferInstance⟩

end
end Dubon2026
