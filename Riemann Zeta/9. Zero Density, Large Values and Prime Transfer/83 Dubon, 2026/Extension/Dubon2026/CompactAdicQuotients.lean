import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.RingTheory.AdicCompletion.Topology

/-! # Genuine adic topology and completeness of compact Noetherian ring quotients -/

namespace Dubon2026

noncomputable section
open Filter Set
open scoped Topology

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The genuine quotient topology of an original adic ring is adic for the image of the original ideal. -/
theorem adicQuotient_isAdic (I J : Ideal R) (hI : IsAdic I) :
    IsAdic (I.map (Ideal.Quotient.mk J)) := by
  have himage (n : ℕ) :
      ((I.map (Ideal.Quotient.mk J) ^ n : Ideal (R ⧸ J)) : Set (R ⧸ J)) =
        Ideal.Quotient.mk J '' ((I ^ n : Ideal R) : Set R) := by
    rw [← Ideal.map_pow]
    ext x
    exact Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J)
      (Ideal.Quotient.mk_surjective) 
  apply isAdic_iff.mpr
  constructor
  · intro n
    rw [himage]
    exact QuotientRing.isOpenMap_coe J _ ((isAdic_iff.mp hI).1 n)
  · intro U hU
    have hpre : Ideal.Quotient.mk J ⁻¹' U ∈ 𝓝 (0 : R) := by
      simpa only [map_zero] using
        (QuotientRing.isOpenQuotientMap_mk J).continuous.continuousAt.preimage_mem_nhds hU
    obtain ⟨n, hn⟩ := (isAdic_iff.mp hI).2 _ hpre
    refine ⟨n, ?_⟩
    rw [himage]
    exact Set.image_subset_iff.mpr hn

/-- Every actual ideal quotient of a compact Hausdorff Noetherian ring is Hausdorff in its genuine quotient topology. -/
theorem compactNoetherianQuotient_t2Space
    [CompactSpace R] [T2Space R] [IsNoetherianRing R] (J : Ideal R) :
    T2Space (R ⧸ J) := by
  letI : IsClosed (J.toAddSubgroup : Set R) := IsNoetherianRing.isClosed_ideal J
  exact inferInstanceAs (T2Space (R ⧸ J.toAddSubgroup))

/-- The genuine quotient by any original ideal remains complete and separated for the image adic ideal. -/
theorem compactNoetherianAdicQuotient_complete
    [CompactSpace R] [T2Space R] [IsNoetherianRing R]
    (I J : Ideal R) (hI : IsAdic I) :
    IsAdicComplete (I.map (Ideal.Quotient.mk J)) (R ⧸ J) := by
  letI : T2Space (R ⧸ J) := compactNoetherianQuotient_t2Space J
  letI : UniformSpace (R ⧸ J) := IsTopologicalAddGroup.rightUniformSpace (R ⧸ J)
  letI : IsUniformAddGroup (R ⧸ J) := isUniformAddGroup_of_addCommGroup
  exact (IsAdic.isAdicComplete_iff (adicQuotient_isAdic I J hI)).mpr
    ⟨inferInstance, inferInstance⟩

end
end Dubon2026
