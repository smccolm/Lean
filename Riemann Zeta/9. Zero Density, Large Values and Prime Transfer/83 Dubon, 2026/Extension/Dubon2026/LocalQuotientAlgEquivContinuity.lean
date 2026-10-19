import Dubon2026.LocalQuotientAdicTopology
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Dubon2026.AuxiliaryFamilyAugmentationRepresentation

/-! The actual augmentation isomorphism is automatically continuous:
ring isomorphisms preserve maximal ideals, and the original quotient
topology is already proved maximal-adic. This avoids reconstructing
the intervening inertia-quotient map just to prove continuity. -/

namespace Dubon2026
noncomputable section
open IsLocalRing Matrix

/-- A ring isomorphism between the original maximal-adic topologies
is continuous, by the native ideal-map criterion. -/
theorem maximalAdic_ringEquiv_continuous
    {R A : Type*} [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    (hR : (inferInstance : TopologicalSpace R) = (maximalIdeal R).adicTopology)
    (hA : (inferInstance : TopologicalSpace A) = (maximalIdeal A).adicTopology)
    (e : R ≃+* A) : Continuous e := by
  have h : @Continuous R A (maximalIdeal R).adicTopology (maximalIdeal A).adicTopology e := by
    letI : WithIdeal R := ⟨maximalIdeal R⟩
    letI : WithIdeal A := ⟨maximalIdeal A⟩
    exact (WithIdeal.uniformContinuous_of_map_le (f := e.toRingHom)
      (map_maximalIdeal_of_surjective e.toRingHom e.surjective).le).continuous
  rw [← hR, ← hA] at h
  exact h

/-- An algebra isomorphism from the actual local quotient retains
both original topologies. Locality of the quotient is derived from
the displayed isomorphism with the local target ring. -/
theorem localQuotientAlgEquiv_continuous_both
    {O R A : Type*} [CommRing O]
    [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
    (J : Ideal R)
    (hR : (inferInstance : TopologicalSpace R) = (maximalIdeal R).adicTopology)
    (hA : (inferInstance : TopologicalSpace A) = (maximalIdeal A).adicTopology)
    (e : (R ⧸ J) ≃ₐ[O] A) : Continuous e ∧ Continuous e.symm := by
  letI : IsLocalRing (R ⧸ J) := e.symm.toRingEquiv.isLocalRing
  have hQ := localQuotient_maximal_adicTopology J hR
  exact ⟨maximalAdic_ringEquiv_continuous hQ hA e.toRingEquiv,
    maximalAdic_ringEquiv_continuous hA hQ e.symm.toRingEquiv⟩

/-- Upgrade the already constructed augmentation comparison without
changing its characters, algebra isomorphism or universal matrices. -/
def auxiliaryFamilyAugmentationTopologicalComparisonOfAdic
    (O : Type*) [CommRing O] {S ι n G R A : Type*}
    [Fintype S] [Fintype ι] [Fintype n] [DecidableEq n]
    [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
    (D : S → Type*) [∀ s, Group (D s)]
    (τ : G → GeneralLinearGroup n R) (τ₀ : G → GeneralLinearGroup n A)
    (hR : (inferInstance : TopologicalSpace R) = (maximalIdeal R).adicTopology)
    (hA : (inferInstance : TopologicalSpace A) = (maximalIdeal A).adicTopology)
    (c : AuxiliaryFamilyAugmentationRepresentationComparison O (ι := ι) D τ τ₀) :
    {d : AuxiliaryFamilyAugmentationRepresentationComparison O (ι := ι) D τ τ₀ //
      Continuous d.equiv ∧ Continuous d.equiv.symm} :=
  ⟨c, localQuotientAlgEquiv_continuous_both
    (auxiliaryFamilyAugmentationIdeal O c.characters) hR hA c.equiv⟩

end
end Dubon2026
