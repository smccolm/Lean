import Dubon2026.CoefficientRetractionAdicTopology

/-! # Actual coefficient retraction completeness in the proved original adic topology -/

namespace Dubon2026
noncomputable section

variable {O R : Type*} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
  [t : TopologicalSpace R] [IsTopologicalRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- A genuine local retraction onto an original closed coefficient subalgebra gives its own actual maximal-adic topology and completeness while preserving the original ambient topology by explicit equality transport. -/
theorem originalAdicCoefficientRetraction_localTopology
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom]
    (hS : IsClosed (S : Set R))
    (f : R →ₐ[O] S) (hfix : ∀ x : S, f x = x) :
    IsAdic (IsLocalRing.maximalIdeal S) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  refine ⟨coefficientRetraction_isAdic hR S f hfix, ?_⟩
  change t = (IsLocalRing.maximalIdeal R).adicTopology at hR
  subst t
  letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  exact coefficientRetraction_isAdicComplete rfl S hS f hfix

end
end Dubon2026
