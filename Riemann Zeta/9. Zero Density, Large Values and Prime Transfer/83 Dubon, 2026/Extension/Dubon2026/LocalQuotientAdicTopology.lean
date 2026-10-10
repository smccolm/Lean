import Dubon2026.LocalAdicQuotientResidue

/-! # The literal quotient topology equals the original maximal-adic topology -/

namespace Dubon2026

variable {R : Type*} [CommRing R] [IsLocalRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- The actual local coefficient quotient retains exactly its genuine maximal-adic topology. This is equality of topologies on the original quotient, before any coefficient-object instance is installed. -/
theorem localQuotient_maximal_adicTopology
    (J : Ideal R) [IsLocalRing (R ⧸ J)]
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) :
    (inferInstance : TopologicalSpace (R ⧸ J)) =
      (IsLocalRing.maximalIdeal (R ⧸ J)).adicTopology := by
  change IsAdic (IsLocalRing.maximalIdeal (R ⧸ J))
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective]
  exact adicQuotient_isAdic (IsLocalRing.maximalIdeal R) J hR

end Dubon2026
