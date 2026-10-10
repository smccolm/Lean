import Dubon2026.SurjectiveLocalResidue
import Dubon2026.CompactAdicQuotients

/-! # Actual maximal-adic completeness and original residues of local coefficient quotients -/

namespace Dubon2026

noncomputable section

variable {O R : Type*} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- The genuine coefficient quotient induces the actual equivalence from the original residue algebra. -/
def localQuotientResidueAlgEquiv (J : Ideal R) [IsLocalRing (R ⧸ J)] :
    IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField (R ⧸ J) := by
  let q := Ideal.Quotient.mkₐ O J
  letI : IsLocalHom q.toRingHom :=
    IsLocalHom.of_surjective q.toRingHom Ideal.Quotient.mk_surjective
  exact surjectiveLocalResidueAlgEquiv q Ideal.Quotient.mk_surjective

/-- The original quotient residue equivalence agrees with literal coefficient reduction. -/
theorem localQuotientResidueAlgEquiv_residue (J : Ideal R)
    [IsLocalRing (R ⧸ J)] (r : R) :
    localQuotientResidueAlgEquiv (O := O) J (IsLocalRing.residue R r) =
      IsLocalRing.residue (R ⧸ J) (Ideal.Quotient.mk J r) := rfl

/-- An actual local quotient of original compact Noetherian maximal-adic coefficients is complete for its own genuine maximal ideal. -/
theorem compactLocalAdicQuotient_maximal_complete
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    [IsNoetherianRing R] (J : Ideal R) [IsLocalRing (R ⧸ J)]
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) :
    IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ J)) (R ⧸ J) := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective]
  exact compactNoetherianAdicQuotient_complete (IsLocalRing.maximalIdeal R) J hR

end
end Dubon2026
