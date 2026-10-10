import Dubon2026.OriginalAdicCompleteLocalCompactness
import Dubon2026.LocalAdicQuotientResidue
import Dubon2026.LocalQuotientAdicTopology

/-! # Actual complete local coefficient quotients in their original quotient topology -/

namespace Dubon2026
noncomputable section

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [Finite (IsLocalRing.ResidueField R)] [TopologicalSpace R] [IsTopologicalRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- A genuine local quotient of original complete Noetherian finite-residue coefficients is Noetherian, complete and maximal-adic in its same original quotient topology. -/
theorem originalAdicLocalQuotient_localData
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) (J : Ideal R)
    [IsLocalRing (R ⧸ J)] :
    IsNoetherianRing (R ⧸ J) ∧
      IsAdic (IsLocalRing.maximalIdeal (R ⧸ J)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ J)) (R ⧸ J) := by
  letI : T2Space R := originalAdicCompleteLocal_t2Space hR
  letI : CompactSpace R := originalAdicCompleteLocal_compactSpace hR
  exact ⟨isNoetherianRing_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective, localQuotient_maximal_adicTopology J hR,
    compactLocalAdicQuotient_maximal_complete J hR⟩

end
end Dubon2026
