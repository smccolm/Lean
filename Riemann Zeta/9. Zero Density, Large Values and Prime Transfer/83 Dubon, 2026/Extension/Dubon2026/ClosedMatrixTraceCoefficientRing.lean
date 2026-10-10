import Dubon2026.ClosedCoefficientSubalgebraLocality
import Dubon2026.CoefficientSubalgebraResidue
import Dubon2026.ClosedMatrixTraceAlgebra

/-! # The actual local coefficient ring and true residue of the original closed trace algebra -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R]

/-- The actual closed trace algebra of the whole original representation is local, with its existing original ring operations. -/
theorem closedMatrixTraceAlgebra_isLocalRing
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) :
    IsLocalRing (closedMatrixTraceAlgebra (O := O) ρ) :=
  closedCoefficientSubalgebra_isLocalRing hR eR _ (isClosed_closedMatrixTraceAlgebra ρ)

/-- The actual inclusion of the original closed trace algebra reflects units. -/
theorem closedMatrixTraceAlgebra_isLocalHom
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) :
    IsLocalHom (closedMatrixTraceAlgebra (O := O) ρ).val.toRingHom :=
  closedCoefficientSubalgebra_isLocalHom hR eR _ (isClosed_closedMatrixTraceAlgebra ρ)

/-- The genuine residue field of the actual closed trace coefficient algebra is identified with the original coefficient residue field. -/
def closedMatrixTraceResidueEquiv
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) :
    letI := closedMatrixTraceAlgebra_isLocalRing hR eR ρ
    IsLocalRing.ResidueField (closedMatrixTraceAlgebra (O := O) ρ) ≃ₐ[O]
      IsLocalRing.ResidueField O := by
  letI := closedMatrixTraceAlgebra_isLocalRing hR eR ρ
  letI := closedMatrixTraceAlgebra_isLocalHom hR eR ρ
  exact coefficientSubalgebraResidueEquiv eR (closedMatrixTraceAlgebra (O := O) ρ)

/-- The whole actual reduction on the original closed trace algebra is the restriction of the original ambient coefficient reduction. -/
theorem closedMatrixTraceReduction_eq
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) :
    letI := closedMatrixTraceAlgebra_isLocalRing hR eR ρ
    localCoefficientReduction (closedMatrixTraceResidueEquiv hR eR ρ) =
      (localCoefficientReduction eR).comp (closedMatrixTraceAlgebra (O := O) ρ).val := by
  letI := closedMatrixTraceAlgebra_isLocalRing hR eR ρ
  letI := closedMatrixTraceAlgebra_isLocalHom hR eR ρ
  exact coefficientSubalgebraReduction_eq eR (closedMatrixTraceAlgebra (O := O) ρ)

end
end Dubon2026
