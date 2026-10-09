import Dubon2026.ResidualRepresentationCoordinates
import Dubon2026.RepresentationCoordinateFiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule

/-! # Localization at the actual original residual representation point -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- The literal original residual representation point is prime because its actual evaluation has field quotient. -/
instance residualRepresentationCoordinateIdeal_isPrime
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (residualRepresentationCoordinateIdeal ρ).IsPrime :=
  (residualRepresentationCoordinateIdeal_isMaximal ρ).isPrime

/-- The actual localization of the original coordinate algebra at its original residual point. -/
abbrev ResidualRepresentationLocalRing
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :=
  Localization.AtPrime (residualRepresentationCoordinateIdeal ρ)

/-- The original residual representation localization is a genuine local ring. -/
theorem residualRepresentationLocalRing_isLocalRing
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    IsLocalRing (ResidualRepresentationLocalRing ρ) := inferInstance

/-- For an abstract finitely generated original group and Noetherian local coefficient ring, the actual residual localization is Noetherian. -/
theorem residualRepresentationLocalRing_isNoetherian [Group.FG G] [IsNoetherianRing O]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    IsNoetherianRing (ResidualRepresentationLocalRing ρ) := by
  letI := representationCoordinateAlgebra_isNoetherian_of_fg (G := G) (ι := ι) (R := O)
  infer_instance

/-- The genuine original universal matrix representation with coefficients in its actual residual localization. -/
def localizedUniversalMatrixRepresentation
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    G →* GeneralLinearGroup ι (ResidualRepresentationLocalRing ρ) := by
  let coefficientMap : RepresentationCoordinateAlgebra G ι O →+*
      ResidualRepresentationLocalRing ρ := algebraMap _ _
  let matrixMap : GeneralLinearGroup ι (RepresentationCoordinateAlgebra G ι O) →*
      GeneralLinearGroup ι (ResidualRepresentationLocalRing ρ) :=
    GeneralLinearGroup.map (n := ι) (R := RepresentationCoordinateAlgebra G ι O)
      (S := ResidualRepresentationLocalRing ρ) coefficientMap
  exact matrixMap.comp (universalMatrixRepresentation G ι O)

/-- The actual maximal ideal of the original residual localization pulls back to precisely the original residual representation point. -/
theorem residualRepresentationLocalRing_comap_maximal
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Ideal.comap (algebraMap (RepresentationCoordinateAlgebra G ι O)
      (ResidualRepresentationLocalRing ρ))
        (IsLocalRing.maximalIdeal (ResidualRepresentationLocalRing ρ)) =
      residualRepresentationCoordinateIdeal ρ :=
  IsLocalization.AtPrime.under_maximalIdeal _ _

end
end Dubon2026
