import Dubon2026.RepresentationCoordinateEvaluation

/-! # The actual point ideal and residue algebra of an original matrix representation -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The actual coordinate evaluation at the original representation over the base ring is surjective because it fixes all original scalars. -/
theorem representationCoordinateEvaluation_surjective (ρ : G →* GeneralLinearGroup ι R) :
    Function.Surjective (representationCoordinateEvaluation (R := R) ρ) := by
  intro r
  refine ⟨algebraMap R (RepresentationCoordinateAlgebra G ι R) r, ?_⟩
  exact (representationCoordinateEvaluation (R := R) ρ).commutes r

/-- The literal kernel of evaluation at the original representation point. -/
def representationCoordinatePointIdeal (ρ : G →* GeneralLinearGroup ι R) :
    Ideal (RepresentationCoordinateAlgebra G ι R) :=
  RingHom.ker (representationCoordinateEvaluation (R := R) ρ).toRingHom

/-- The actual coordinate quotient by the original point ideal is the original coefficient algebra. -/
def representationCoordinatePointQuotientEquiv (ρ : G →* GeneralLinearGroup ι R) :
    (RepresentationCoordinateAlgebra G ι R ⧸ representationCoordinatePointIdeal ρ) ≃ₐ[R] R :=
  Ideal.quotientKerAlgEquivOfSurjective (representationCoordinateEvaluation_surjective ρ)

/-- The original point quotient identification is literally evaluation of the original coordinate element. -/
theorem representationCoordinatePointQuotientEquiv_mk (ρ : G →* GeneralLinearGroup ι R)
    (x : RepresentationCoordinateAlgebra G ι R) :
    representationCoordinatePointQuotientEquiv ρ
      (Ideal.Quotient.mk (representationCoordinatePointIdeal ρ) x) =
        representationCoordinateEvaluation (R := R) ρ x := rfl

variable {K : Type*} [Field K]

/-- Over the original coefficient field, the kernel of the original representation point is an actual maximal ideal. -/
theorem representationCoordinatePointIdeal_isMaximal (ρ : G →* GeneralLinearGroup ι K) :
    (representationCoordinatePointIdeal ρ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (representationCoordinateEvaluation (R := K) ρ).toRingHom
    (representationCoordinateEvaluation_surjective ρ)

end
end Dubon2026
