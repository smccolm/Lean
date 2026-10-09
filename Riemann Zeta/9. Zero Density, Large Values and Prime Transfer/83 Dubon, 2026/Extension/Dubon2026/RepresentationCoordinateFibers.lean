import Dubon2026.RepresentationCoordinateEquivalence

/-! # Actual coefficient-reduction fibers of the original representation coordinate algebra -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R A B : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Changing coefficients in the original coordinate map changes the entire induced representation by that same map. -/
theorem representationFromCoordinates_comp
    (f : RepresentationCoordinateAlgebra G ι R →ₐ[R] A) (π : A →ₐ[R] B) :
    representationFromCoordinates (π.comp f) =
      (GeneralLinearGroup.map π.toRingHom).comp (representationFromCoordinates f) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  rfl

/-- The actual coefficient-reduction condition on a coordinate map is equivalent to the original representation reduction condition. -/
theorem representationCoordinateFiber_iff
    (ρ : G →* GeneralLinearGroup ι B) (π : A →ₐ[R] B)
    (f : RepresentationCoordinateAlgebra G ι R →ₐ[R] A) :
    (GeneralLinearGroup.map π.toRingHom).comp (representationFromCoordinates f) = ρ ↔
      π.comp f = representationCoordinateEvaluation (R := R) ρ := by
  rw [← representationFromCoordinates_comp]
  constructor
  · intro h
    have he := congrArg (representationCoordinateEvaluation (R := R)) h
    rw [representationCoordinateEvaluation_fromCoordinates] at he
    exact he
  · intro h
    rw [h, representationFromCoordinates_evaluation]

/-- The literal fiber of original matrix representations under the actual coefficient-reduction map. -/
abbrev MatrixRepresentationFiber (ρ : G →* GeneralLinearGroup ι B) (π : A →ₐ[R] B) :=
  {τ : G →* GeneralLinearGroup ι A // (GeneralLinearGroup.map π.toRingHom).comp τ = ρ}

/-- The literal fiber of algebra maps from the original coordinate algebra over the original representation point. -/
abbrev RepresentationCoordinateFiber (ρ : G →* GeneralLinearGroup ι B) (π : A →ₐ[R] B) :=
  {f : RepresentationCoordinateAlgebra G ι R →ₐ[R] A //
    π.comp f = representationCoordinateEvaluation (R := R) ρ}

/-- The actual coordinate algebra represents the full original coefficient-reduction fiber, with both inverse maps inherited from the proved evaluation equivalence. -/
def representationCoordinateFiberEquiv (ρ : G →* GeneralLinearGroup ι B)
    (π : A →ₐ[R] B) : RepresentationCoordinateFiber ρ π ≃ MatrixRepresentationFiber ρ π where
  toFun f := ⟨representationFromCoordinates f.val,
    (representationCoordinateFiber_iff ρ π f.val).mpr f.property⟩
  invFun τ := ⟨representationCoordinateEvaluation (R := R) τ.val, by
    rw [← representationCoordinateEvaluation_natural, τ.property]⟩
  left_inv f := Subtype.ext (representationCoordinateEvaluation_fromCoordinates f.val)
  right_inv τ := Subtype.ext (representationFromCoordinates_evaluation τ.val)

/-- The full original representation in the coordinate-fiber equivalence is literally obtained by evaluating the original universal matrices. -/
theorem representationCoordinateFiberEquiv_apply (ρ : G →* GeneralLinearGroup ι B)
    (π : A →ₐ[R] B) (f : RepresentationCoordinateFiber ρ π) :
    (representationCoordinateFiberEquiv ρ π f).val =
      (GeneralLinearGroup.map f.val.toRingHom).comp (universalMatrixRepresentation G ι R) := rfl

end
end Dubon2026
