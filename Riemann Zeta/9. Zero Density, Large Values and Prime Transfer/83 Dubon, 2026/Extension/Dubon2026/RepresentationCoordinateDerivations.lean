import Dubon2026.FirstOrderRepresentationCoordinates
import Dubon2026.DualNumberCoordinateKernel

/-! # Genuine derivations of original representation coordinates and first-order lifts -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original representation point included as the actual constant dual-number coordinate map. -/
def representationCoordinateConstantLift (ρ : G →* GeneralLinearGroup ι R) :
    RepresentationCoordinateAlgebra G ι R →ₐ[R] DualNumber R :=
  (TrivSqZeroExt.inlAlgHom R R R).comp (representationCoordinateEvaluation (R := R) ρ)

/-- The constant coordinate lift has exactly the original coordinate evaluation as its ordinary reduction. -/
theorem representationCoordinateConstantLift_reduction (ρ : G →* GeneralLinearGroup ι R) :
    (TrivSqZeroExt.fstHom R R R).comp (representationCoordinateConstantLift ρ) =
      representationCoordinateEvaluation (R := R) ρ := by
  ext x
  rfl

/-- Actual derivations of the original coordinate algebra into the literal epsilon ideal, with its action given by the original representation point. -/
abbrev RepresentationCoordinateDerivations (ρ : G →* GeneralLinearGroup ι R) :=
  letI := (representationCoordinateConstantLift ρ).toRingHom.toAlgebra
  Derivation R (RepresentationCoordinateAlgebra G ι R) (TrivSqZeroExt.kerIdeal R R)

/-- Mathlib's actual square-zero derivation/lift equivalence identifies the genuine coordinate derivations with the original first-order coordinate fiber. -/
def representationCoordinateDerivationEquiv (ρ : G →* GeneralLinearGroup ι R) :
    RepresentationCoordinateDerivations ρ ≃
      RepresentationCoordinateFiber ρ (TrivSqZeroExt.fstHom R R R) := by
  letI := (representationCoordinateConstantLift ρ).toRingHom.toAlgebra
  letI : IsScalarTower R (RepresentationCoordinateAlgebra G ι R) (DualNumber R) :=
    IsScalarTower.of_algHom (representationCoordinateConstantLift ρ)
  have hc : IsScalarTower.toAlgHom R (RepresentationCoordinateAlgebra G ι R)
      (DualNumber R ⧸ TrivSqZeroExt.kerIdeal R R) =
        (Ideal.Quotient.mkₐ R (TrivSqZeroExt.kerIdeal R R)).comp
          (representationCoordinateConstantLift ρ) := by
    ext x
    rfl
  have hf (f : RepresentationCoordinateAlgebra G ι R →ₐ[R] DualNumber R) :
      (Ideal.Quotient.mkₐ R (TrivSqZeroExt.kerIdeal R R)).comp f =
        IsScalarTower.toAlgHom R (RepresentationCoordinateAlgebra G ι R)
          (DualNumber R ⧸ TrivSqZeroExt.kerIdeal R R) ↔
        (TrivSqZeroExt.fstHom R R R).comp f = representationCoordinateEvaluation (R := R) ρ := by
    rw [hc, dualNumberQuotient_comp_eq_iff, representationCoordinateConstantLift_reduction]
  exact (derivationToSquareZeroEquivLift (R := R)
    (A := RepresentationCoordinateAlgebra G ι R) (TrivSqZeroExt.kerIdeal R R)
    (TrivSqZeroExt.kerIdeal_sq R R)).trans
      { toFun := fun f => ⟨f.val, (hf f.val).mp f.property⟩
        invFun := fun f => ⟨f.val, (hf f.val).mpr f.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

/-- The actual coordinate lift supplied by a genuine derivation is its literal epsilon correction added to the original constant coordinate point. -/
theorem representationCoordinateDerivationEquiv_apply (ρ : G →* GeneralLinearGroup ι R)
    (d : RepresentationCoordinateDerivations ρ) (x : RepresentationCoordinateAlgebra G ι R) :
    (representationCoordinateDerivationEquiv ρ d).val x =
      (d x : DualNumber R) + representationCoordinateConstantLift ρ x := rfl

/-- The genuine derivations of the original matrix-representation coordinate algebra are equivalent to the actual adjoint cocycles of that original representation. -/
def representationCoordinateDerivationCocycleEquiv (ρ : G →* GeneralLinearGroup ι R) :
    RepresentationCoordinateDerivations ρ ≃ groupCohomology.cocycles₁ (matrixAdjointRep ρ) :=
  (representationCoordinateDerivationEquiv ρ).trans (firstOrderCoordinateCocycleEquiv ρ)

/-- Every original adjoint cocycle comes from a genuine derivation of the actual coordinate algebra at the original representation point. -/
theorem representationCoordinateDerivationCocycleEquiv_surjective
    (ρ : G →* GeneralLinearGroup ι R) :
    Function.Surjective (representationCoordinateDerivationCocycleEquiv ρ) :=
  (representationCoordinateDerivationCocycleEquiv ρ).surjective

end
end Dubon2026
