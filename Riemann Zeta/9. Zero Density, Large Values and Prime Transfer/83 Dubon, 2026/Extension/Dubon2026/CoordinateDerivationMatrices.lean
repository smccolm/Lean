import Dubon2026.RepresentationCoordinateDerivations

/-! # Actual epsilon matrix entries of coordinate derivations -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The literal epsilon entries of the original coordinate derivation at an original group element. -/
def coordinateDerivationMatrix (ρ : G →* GeneralLinearGroup ι R)
    (d : RepresentationCoordinateDerivations ρ) (g : G) : Matrix ι ι R :=
  fun i j => (d (representationCoordinateMatrix G ι R g i j)).val.snd

/-- The actual coordinate derivation gives the original adjoint cocycle by the exact right logarithmic matrix formula. -/
theorem representationCoordinateDerivationCocycleEquiv_value
    (ρ : G →* GeneralLinearGroup ι R) (d : RepresentationCoordinateDerivations ρ) (g : G) :
    representationCoordinateDerivationCocycleEquiv ρ d g =
      coordinateDerivationMatrix ρ d g * ((ρ g)⁻¹).val := by
  let f := representationCoordinateDerivationEquiv ρ d
  let τ := firstOrderRepresentationCoordinateEquiv ρ f
  have hr : dualMatrixReduction (τ.val g) = ρ g := DFunLike.congr_fun τ.property g
  have hs : dualMatrixSnd (τ.val g).val = coordinateDerivationMatrix ρ d g := by
    apply Matrix.ext
    intro i j
    change ((representationCoordinateDerivationEquiv ρ d).val
      (representationCoordinateMatrix G ι R g i j)).snd =
        (d (representationCoordinateMatrix G ι R g i j)).val.snd
    rw [representationCoordinateDerivationEquiv_apply]
    simp [representationCoordinateConstantLift]
  change dualMatrixInfinitesimal (τ.val g) = _
  rw [dualMatrixInfinitesimal, hs, hr]

/-- The original epsilon matrix is additive in the actual coordinate derivation. -/
theorem coordinateDerivationMatrix_add (ρ : G →* GeneralLinearGroup ι R)
    (d e : RepresentationCoordinateDerivations ρ) (g : G) :
    coordinateDerivationMatrix ρ (d + e) g =
      coordinateDerivationMatrix ρ d g + coordinateDerivationMatrix ρ e g := rfl

/-- The original epsilon matrix respects scalar multiplication of the actual coordinate derivation. -/
theorem coordinateDerivationMatrix_smul (ρ : G →* GeneralLinearGroup ι R)
    (a : R) (d : RepresentationCoordinateDerivations ρ) (g : G) :
    coordinateDerivationMatrix ρ (a • d) g = a • coordinateDerivationMatrix ρ d g := rfl

end
end Dubon2026
