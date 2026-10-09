import Dubon2026.LocalCoefficientReduction
import Dubon2026.RepresentationCoordinateFibers

/-! # Original residual coordinate lifts into genuine local coefficient algebras -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]

/-- The original coordinate lift into a local coefficient algebra pulls back its actual maximal ideal to the literal original residual point. -/
theorem localCoefficientCoordinateMap_comap_maximal
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e)) :
    Ideal.comap f.val.toRingHom (IsLocalRing.maximalIdeal A) =
      residualRepresentationCoordinateIdeal ρ := by
  ext x
  rw [Ideal.mem_comap, ← localCoefficientReduction_eq_zero_iff e]
  change localCoefficientReduction e (f.val x) = 0 ↔
    representationCoordinateEvaluation (R := O) ρ x = 0
  have hf : localCoefficientReduction e (f.val x) =
      representationCoordinateEvaluation (R := O) ρ x := DFunLike.congr_fun f.property x
  rw [hf]

/-- Every denominator outside the original residual point maps to an actual unit under the original local coefficient lift. -/
theorem localCoefficientCoordinateMap_isUnit
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e))
    (x : RepresentationCoordinateAlgebra G ι O) (hx : x ∉ residualRepresentationCoordinateIdeal ρ) :
    IsUnit (f.val x) := by
  apply (localCoefficientReduction_ne_zero_iff e (f.val x)).mp
  have hf : localCoefficientReduction e (f.val x) =
      representationCoordinateEvaluation (R := O) ρ x := DFunLike.congr_fun f.property x
  rw [hf]
  exact hx

/-- The original matrix representation over the actual local coefficient algebra itself supplies the units required at its original residual point. -/
theorem localCoefficientRepresentationCoordinates_isUnit
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : MatrixRepresentationFiber ρ (localCoefficientReduction e))
    (x : RepresentationCoordinateAlgebra G ι O) (hx : x ∉ residualRepresentationCoordinateIdeal ρ) :
    IsUnit (representationCoordinateEvaluation (R := O) τ.val x) :=
  localCoefficientCoordinateMap_isUnit ρ e
    ((representationCoordinateFiberEquiv ρ (localCoefficientReduction e)).symm τ) x hx

end
end Dubon2026
