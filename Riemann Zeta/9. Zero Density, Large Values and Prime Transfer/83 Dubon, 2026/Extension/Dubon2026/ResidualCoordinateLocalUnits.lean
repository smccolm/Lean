import Dubon2026.ResidualRepresentationCoordinates
import Dubon2026.RepresentationCoordinateFibers

/-! # Original integral lifts invert the actual residual point complement -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- An actual integral coordinate lift pulls back the original coefficient maximal ideal to the exact original residual point ideal. -/
theorem integralCoordinateMap_comap_maximal
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (f : RepresentationCoordinateFiber ρ (Algebra.ofId O (IsLocalRing.ResidueField O))) :
    Ideal.comap f.val.toRingHom (IsLocalRing.maximalIdeal O) =
      residualRepresentationCoordinateIdeal ρ := by
  ext x
  rw [Ideal.mem_comap, ← IsLocalRing.residue_eq_zero_iff]
  change IsLocalRing.residue O (f.val x) = 0 ↔
    representationCoordinateEvaluation (R := O) ρ x = 0
  have hx : IsLocalRing.residue O (f.val x) = representationCoordinateEvaluation (R := O) ρ x :=
    DFunLike.congr_fun f.property x
  rw [hx]

/-- Every element outside the original residual point ideal evaluates to a genuine unit under the original integral coordinate lift. -/
theorem integralCoordinateMap_isUnit
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (f : RepresentationCoordinateFiber ρ (Algebra.ofId O (IsLocalRing.ResidueField O)))
    (x : RepresentationCoordinateAlgebra G ι O) (hx : x ∉ residualRepresentationCoordinateIdeal ρ) :
    IsUnit (f.val x) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (f.val x)).mp
  have hf : IsLocalRing.residue O (f.val x) = representationCoordinateEvaluation (R := O) ρ x :=
    DFunLike.congr_fun f.property x
  rw [hf]
  exact hx

/-- The original integral matrix representation itself gives the actual units required for localization at its original residual representation point. -/
theorem integralRepresentationCoordinates_isUnit
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : MatrixRepresentationFiber ρ (Algebra.ofId O (IsLocalRing.ResidueField O)))
    (x : RepresentationCoordinateAlgebra G ι O) (hx : x ∉ residualRepresentationCoordinateIdeal ρ) :
    IsUnit (representationCoordinateEvaluation (R := O) τ.val x) :=
  integralCoordinateMap_isUnit ρ
    ((representationCoordinateFiberEquiv ρ (Algebra.ofId O (IsLocalRing.ResidueField O))).symm τ) x hx

end
end Dubon2026
