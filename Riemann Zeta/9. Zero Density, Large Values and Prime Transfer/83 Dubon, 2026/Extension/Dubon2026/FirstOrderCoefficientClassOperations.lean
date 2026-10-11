import Dubon2026.FirstOrderCoefficientAddition
import Dubon2026.FirstOrderCoefficientScaling
import Dubon2026.ContinuousAdjointCohomology

/-! # Actual first-order coefficient operations give the original cohomology operations -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k] [IsTopologicalRing k]

/-- The genuine compatible-coefficient sum represents the sum of the same original
continuous cohomology classes. -/
theorem continuousMatrixFirstOrderClass_sum
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (τ υ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) (hυ : Continuous υ.val) :
    continuousMatrixFirstOrderClass ρ hρ (matrixFirstOrderSum ρ τ υ)
        (matrixFirstOrderSum_continuous ρ hρ τ υ hτ hυ) =
      continuousMatrixFirstOrderClass ρ hρ τ hτ + continuousMatrixFirstOrderClass ρ hρ υ hυ := by
  let u : continuousMatrixAdjointCocycles ρ :=
    ⟨matrixFirstOrderCocycle ρ τ, matrixFirstOrderCocycle_continuous ρ hρ τ hτ⟩
  let v : continuousMatrixAdjointCocycles ρ :=
    ⟨matrixFirstOrderCocycle ρ υ, matrixFirstOrderCocycle_continuous ρ hρ υ hυ⟩
  let w : continuousMatrixAdjointCocycles ρ :=
    ⟨matrixFirstOrderCocycle ρ (matrixFirstOrderSum ρ τ υ),
      matrixFirstOrderCocycle_continuous ρ hρ _ (matrixFirstOrderSum_continuous ρ hρ τ υ hτ hυ)⟩
  have hw : w = u + v := by
    apply Subtype.ext
    exact matrixFirstOrderSum_cocycle ρ τ υ
  change (Submodule.Quotient.mk w : ContinuousMatrixAdjointH1 ρ hρ) =
    Submodule.Quotient.mk u + Submodule.Quotient.mk v
  rw [hw]
  exact Submodule.Quotient.mk_add _

/-- The actual epsilon scaling represents scalar multiplication of the same original
continuous cohomology class. -/
theorem continuousMatrixFirstOrderClass_scale
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (c : k) (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixFirstOrderClass ρ hρ (matrixFirstOrderScale ρ c τ)
        (matrixFirstOrderScale_continuous ρ hρ c τ hτ) =
      c • continuousMatrixFirstOrderClass ρ hρ τ hτ := by
  let u : continuousMatrixAdjointCocycles ρ :=
    ⟨matrixFirstOrderCocycle ρ τ, matrixFirstOrderCocycle_continuous ρ hρ τ hτ⟩
  let w : continuousMatrixAdjointCocycles ρ :=
    ⟨matrixFirstOrderCocycle ρ (matrixFirstOrderScale ρ c τ),
      matrixFirstOrderCocycle_continuous ρ hρ _ (matrixFirstOrderScale_continuous ρ hρ c τ hτ)⟩
  have hw : w = c • u := by
    apply Subtype.ext
    exact matrixFirstOrderScale_cocycle ρ c τ
  change (Submodule.Quotient.mk w : ContinuousMatrixAdjointH1 ρ hρ) =
    c • Submodule.Quotient.mk u
  rw [hw]
  exact Submodule.Quotient.mk_smul _ c u

/-- The genuine lift of the zero cocycle represents the zero original continuous
cohomology class. -/
theorem continuousMatrixFirstOrderClass_zero
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ) :
    continuousMatrixFirstOrderClass ρ hρ (firstOrderLiftFromCocycle ρ 0)
      (firstOrderLiftFromCocycle_continuous ρ hρ 0 continuous_const) = 0 := by
  let w : continuousMatrixAdjointCocycles ρ :=
    ⟨matrixFirstOrderCocycle ρ (firstOrderLiftFromCocycle ρ 0),
      matrixFirstOrderCocycle_continuous ρ hρ _
        (firstOrderLiftFromCocycle_continuous ρ hρ 0 continuous_const)⟩
  have hw : w = 0 := by
    apply Subtype.ext
    exact matrixFirstOrderCocycle_fromCocycle ρ 0
  change (Submodule.Quotient.mk w : ContinuousMatrixAdjointH1 ρ hρ) = 0
  rw [hw]
  exact Submodule.Quotient.mk_zero _

end
end Dubon2026
