import Dubon2026.SourceOriginalArithmeticIntegralCharts
import Dubon2026.SourceOriginalArithmeticPlaces

/-! DUB-17/18 -> original arithmetic inertia on Picard classes -> actual
reduction-place invariance. Identify the two already proved equal modular
fields and transport the existing original place action. Native place
transport and the nonunit criterion avoid rebuilding valuations or orders.
The arithmetic actor remains the original coefficient automorphism. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ)
local notation "Fo" => modularFunctionFieldOver N Qbar
local notation "F" => modularFunctionFieldCoeff N Qbar

/-- The identity on the Laurent series in the two equal modular fields. -/
def originalCoefficientEquiv : Fo ≃ₐ[Qbar] F where
  toFun f := ⟨f.val, by rw [← original_field_eq_coefficient_field]; exact f.property⟩
  invFun f := ⟨f.val, by rw [original_field_eq_coefficient_field]; exact f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem originalCoefficientEquiv_arithmetic (τ : Qbar ≃ₐ[ℚ] Qbar) (f : Fo) :
    originalCoefficientEquiv N (originalArithmeticRingAut N τ f) =
      coefficientArithmeticRingAut N τ (originalCoefficientEquiv N f) := by
  apply Subtype.ext
  rfl

/-- The native place equivalence of the identical modular fields. -/
def originalCoefficientPlaceEquiv : Place Qbar Fo ≃ Place Qbar F :=
  Place.placeEquiv (originalCoefficientEquiv N).symm

/-- The original arithmetic place action in coefficient-field coordinates. -/
def coefficientArithmeticPlace (τ : Qbar ≃ₐ[ℚ] Qbar) (P : Place Qbar F) : Place Qbar F :=
  originalCoefficientPlaceEquiv N
    (originalArithmeticPlace N τ ((originalCoefficientPlaceEquiv N).symm P))

theorem coefficientArithmeticPlace_original (τ : Qbar ≃ₐ[ℚ] Qbar) (P : Place Qbar Fo) :
    coefficientArithmeticPlace N τ (originalCoefficientPlaceEquiv N P) =
      originalCoefficientPlaceEquiv N (originalArithmeticPlace N τ P) := by
  unfold coefficientArithmeticPlace
  rw [Equiv.symm_apply_apply]

theorem mem_coefficientArithmeticPlace_iff (τ : Qbar ≃ₐ[ℚ] Qbar)
    (P : Place Qbar F) (f : F) :
    f ∈ (coefficientArithmeticPlace N τ P).toValuationSubring ↔
      coefficientArithmeticRingAut N τ.symm f ∈ P.toValuationSubring := by
  change originalCoefficientEquiv N
      (originalArithmeticRingAut N τ.symm ((originalCoefficientEquiv N).symm f)) ∈
        P.toValuationSubring ↔ _
  rw [originalCoefficientEquiv_arithmetic, AlgEquiv.apply_symm_apply]

theorem nonunit_coefficientArithmeticPlace_iff (τ : Qbar ≃ₐ[ℚ] Qbar)
    (P : Place Qbar F) (f : F) :
    f ∈ (coefficientArithmeticPlace N τ P).toValuationSubring.nonunits ↔
      coefficientArithmeticRingAut N τ.symm f ∈ P.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    mem_coefficientArithmeticPlace_iff, map_inv₀]
  simp only [map_eq_zero]

end
end Dubon2026.SourceFunctionField.GaussReduction
