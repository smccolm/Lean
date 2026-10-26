import Dubon2026.SourceCurveCorrespondencePlaces
import Dubon2026.SourceGammaOneArithmeticDivisors

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> arithmetic equivariance of the actual Picard Hecke operator.
Commutation of the actual field maps gives place-restriction compatibility. Existing discrete orders then prove the actual ramification invariance.
Reuse the existing original arithmetic correspondence proof on these actual
integral-ratio fields. No arithmetic naturality certificate is postulated. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve
variable {L : Type*} [Field L] [Algebra ℚ L] [CharZero L]
variable (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

omit [CharZero L] in
theorem mem_arithmeticPlace_iff (σ : L ≃ₐ[ℚ] L)
    (v : Place L (functionFieldOver Γ L)) (x : functionFieldOver Γ L) :
    x ∈ (arithmeticPlace Γ σ v).toValuationSubring ↔
      arithmeticRingAut Γ σ.symm x ∈ v.toValuationSubring := Iff.rfl

variable (φ : functionFieldOver Γ L →ₐ[L] functionFieldOver Δ L)
variable (hφ : φ.toRingHom.Finite)
variable (hcomm : ∀ (σ : L ≃ₐ[ℚ] L) (x : functionFieldOver Γ L),
  arithmeticRingAut Δ σ (φ x) = φ (arithmeticRingAut Γ σ x))
include hcomm

theorem arithmeticPlace_restrictAlong (σ : L ≃ₐ[ℚ] L)
    (w : Place L (functionFieldOver Δ L)) :
    Place.restrictAlong φ hφ (arithmeticPlace Δ σ w) =
      arithmeticPlace Γ σ (Place.restrictAlong φ hφ w) := by
  apply Place.ext
  ext x
  rw [Place.mem_restrictAlong_iff, mem_arithmeticPlace_iff,
    mem_arithmeticPlace_iff, Place.mem_restrictAlong_iff]
  rw [hcomm]

theorem arithmeticPlace_ramificationAlong (σ : L ≃ₐ[ℚ] L)
    (w : Place L (functionFieldOver Δ L)) :
    Place.ramificationAlong φ hφ (arithmeticPlace Δ σ w) =
      Place.ramificationAlong φ hφ w := by
  have h := Place.ord_restrictAlong φ hφ (arithmeticPlace Δ σ w)
    (arithmeticRingAut Γ σ (Place.restrictAlong φ hφ w).uniformizer)
  rw [arithmeticPlace_restrictAlong Γ Δ φ hφ hcomm,
    arithmeticPlace_ord_action, Place.ord_uniformizer, one_mul] at h
  rw [← hcomm, arithmeticPlace_ord_action] at h
  exact h.symm

end
end Dubon2026.SourceFunctionField.GammaOne
