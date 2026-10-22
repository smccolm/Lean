import Dubon2026.SourceCurveCorrespondencePlaces
import Dubon2026.SourceOriginalHeckeFieldNaturality
import Dubon2026.SourceOriginalArithmeticDivisors

/-! DUB-17/18 -> original Tate Hecke realization -> arithmetic Hecke
equivariance. Commutation of the actual field maps with coefficient
automorphisms gives commutation of place restriction. The existing exact
order equations then identify the ramification orders on corresponding
places, without a ramification-invariance premise.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable {L : Type*} [Field L] [Algebra ℚ L] [CharZero L]
variable (N M : ℕ)

omit [CharZero L] in
theorem mem_originalArithmeticPlace_iff (σ : L ≃ₐ[ℚ] L)
    (v : Place L (modularFunctionFieldOver N L)) (x : modularFunctionFieldOver N L) :
    x ∈ (originalArithmeticPlace N σ v).toValuationSubring ↔
      originalArithmeticRingAut N σ.symm x ∈ v.toValuationSubring := Iff.rfl

variable (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
variable (hφ : φ.toRingHom.Finite)
variable (hcomm : ∀ (σ : L ≃ₐ[ℚ] L) (x : modularFunctionFieldOver N L),
  originalArithmeticRingAut M σ (φ x) = φ (originalArithmeticRingAut N σ x))
include hcomm

theorem originalArithmeticPlace_restrictAlong (σ : L ≃ₐ[ℚ] L)
    (w : Place L (modularFunctionFieldOver M L)) :
    Place.restrictAlong φ hφ (originalArithmeticPlace M σ w) =
      originalArithmeticPlace N σ (Place.restrictAlong φ hφ w) := by
  apply Place.ext
  ext x
  rw [Place.mem_restrictAlong_iff, mem_originalArithmeticPlace_iff,
    mem_originalArithmeticPlace_iff, Place.mem_restrictAlong_iff]
  rw [hcomm]

theorem originalArithmeticPlace_ramificationAlong (σ : L ≃ₐ[ℚ] L)
    (w : Place L (modularFunctionFieldOver M L)) :
    Place.ramificationAlong φ hφ (originalArithmeticPlace M σ w) =
      Place.ramificationAlong φ hφ w := by
  have h := Place.ord_restrictAlong φ hφ (originalArithmeticPlace M σ w)
    (originalArithmeticRingAut N σ (Place.restrictAlong φ hφ w).uniformizer)
  rw [originalArithmeticPlace_restrictAlong N M φ hφ hcomm,
    originalArithmeticPlace_ord_action, Place.ord_uniformizer, one_mul] at h
  rw [← hcomm, originalArithmeticPlace_ord_action] at h
  exact h.symm

end
end Dubon2026.SourceFunctionField
