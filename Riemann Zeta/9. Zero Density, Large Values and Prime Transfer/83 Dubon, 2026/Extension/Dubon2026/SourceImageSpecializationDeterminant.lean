import Dubon2026.SourceImageSpecializationPairing
import Dubon2026.SourceAlternatingRankTwoDeterminant
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! DUB-17/18 -> the separate primitive determinant. Combine the proved
nondegenerate image pairing, its exact prescribed specialization, invariance
and multiplier with the two-dimensional determinant calculation. -/
namespace Dubon2026
noncomputable section
open Matrix
variable {E V Z : Type*} [Field E]
variable [AddCommGroup V] [Module E V] [AddCommGroup Z] [Module E Z]

theorem image_specialization_determinant
    (B : V →ₗ[E] V →ₗ[E] Z) (π : V →ₗ[E] (Fin 2 → E))
    (Q : Module.End E V) (e : Q.range ≃ₗ[E] (Fin 2 → E))
    (he : ∀ x, e x = π x.val) (hAlt : B.IsAlt)
    (hInj : Function.Injective (B.compl₁₂ Q.range.subtype Q.range.subtype))
    (G : Module.End E V) (M : Matrix (Fin 2) (Fin 2) E)
    (hc : Commute G Q) (hπ : ∀ x, π (G x) = M *ᵥ π x) (c : E)
    (hB : ∀ x y, B (G x) (G y) = c • B x y) : M.det = c := by
  exact determinant_eq_alternating_multiplier (imageSpecializationPairing B Q e)
    (imageSpecializationPairing_self B Q e hAlt)
    (imageSpecializationPairing_injective B Q e hInj) M c
    (imageSpecializationPairing_multiplier B π Q e he G (Matrix.toLin' M) hc hπ c hB)

end
end Dubon2026
