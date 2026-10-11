import Dubon2026.OriginalUnframedDeformationClasses
import Dubon2026.MatrixInvariantSubmoduleConjugacy

/-! # The genuine ordinary invariant-summand condition on original unframed classes -/

namespace Dubon2026
noncomputable section
open Matrix

variable {O A : Type} [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- The ordinary condition means that the entire actual subgroup-invariant module is free of rank one and a direct summand of the original two-dimensional coefficient module. -/
def originalUnframedOrdinary
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{0}) (σ : H →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (N : Subgroup H) : OriginalUnframedDeformationClass eA H σ → Prop :=
  Quotient.lift (fun ρ : OriginalContinuousFramedFiber eA H σ =>
    Nonempty ((matrixStandardRepresentation (ρ.val.toMonoidHom.comp N.subtype)).invariants ≃ₗ[A] A) ∧
      ∃ W : Submodule A (Fin 2 → A),
        IsCompl (matrixStandardRepresentation (ρ.val.toMonoidHom.comp N.subtype)).invariants W) (by
      intro ρ τ h
      obtain ⟨U, _hU, hc⟩ := h
      apply propext
      exact matrix_invariants_rankOne_split_conjugacy_iff
        (ρ.val.toMonoidHom.comp N.subtype) (τ.val.toMonoidHom.comp N.subtype) U
        (fun g => hc g.val))

/-- The ordinary condition on the class of an original framed lift is exactly the original rank-one invariant direct-summand condition, with no surrogate condition. -/
theorem originalUnframedOrdinary_class_iff
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{0}) (σ : H →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (N : Subgroup H) (ρ : OriginalContinuousFramedFiber eA H σ) :
    originalUnframedOrdinary eA H σ N (originalUnframedClass eA H σ ρ) ↔
      (Nonempty ((matrixStandardRepresentation (ρ.val.toMonoidHom.comp N.subtype)).invariants ≃ₗ[A] A) ∧
        ∃ W : Submodule A (Fin 2 → A),
          IsCompl (matrixStandardRepresentation (ρ.val.toMonoidHom.comp N.subtype)).invariants W) := by
  rfl

end
end Dubon2026
