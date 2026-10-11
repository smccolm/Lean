import Dubon2026.OriginalUnframedOrdinaryCondition
import Dubon2026.OriginalCoefficientRepresentationClass
import Dubon2026.MatrixOrdinaryIdealInvariantCriterion

/-! # The literal ordinary ideal describes the genuine ordinary condition on original classes -/

namespace Dubon2026
noncomputable section
open Matrix

variable {O R A : Type} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- Evaluating the same original representation through the same genuine coefficient map gives an ordinary class exactly when that map kills the literal ordinary relation ideal of the original subgroup action. -/
theorem originalUnframedOrdinary_coefficient_iff
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{0}) (σ : H →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup (Fin 2) R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (N : Subgroup H) (g₀ : N) (hg₀ : σ g₀.val ≠ 1)
    (f : OriginalContinuousCoefficientFiber eR eA) :
    originalUnframedOrdinary eA H σ N
        (originalCoefficientRepresentationClass eR eA H σ τ hτ f) ↔
      matrixOrdinaryRelationIdeal (τ.toMonoidHom.comp N.subtype) g₀ ≤
        RingHom.ker f.val.toRingHom := by
  letI : IsLocalHom (localCoefficientReduction eA).toRingHom :=
    ⟨fun x hx => (localCoefficientReduction_ne_zero_iff eA x).mp (isUnit_iff_ne_zero.mp hx)⟩
  have hred : GeneralLinearGroup.map
      ((localCoefficientReduction eA).toRingHom.comp f.val.toRingHom) (τ g₀.val) = σ g₀.val :=
    DFunLike.congr_fun (originalCoefficientRepresentationFramed eR eA H σ τ hτ f).property g₀.val
  exact (matrixOrdinaryRelationIdeal_le_kernel_iff_invariants
    (τ.toMonoidHom.comp N.subtype) g₀ f.val.toRingHom (localCoefficientReduction eA).toRingHom
    (fun h => hg₀ (hred.symm.trans h))).symm

end
end Dubon2026
