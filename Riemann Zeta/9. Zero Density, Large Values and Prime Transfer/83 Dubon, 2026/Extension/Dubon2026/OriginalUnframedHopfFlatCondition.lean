import Dubon2026.OriginalUnframedDeformationClasses
import Dubon2026.MatrixAdicHopfFlatFiniteCoefficients

/-! # The full local model condition on the original deformation classes

The restriction homomorphism is an explicit input. Arithmetic identification of
that map and existence of the required local models remain separate obligations.
-/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable (R F K : Type u) {ι O A : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- The entire actual maximal-adic local model condition on the existing original unframed deformation class, with the specified original Galois restriction. Strict conjugacy preserves it at every original reduction level. -/
def originalUnframedHopfFlat
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (j : (K ≃ₐ[F] K) →* H) : OriginalUnframedDeformationClass eA H σ → Prop :=
  Quotient.lift (fun ρ : OriginalContinuousFramedFiber eA H σ =>
    MatrixAdicHopfFlat R F K (ρ.val.toMonoidHom.comp j)) (by
      intro ρ τ h
      obtain ⟨U, _hU, hc⟩ := h
      apply propext
      exact matrixAdicHopfFlat_conjugacy_iff
        (ρ.val.toMonoidHom.comp j) (τ.val.toMonoidHom.comp j) U (fun g => hc (j g)))

variable {R F K}

/-- Evaluation on an original framed representative keeps precisely the original restricted representation and every positive original maximal-adic reduction. This is the defining identification, not an existence assertion. -/
theorem originalUnframedHopfFlat_class_iff
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (j : (K ≃ₐ[F] K) →* H) (ρ : OriginalContinuousFramedFiber eA H σ) :
    originalUnframedHopfFlat R F K eA H σ j (originalUnframedClass eA H σ ρ) ↔
      MatrixAdicHopfFlat R F K (ρ.val.toMonoidHom.comp j) := by
  rfl

variable [IsDomain R] [IsPrincipalIdealRing R] [PerfectField F] [IsFractionRing R F]
  [Normal F K] [IsAlgClosed K] [Finite A]

/-- Over original finite local coefficients the class condition is equivalent to an actual finite free model of the same original restricted whole representation. The equivalence uses proved nilpotence and the genuine model subquotient constructions. -/
theorem originalUnframedHopfFlat_finite_class_iff
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (j : (K ≃ₐ[F] K) →* H) (ρ : OriginalContinuousFramedFiber eA H σ) :
    originalUnframedHopfFlat R F K eA H σ j (originalUnframedClass eA H σ ρ) ↔
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A))
        (matrixUnderlyingGroupAction (ρ.val.toMonoidHom.comp j))) := by
  exact matrixAdicHopfFlat_finite_iff (ρ.val.toMonoidHom.comp j)

end
end Dubon2026
