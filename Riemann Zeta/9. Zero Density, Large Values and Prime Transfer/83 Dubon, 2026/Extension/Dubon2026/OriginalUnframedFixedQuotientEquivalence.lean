import Dubon2026.OriginalUnframedDeformationClasses
import Dubon2026.OriginalResidualFramedFibers

/-! # The genuine original fixed-residual quotient preserves all unframed deformation classes -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- The existing whole framed fixed-quotient equivalence preserves and reflects the actual same strict conjugators, since every original quotient element has an original group representative. -/
theorem originalFramedFixedQuotient_strict_iff
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (ρ τ : OriginalContinuousFramedFiber eA H σ) :
    MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
        ρ.val.toMonoidHom τ.val.toMonoidHom ↔
      MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
        ((originalFramedFiberFixedQuotientEquiv hA eA p hp H σ hσ) ρ).val.toMonoidHom
        ((originalFramedFiberFixedQuotientEquiv hA eA p hp H σ hσ) τ).val.toMonoidHom := by
  let N := fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)
  constructor
  · rintro ⟨U, hU, h⟩
    refine ⟨U, hU, ?_⟩
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact h g
  · rintro ⟨U, hU, h⟩
    exact ⟨U, hU, fun g => h (QuotientGroup.mk' N g)⟩

/-- Descend the actual existing framed equivalence to the actual existing original strict-conjugacy quotients, giving the whole unframed fixed-residual quotient equivalence. -/
def originalUnframedFixedQuotientEquiv
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ) :
    OriginalUnframedDeformationClass eA H σ ≃
      OriginalUnframedDeformationClass eA
        (fixedResidualProfiniteQuotient p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ))
        (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom :=
  Quotient.congr (originalFramedFiberFixedQuotientEquiv hA eA p hp H σ hσ)
    (originalFramedFixedQuotient_strict_iff hA eA p hp H σ hσ)

/-- The genuine unframed quotient equivalence sends every original framed class to the class of its actual existing fixed-quotient factor. -/
theorem originalUnframedFixedQuotientEquiv_class
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (ρ : OriginalContinuousFramedFiber eA H σ) :
    originalUnframedFixedQuotientEquiv hA eA p hp H σ hσ (originalUnframedClass eA H σ ρ) =
      originalUnframedClass eA _ (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom
        (originalFramedFiberFixedQuotientEquiv hA eA p hp H σ hσ ρ) := by
  rfl

end
end Dubon2026
