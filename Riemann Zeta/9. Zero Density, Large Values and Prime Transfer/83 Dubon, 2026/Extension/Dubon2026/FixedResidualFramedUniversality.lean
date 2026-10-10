import Dubon2026.FixedResidualFramedCoefficientRing

/-! # Universal original framed lifts over the actual fixed-residual coefficient ring -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {ι O : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]

/-- Pull the actual presented universal matrices back to every element of the original whole group. -/
def fixedResidualFramedUniversalRepresentation
    (p : ℕ) (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S)) :
    H →* GeneralLinearGroup ι (FixedResidualFramedCoefficientRing p H σ hσ S) :=
  (completedPresentationRepresentation
    (originalPresentedResidualRestriction (originalResidualProfiniteGroup p H σ hσ)
      (profiniteGeneratorPresentation (originalResidualProfiniteGroup p H σ hσ) S)
      (fixedResidualOriginalRepresentation p H σ hσ))
    (originalResidualProfiniteGroup p H σ hσ)
    (profiniteGeneratorPresentation (originalResidualProfiniteGroup p H σ hσ) S) hS).comp
      (QuotientGroup.mk' (fixedResidualProPKernel p H σ.ker
        (originalResidualMatrixKernel_isClosed H σ hσ)))

/-- The actual universal representation of the original whole group is continuous in the original quotient coefficient topology. -/
theorem fixedResidualFramedUniversalRepresentation_continuous
    (p : ℕ) (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S)) :
    Continuous (fixedResidualFramedUniversalRepresentation p H σ hσ S hS) :=
  (completedPresentedGroupRepresentation_continuous _ _ _ hS).comp
    QuotientGroup.continuous_mk

/-- Reduction through the actual residue field of the genuine universal coefficient ring recovers the original entire residual representation. -/
theorem fixedResidualFramedUniversalRepresentation_residue
    (p : ℕ) (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S)) :
    (letI := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
     (GeneralLinearGroup.map (n := ι)
       (localCoefficientReduction (fixedResidualFramedCoefficientResidueEquiv p H σ hσ S)).toRingHom).comp
         (fixedResidualFramedUniversalRepresentation p H σ hσ S hS) = σ) := by
  letI := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
  have hr := originalPresentedCoefficientRing_universal_residue
    (originalResidualProfiniteGroup p H σ hσ)
    (profiniteGeneratorPresentation (originalResidualProfiniteGroup p H σ hσ) S) hS
    (fixedResidualOriginalRepresentation p H σ hσ)
  apply MonoidHom.ext
  intro h
  exact DFunLike.congr_fun hr (QuotientGroup.mk'
    (fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)) h)

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Genuine continuous residue-preserving maps from the actual fixed-residual coefficient ring classify all original continuous framed lifts over every complete Noetherian local coefficient algebra. -/
def fixedResidualFramedFiberEquiv
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S)) :
    (letI := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
     OriginalContinuousCoefficientFiber (fixedResidualFramedCoefficientResidueEquiv p H σ hσ S) eA ≃
       OriginalContinuousFramedFiber eA H σ) :=
  (originalPresentedFramedFiberEquiv hA eA (originalResidualProfiniteGroup p H σ hσ)
    (profiniteGeneratorPresentation (originalResidualProfiniteGroup p H σ hσ) S) hS
    (fixedResidualOriginalRepresentation p H σ hσ)).trans
      (originalFramedFiberFixedQuotientEquiv hA eA p hp H σ hσ).symm

/-- The full original framed classification evaluates the actual universal representation at each original group element. -/
theorem fixedResidualFramedFiberEquiv_evaluation
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S)) :
    (letI := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
     ∀ (f : OriginalContinuousCoefficientFiber
       (fixedResidualFramedCoefficientResidueEquiv p H σ hσ S) eA) (h : H),
       (fixedResidualFramedFiberEquiv hA eA p hp H σ hσ S hS f).val h =
         GeneralLinearGroup.map (n := ι) f.val.toRingHom
           (fixedResidualFramedUniversalRepresentation p H σ hσ S hS h)) := by
  intro f h
  rfl

variable {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- The original whole-group classification is natural under every actual continuous residue-preserving coefficient morphism. It is the literal identity obtained by evaluating the same universal matrices. -/
theorem fixedResidualFramedFiberEquiv_natural
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S))
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    (letI := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
     ∀ f : OriginalContinuousCoefficientFiber
       (fixedResidualFramedCoefficientResidueEquiv p H σ hσ S) eA,
       fixedResidualFramedFiberEquiv hB eB p hp H σ hσ S hS
         (originalCoefficientFiberPostcomp _ eA eB k hk hres f) =
           originalFramedFiberPostcomp eA eB H σ k hk hres
             (fixedResidualFramedFiberEquiv hA eA p hp H σ hσ S hS f)) := by
  intro f
  apply Subtype.ext
  apply DFunLike.ext
  intro h
  rfl

end
end Dubon2026
