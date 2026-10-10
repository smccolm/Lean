import Dubon2026.ArithmeticLocalFirstOrderClasses
import Dubon2026.RelativeDualNumberFramedEquiv

/-! # Original local first-order lifts and the actual restricted dual-number framed fiber -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The original coefficient ring and its prescribed determinant give the genuine restricted residual dual-number fiber of the same local first-order lifts. -/
def arithmeticRelativeLocalDualNumberFramedFiberEquiv (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (ρ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    ArithmeticLocalFirstOrderLift a ρ P ≃
      (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) := ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
       letI : TopologicalSpace (DualNumber (IsLocalRing.ResidueField O)) :=
         (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))).adicTopology
       {f : {f : OriginalContinuousFramedFiber (relativeDualNumberResidueEquiv O)
          (rationalArithmeticGaloisGroup a)
          ρ //
          ∀ g, GeneralLinearGroup.det (f.val g) =
            Units.map (algebraMap O (DualNumber (IsLocalRing.ResidueField O))) (δ g)} //
        rationalArithmeticInertia a P ≤ f.val.val.toMonoidHom.ker}) where
  toFun τ := by
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) := ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    letI : TopologicalSpace (DualNumber (IsLocalRing.ResidueField O)) :=
      (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))).adicTopology
    refine ⟨⟨relativeDualNumberFramedFiberEquiv (rationalArithmeticGaloisGroup a) ρ τ.val, ?_⟩,
      τ.property.2⟩
    intro g
    apply Units.ext
    exact (τ.property.1 g).trans (congrArg TrivSqZeroExt.inl (congrArg Units.val (hδ g)))
  invFun f := by
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) := ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    letI : TopologicalSpace (DualNumber (IsLocalRing.ResidueField O)) :=
      (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))).adicTopology
    refine ⟨(relativeDualNumberFramedFiberEquiv (rationalArithmeticGaloisGroup a) ρ).symm
      f.val.val, ?_, f.property⟩
    intro g
    exact (congrArg Units.val (f.val.property g)).trans
      (congrArg TrivSqZeroExt.inl (congrArg Units.val (hδ g))).symm
  left_inv τ := by
    apply Subtype.ext
    exact (relativeDualNumberFramedFiberEquiv (rationalArithmeticGaloisGroup a) ρ).symm_apply_apply τ.val
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    exact (relativeDualNumberFramedFiberEquiv (rationalArithmeticGaloisGroup a) ρ).apply_symm_apply f.val.val

/-- Every original restricted dual-number coefficient lift corresponds uniquely to its original continuous local first-order representation. -/
theorem arithmeticRelativeLocalDualNumberFramedFiberEquiv_bijective (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (ρ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Function.Bijective (arithmeticRelativeLocalDualNumberFramedFiberEquiv a ρ δ hδ P) :=
  (arithmeticRelativeLocalDualNumberFramedFiberEquiv a ρ δ hδ P).bijective

end
end Dubon2026
