import Dubon2026.ArithmeticLocalFirstOrderClasses
import Dubon2026.OriginalDualNumberFramedEquiv

/-! # Original local first-order lifts and the actual restricted dual-number framed fiber -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace K] [DiscreteTopology K]

/-- The same whole first-order lifts with original inertia and determinant equations form the genuine restricted framed fiber over the actual dual-number coefficient algebra. -/
def arithmeticLocalDualNumberFramedFiberEquiv (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    ArithmeticLocalFirstOrderLift a ρ P ≃
      (letI : WithIdeal (DualNumber K) := ⟨IsLocalRing.maximalIdeal (DualNumber K)⟩
       letI : TopologicalSpace (DualNumber K) :=
         (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology
       {f : {f : OriginalContinuousFramedFiber (dualNumberOriginalResidueEquiv K)
          (rationalArithmeticGaloisGroup a)
          ((GeneralLinearGroup.map (n := ι) (IsLocalRing.residue K)).comp ρ) //
          ∀ g, GeneralLinearGroup.det (f.val g) =
            Units.map (algebraMap K (DualNumber K)).toMonoidHom (GeneralLinearGroup.det (ρ g))} //
        rationalArithmeticInertia a P ≤ f.val.val.toMonoidHom.ker}) where
  toFun τ := by
    letI : WithIdeal (DualNumber K) := ⟨IsLocalRing.maximalIdeal (DualNumber K)⟩
    letI : TopologicalSpace (DualNumber K) :=
      (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology
    refine ⟨⟨originalDualNumberFramedFiberEquiv (rationalArithmeticGaloisGroup a) ρ τ.val, ?_⟩,
      τ.property.2⟩
    intro g
    apply Units.ext
    exact τ.property.1 g
  invFun f := by
    letI : WithIdeal (DualNumber K) := ⟨IsLocalRing.maximalIdeal (DualNumber K)⟩
    letI : TopologicalSpace (DualNumber K) :=
      (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology
    refine ⟨(originalDualNumberFramedFiberEquiv (rationalArithmeticGaloisGroup a) ρ).symm
      f.val.val, ?_, f.property⟩
    intro g
    exact congrArg Units.val (f.val.property g)
  left_inv τ := by
    apply Subtype.ext
    exact (originalDualNumberFramedFiberEquiv (rationalArithmeticGaloisGroup a) ρ).symm_apply_apply τ.val
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    exact (originalDualNumberFramedFiberEquiv (rationalArithmeticGaloisGroup a) ρ).apply_symm_apply f.val.val

/-- Every original restricted dual-number coefficient lift corresponds uniquely to its original continuous local first-order representation. -/
theorem arithmeticLocalDualNumberFramedFiberEquiv_bijective (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Function.Bijective (arithmeticLocalDualNumberFramedFiberEquiv a ρ P) :=
  (arithmeticLocalDualNumberFramedFiberEquiv a ρ P).bijective

end
end Dubon2026
