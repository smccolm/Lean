import Dubon2026.ContinuousFixedDeterminantClasses
import Dubon2026.ArithmeticUnramifiedFirstOrderCriterion

/-! # Actual unramified fixed-determinant arithmetic first-order classes -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- The intersection of the actual determinant trace kernel with the actual original inertia restriction kernel in continuous arithmetic adjoint cohomology. -/
def arithmeticUnramifiedFixedDeterminantClasses (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Submodule R (ContinuousMatrixAdjointH1 ρ hρ) :=
  continuousFixedDeterminantClasses ρ hρ ⊓ arithmeticUnramifiedAdjointClasses a ρ hρ P

/-- The actual simultaneous local submodule characterizes precisely the genuine first-order lifts with constant residual determinant and trivial original inertia. -/
theorem arithmeticUnramifiedFixedDeterminantClasses_firstOrder_iff (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ ∈
      arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P ↔
        (∀ g, Matrix.det (τ.val g).val = TrivSqZeroExt.inl (Matrix.det (ρ g).val)) ∧
          rationalArithmeticInertia a P ≤ τ.val.ker := by
  change (_ ∈ continuousFixedDeterminantClasses ρ hρ ∧
    _ ∈ arithmeticUnramifiedAdjointClasses a ρ hρ P) ↔ _
  rw [continuousFixedDeterminantClasses_firstOrder_iff,
    arithmeticUnramifiedAdjointClasses_firstOrder_inertia_iff a ρ hρ P hP]

/-- This genuine simultaneous first-order local condition is finite dimensional over the original finite arithmetic coefficient field. -/
theorem arithmeticUnramifiedFixedDeterminantClasses_finiteDimensional
    (K : Type) [Field K] [Finite K] [TopologicalSpace K] [DiscreteTopology K]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Module.Finite K (arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P) := by
  letI := arithmeticContinuousAdjointH1_finite a ha p hp hpa ρ hρ
  letI : Finite (arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Module.Finite.of_finite

end
end Dubon2026
