import Dubon2026.ArithmeticUnramifiedFixedDeterminantClasses
import Mathlib.Data.Setoid.Basic

/-! # Genuine local arithmetic first-order lifts modulo actual strict conjugacy -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- The original continuous dual-number lifts satisfying the actual fixed residual determinant and inertia equations. -/
def ArithmeticLocalFirstOrderLift (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :=
  {τ : {τ : MatrixFirstOrderLift ρ // Continuous τ.val} //
    (∀ g, Matrix.det (τ.val.val g).val = TrivSqZeroExt.inl (Matrix.det (ρ g).val)) ∧
      rationalArithmeticInertia a P ≤ τ.val.val.ker}

/-- The actual first-order class map lands in the genuine simultaneous local cohomology submodule by the proved determinant and inertia criteria. -/
def arithmeticLocalFirstOrderClass (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker)
    (τ : ArithmeticLocalFirstOrderLift a ρ P) :
    arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P :=
  ⟨continuousMatrixFirstOrderClass ρ hρ τ.val.val τ.val.property,
    (arithmeticUnramifiedFixedDeterminantClasses_firstOrder_iff a ρ hρ P hP
      τ.val.val τ.val.property).mpr τ.property⟩

/-- Every class in the actual simultaneous local submodule is represented by an original continuous first-order lift satisfying both genuine local equations. -/
theorem arithmeticLocalFirstOrderClass_surjective (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker) :
    Function.Surjective (arithmeticLocalFirstOrderClass a ρ hρ P hP) := by
  intro c
  obtain ⟨⟨τ, hτ⟩, hc⟩ := continuousMatrixFirstOrderClass_surjective ρ hρ c.val
  change continuousMatrixFirstOrderClass ρ hρ τ hτ = c.val at hc
  have hmem : continuousMatrixFirstOrderClass ρ hρ τ hτ ∈
      arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P := hc.symm ▸ c.property
  refine ⟨⟨⟨τ, hτ⟩,
    (arithmeticUnramifiedFixedDeterminantClasses_firstOrder_iff a ρ hρ P hP τ hτ).mp hmem⟩, ?_⟩
  exact Subtype.ext hc

/-- Two original local lifts have the same actual local class precisely when an original invertible dual-number change of basis reducing to the identity conjugates their entire representations. -/
theorem arithmeticLocalFirstOrderClass_eq_iff (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker)
    (τ υ : ArithmeticLocalFirstOrderLift a ρ P) :
    arithmeticLocalFirstOrderClass a ρ hρ P hP τ = arithmeticLocalFirstOrderClass a ρ hρ P hP υ ↔
      MatrixFirstOrderStrictlyConjugate ρ τ.val.val υ.val.val := by
  rw [Subtype.ext_iff]
  exact continuousMatrixFirstOrderClass_eq_iff ρ hρ τ.val.val υ.val.val
    τ.val.property υ.val.property

/-- The quotient by equality of actual local classes, proved above to be exactly original strict conjugacy, is equivalent to the genuine local cohomology submodule. -/
def arithmeticLocalFirstOrderClassesEquiv (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker) :
    Quotient (Setoid.ker (arithmeticLocalFirstOrderClass a ρ hρ P hP)) ≃
      arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P :=
  Setoid.quotientKerEquivOfSurjective _ (arithmeticLocalFirstOrderClass_surjective a ρ hρ P hP)

end
end Dubon2026
