import Dubon2026.ArithmeticLocalFirstOrderClasses

/-! # The actual continuous cocycles of original local first-order arithmetic lifts -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Original continuous adjoint cocycles with zero actual trace and zero restriction to the original inertia subgroup. -/
def arithmeticLocalFirstOrderCocycles (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Submodule R (continuousMatrixAdjointCocycles ρ) :=
  (continuousMatrixAdjointTrace ρ).ker ⊓
    (continuousMatrixAdjointRestriction ρ
      (rationalArithmeticInertia a P).subtype continuous_subtype_val).ker

/-- The actual cocycle of the original continuous lift satisfies these two linear conditions exactly when that whole lift has the prescribed residual determinant and kills the original inertia subgroup. -/
theorem arithmeticLocalFirstOrderCocycles_lift_iff (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    (⟨matrixFirstOrderCocycle ρ τ, matrixFirstOrderCocycle_continuous ρ hρ τ hτ⟩ :
        continuousMatrixAdjointCocycles ρ) ∈ arithmeticLocalFirstOrderCocycles a ρ P ↔
      (∀ g, Matrix.det (τ.val g).val = TrivSqZeroExt.inl (Matrix.det (ρ g).val)) ∧
        rationalArithmeticInertia a P ≤ τ.val.ker := by
  constructor
  · rintro ⟨ht, hI⟩
    refine ⟨(matrixFirstOrderLift_fixedDeterminant_iff ρ τ).mpr ?_, ?_⟩
    · intro g
      exact congrFun ht g
    · apply (matrixFirstOrderLift_subgroup_kernel_iff ρ τ _ hP).mpr
      intro g hg
      exact congrArg (fun c : continuousMatrixAdjointCocycles
        (ρ.comp (rationalArithmeticInertia a P).subtype) => c.val ⟨g, hg⟩) hI
  · rintro ⟨ht, hI⟩
    constructor
    · funext g
      exact (matrixFirstOrderLift_fixedDeterminant_iff ρ τ).mp ht g
    · apply Subtype.ext
      apply groupCohomology.cocycles₁_ext
      intro g
      exact (matrixFirstOrderLift_subgroup_kernel_iff ρ τ _ hP).mp hI g.val g.property

/-- The original local first-order representation gives its genuine continuous trace-zero inertia-vanishing cocycle. -/
def arithmeticLocalFirstOrderCocycle (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker)
    (τ : ArithmeticLocalFirstOrderLift a ρ P) : arithmeticLocalFirstOrderCocycles a ρ P :=
  ⟨⟨matrixFirstOrderCocycle ρ τ.val.val,
    matrixFirstOrderCocycle_continuous ρ hρ τ.val.val τ.val.property⟩,
      (arithmeticLocalFirstOrderCocycles_lift_iff a ρ hρ P hP τ.val.val τ.val.property).mpr
        τ.property⟩

/-- The same actual local first-order lifts are classified bijectively by their genuine continuous cocycles, before taking strict-conjugacy classes. -/
def arithmeticLocalFirstOrderCocycleEquiv (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker) :
    ArithmeticLocalFirstOrderLift a ρ P ≃ arithmeticLocalFirstOrderCocycles a ρ P where
  toFun := arithmeticLocalFirstOrderCocycle a ρ hρ P hP
  invFun c := by
    let τ := firstOrderLiftFromCocycle ρ c.val.val
    have hτ : Continuous τ.val := firstOrderLiftFromCocycle_continuous ρ hρ c.val.val c.val.property
    refine ⟨⟨τ, hτ⟩, (arithmeticLocalFirstOrderCocycles_lift_iff a ρ hρ P hP τ hτ).mp ?_⟩
    have hc : (⟨matrixFirstOrderCocycle ρ τ,
        matrixFirstOrderCocycle_continuous ρ hρ τ hτ⟩ : continuousMatrixAdjointCocycles ρ) =
          c.val := by
      apply Subtype.ext
      exact matrixFirstOrderCocycle_fromCocycle ρ c.val.val
    rw [hc]
    exact c.property
  left_inv τ := by
    apply Subtype.ext
    apply Subtype.ext
    exact firstOrderLiftFromCocycle_cocycle ρ τ.val.val
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact matrixFirstOrderCocycle_fromCocycle ρ c.val.val

/-- The actual local lift-to-cocycle correspondence is bijective on the entire original representations. -/
theorem arithmeticLocalFirstOrderCocycleEquiv_bijective (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker) :
    Function.Bijective (arithmeticLocalFirstOrderCocycleEquiv a ρ hρ P hP) :=
  (arithmeticLocalFirstOrderCocycleEquiv a ρ hρ P hP).bijective

end
end Dubon2026
