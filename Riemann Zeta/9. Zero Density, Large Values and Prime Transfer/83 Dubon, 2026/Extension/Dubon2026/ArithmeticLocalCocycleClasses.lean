import Dubon2026.ArithmeticLocalFirstOrderCocycles
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Genuine local cocycle classes and their actual coboundary kernel -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- The actual quotient class of an original local cocycle lies in the genuine simultaneous determinant and inertia condition. -/
def arithmeticLocalCocycleClassLinearMap (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    arithmeticLocalFirstOrderCocycles a ρ P →ₗ[R]
      arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P where
  toFun c := ⟨Submodule.Quotient.mk c.val, by
    refine ⟨c.property.1, ?_⟩
    change (Submodule.Quotient.mk
      (continuousMatrixAdjointRestriction ρ (rationalArithmeticInertia a P).subtype
        continuous_subtype_val c.val) :
          ContinuousMatrixAdjointH1 (ρ.comp (rationalArithmeticInertia a P).subtype)
            (hρ.comp continuous_subtype_val)) = 0
    rw [c.property.2]
    rfl⟩
  map_add' c d := by
    apply Subtype.ext
    exact Submodule.Quotient.mk_add _
  map_smul' r c := by
    apply Subtype.ext
    exact Submodule.Quotient.mk_smul _ r c.val

/-- The actual linear cocycle class map retains the original entire first-order representation's class. -/
theorem arithmeticLocalCocycleClassLinearMap_lift (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker)
    (τ : ArithmeticLocalFirstOrderLift a ρ P) :
    arithmeticLocalCocycleClassLinearMap a ρ hρ P
      (arithmeticLocalFirstOrderCocycle a ρ hρ P hP τ) =
        arithmeticLocalFirstOrderClass a ρ hρ P hP τ := rfl

/-- Every original local cohomology class is the genuine quotient class of an actual local continuous cocycle. -/
theorem arithmeticLocalCocycleClassLinearMap_surjective (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker) :
    Function.Surjective (arithmeticLocalCocycleClassLinearMap a ρ hρ P) := by
  intro x
  obtain ⟨τ, hτ⟩ := arithmeticLocalFirstOrderClass_surjective a ρ hρ P hP x
  exact ⟨arithmeticLocalFirstOrderCocycle a ρ hρ P hP τ, hτ⟩

/-- The kernel of the actual local class map consists precisely of the original full-adjoint continuous coboundaries lying in the genuine local cocycles. -/
theorem arithmeticLocalCocycleClassLinearMap_ker (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    (arithmeticLocalCocycleClassLinearMap a ρ hρ P).ker =
      (continuousMatrixAdjointCoboundaries ρ hρ).comap
        (arithmeticLocalFirstOrderCocycles a ρ P).subtype := by
  ext c
  rw [LinearMap.mem_ker, Subtype.ext_iff]
  change (Submodule.Quotient.mk c.val : ContinuousMatrixAdjointH1 ρ hρ) = 0 ↔
    c.val ∈ continuousMatrixAdjointCoboundaries ρ hρ
  exact Submodule.Quotient.mk_eq_zero _

/-- Residual triviality on the original inertia subgroup makes every genuine adjoint coboundary an actual local trace-zero inertia-vanishing cocycle. -/
theorem continuousMatrixAdjointCoboundaries_le_arithmeticLocalFirstOrderCocycles
    (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker) :
    continuousMatrixAdjointCoboundaries ρ hρ ≤ arithmeticLocalFirstOrderCocycles a ρ P := by
  rintro _ ⟨X, rfl⟩
  refine ⟨continuousMatrixAdjointTrace_coboundary ρ hρ X, ?_⟩
  apply Subtype.ext
  apply groupCohomology.cocycles₁_ext
  intro g
  change (ρ g.val).val * X * (ρ g.val⁻¹).val - X = 0
  have hg : ρ g.val = 1 := hP g.property
  rw [map_inv, hg, inv_one, Units.val_one, one_mul, mul_one, sub_self]

end

noncomputable section
open Matrix
open scoped NumberField

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
  [TopologicalSpace K] [DiscreteTopology K]

/-- The actual local first-order cocycles are finite-dimensional by the proved finiteness of the original arithmetic continuous cocycles. -/
theorem arithmeticLocalFirstOrderCocycles_finiteDimensional
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Module.Finite K (arithmeticLocalFirstOrderCocycles a ρ P) := by
  letI := arithmeticContinuousAdjointCocycles_finite a ha p hp hpa ρ hρ
  letI : Finite (arithmeticLocalFirstOrderCocycles a ρ P) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Module.Finite.of_finite

/-- The genuine local cocycle dimension is the sum of the actual local cohomology dimension and the dimension of the original continuous adjoint coboundaries. -/
theorem arithmeticLocalFirstOrderCocycles_finrank
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker) :
    Module.finrank K (arithmeticLocalFirstOrderCocycles a ρ P) =
      Module.finrank K (arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P) +
        Module.finrank K (continuousMatrixAdjointCoboundaries ρ hρ) := by
  letI : AddCommGroup (groupCohomology.cocycles₁ (matrixAdjointRep ρ)) :=
    (groupCohomology.cocycles₁ (matrixAdjointRep ρ)).addCommGroup
  letI : AddCommGroup (continuousMatrixAdjointCocycles ρ) :=
    (continuousMatrixAdjointCocycles ρ).addCommGroup
  letI : AddCommGroup (arithmeticLocalFirstOrderCocycles a ρ P) :=
    Submodule.addCommGroup (R := K) (M := continuousMatrixAdjointCocycles ρ)
      (arithmeticLocalFirstOrderCocycles a ρ P)
  letI := arithmeticLocalFirstOrderCocycles_finiteDimensional a ha p hp hpa ρ hρ P
  have hk : Module.finrank K (arithmeticLocalCocycleClassLinearMap a ρ hρ P).ker =
      Module.finrank K (continuousMatrixAdjointCoboundaries ρ hρ) := by
    rw [arithmeticLocalCocycleClassLinearMap_ker]
    exact (Submodule.comapSubtypeEquivOfLe
      (continuousMatrixAdjointCoboundaries_le_arithmeticLocalFirstOrderCocycles a ρ hρ P hP)).finrank_eq
  have h := LinearMap.finrank_range_add_finrank_ker (arithmeticLocalCocycleClassLinearMap a ρ hρ P)
  rw [LinearMap.range_eq_top.mpr
    (arithmeticLocalCocycleClassLinearMap_surjective a ρ hρ P hP), finrank_top, hk] at h
  exact h.symm

end
end Dubon2026
