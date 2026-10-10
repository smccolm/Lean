import Dubon2026.ArithmeticUnramifiedAdjointClasses
import Dubon2026.FirstOrderInertiaCriterion

/-! # Actual first-order unramified representations and original arithmetic local classes -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- For an original arithmetic representation unramified at the genuine chosen inertia subgroup, its first-order lift class lies in the actual unramified adjoint local condition exactly when that same original lifted representation kills the entire actual inertia subgroup. -/
theorem arithmeticUnramifiedAdjointClasses_firstOrder_inertia_iff
    (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P ≤ ρ.ker)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ ∈ arithmeticUnramifiedAdjointClasses a ρ hρ P ↔
      rationalArithmeticInertia a P ≤ τ.val.ker := by
  rw [arithmeticUnramifiedAdjointClasses_firstOrder_iff,
    matrixFirstOrderLift_subgroup_kernel_iff ρ τ _ hP]
  constructor
  · rintro ⟨X, hX⟩ g hg
    have he := hX ⟨g, hg⟩
    have hρg : ρ g = 1 := hP hg
    have hρgi : ρ g⁻¹ = 1 := by rw [map_inv, hρg, inv_one]
    simpa only [hρg, hρgi, Units.val_one, one_mul, mul_one, sub_self] using he.symm
  · intro h
    refine ⟨0, ?_⟩
    intro σ
    simp only [mul_zero, zero_mul, sub_self, h σ.val σ.property]

end
end Dubon2026
