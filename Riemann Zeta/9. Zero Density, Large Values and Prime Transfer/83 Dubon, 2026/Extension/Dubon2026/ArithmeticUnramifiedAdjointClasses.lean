import Dubon2026.RationalArithmeticInertia
import Dubon2026.ContinuousAdjointRestriction
import Dubon2026.ArithmeticContinuousAdjointFinite

/-! # Actual unramified local conditions on arithmetic adjoint classes -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- The actual unramified local condition: the kernel of restriction of original continuous arithmetic adjoint classes to the original inertia subgroup. -/
def arithmeticUnramifiedAdjointClasses (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Submodule R (ContinuousMatrixAdjointH1 ρ hρ) :=
  (continuousMatrixAdjointH1Restriction ρ hρ
    (rationalArithmeticInertia a P).subtype continuous_subtype_val).ker

/-- The class of an original first-order arithmetic lift satisfies the actual unramified condition exactly when its original cocycle on genuine inertia is an original adjoint coboundary. -/
theorem arithmeticUnramifiedAdjointClasses_firstOrder_iff (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ ∈ arithmeticUnramifiedAdjointClasses a ρ hρ P ↔
      ∃ X : Matrix ι ι R, ∀ σ : rationalArithmeticInertia a P,
        (ρ σ.val).val * X * (ρ σ.val⁻¹).val - X = matrixFirstOrderCocycle ρ τ σ.val := by
  change (Submodule.Quotient.mk
    (continuousMatrixAdjointRestriction ρ (rationalArithmeticInertia a P).subtype
      continuous_subtype_val ⟨matrixFirstOrderCocycle ρ τ,
        matrixFirstOrderCocycle_continuous ρ hρ τ hτ⟩) :
      ContinuousMatrixAdjointH1 (ρ.comp (rationalArithmeticInertia a P).subtype)
        (hρ.comp continuous_subtype_val)) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨X, ?_⟩
    intro σ
    exact congrArg (fun c : continuousMatrixAdjointCocycles
      (ρ.comp (rationalArithmeticInertia a P).subtype) => c.val σ) hX
  · rintro ⟨X, hX⟩
    refine ⟨X, ?_⟩
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro σ
    exact hX σ

/-- Outside the original exceptional integer the actual local unramified condition contains every original continuous arithmetic adjoint class, because original inertia is proved trivial. -/
theorem arithmeticUnramifiedAdjointClasses_eq_top (a : 𝓞 ℚ) (ha : a ≠ 0)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R) (hρ : Continuous ρ) :
    (let U := rationalUnramifiedExtension a
     letI : Algebra ℚ U := U.algebra'
     ∀ (P : Ideal (𝓞 U)), P.IsPrime → P ≠ ⊥ →
       algebraMap (𝓞 ℚ) (𝓞 U) a ∉ P → arithmeticUnramifiedAdjointClasses a ρ hρ P = ⊤) := by
  dsimp only
  intro P hprime hP haP
  have hI := rationalArithmeticInertia_eq_bot a ha P hprime hP haP
  apply top_unique
  intro c _
  obtain ⟨⟨τ, hτ⟩, rfl⟩ := continuousMatrixFirstOrderClass_surjective ρ hρ c
  apply (arithmeticUnramifiedAdjointClasses_firstOrder_iff a ρ hρ P τ hτ).mpr
  refine ⟨0, ?_⟩
  intro σ
  have hσ : σ.val = 1 := (le_of_eq hI) σ.property
  rw [hσ]
  simp only [mul_zero, zero_mul, sub_self, groupCohomology.cocycles₁_map_one]

/-- The actual unramified adjoint local condition is finite dimensional for every original continuous finite-field arithmetic representation. Its ambient arithmetic H1 finiteness is derived. -/
theorem arithmeticUnramifiedAdjointClasses_finiteDimensional
    (K : Type) [Field K] [Finite K] [TopologicalSpace K] [DiscreteTopology K]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Module.Finite K (arithmeticUnramifiedAdjointClasses a ρ hρ P) := by
  letI := arithmeticContinuousAdjointH1_finite a ha p hp hpa ρ hρ
  letI : Finite (arithmeticUnramifiedAdjointClasses a ρ hρ P) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Module.Finite.of_finite

end
end Dubon2026
