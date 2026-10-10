import Dubon2026.ContinuousTraceZeroRestriction
import Dubon2026.ArithmeticUnramifiedFixedDeterminantClasses

/-! # The actual inertia condition in continuous trace-zero arithmetic cohomology -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace K] [IsTopologicalRing K]

/-- The genuine unramified trace-zero condition is the kernel of restriction to the original arithmetic inertia subgroup. -/
def arithmeticUnramifiedTraceZeroClasses (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Submodule K (ContinuousTraceZeroAdjointH1 ρ hρ) :=
  (continuousTraceZeroH1Restriction ρ hρ
    (rationalArithmeticInertia a P).subtype continuous_subtype_val).ker

/-- Include actual unramified trace-zero classes in the original simultaneous determinant and inertia condition. -/
def arithmeticUnramifiedTraceZeroToFixedDeterminant (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    arithmeticUnramifiedTraceZeroClasses a ρ hρ P →ₗ[K]
      arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P where
  toFun x := ⟨continuousTraceZeroH1Inclusion ρ hρ x.val, by
    refine ⟨continuousTraceZeroH1Inclusion_mem ρ hρ x.val, ?_⟩
    change continuousMatrixAdjointH1Restriction ρ hρ
      (rationalArithmeticInertia a P).subtype continuous_subtype_val
        (continuousTraceZeroH1Inclusion ρ hρ x.val) = 0
    rw [← continuousTraceZeroH1Restriction_inclusion, x.property, map_zero]⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (continuousTraceZeroH1Inclusion ρ hρ) x.val y.val
  map_smul' r x := by
    apply Subtype.ext
    exact map_smul (continuousTraceZeroH1Inclusion ρ hρ) r x.val

/-- The genuine local trace-zero comparison is injective when the original matrix dimension is nonzero in the coefficient field. -/
theorem arithmeticUnramifiedTraceZeroToFixedDeterminant_injective
    (hn : (Fintype.card ι : K) ≠ 0) (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Function.Injective (arithmeticUnramifiedTraceZeroToFixedDeterminant a ρ hρ P) := by
  intro x y h
  apply Subtype.ext
  apply continuousTraceZeroH1ToFixedDeterminant_injective hn ρ hρ
  apply Subtype.ext
  exact congrArg (fun z : arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P => z.val) h

/-- Every original simultaneous determinant and inertia class arises from the genuine trace-zero inertia kernel under the original nonzero-dimension condition. -/
theorem arithmeticUnramifiedTraceZeroToFixedDeterminant_surjective
    (hn : (Fintype.card ι : K) ≠ 0) (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Function.Surjective (arithmeticUnramifiedTraceZeroToFixedDeterminant a ρ hρ P) := by
  intro y
  obtain ⟨x, hx⟩ := continuousTraceZeroH1ToFixedDeterminant_surjective ρ hρ
    ⟨y.val, y.property.1⟩
  have hxval : continuousTraceZeroH1Inclusion ρ hρ x = y.val := congrArg Subtype.val hx
  have hI : x ∈ arithmeticUnramifiedTraceZeroClasses a ρ hρ P := by
    apply (continuousTraceZeroH1Restriction_eq_zero_iff hn ρ hρ
      (rationalArithmeticInertia a P).subtype continuous_subtype_val x).mpr
    rw [hxval]
    exact y.property.2
  exact ⟨⟨x, hI⟩, Subtype.ext hxval⟩

/-- Actual trace-zero inertia classes and the original fixed-determinant unramified classes are linearly equivalent under the explicit dimension condition. -/
def arithmeticUnramifiedTraceZeroFixedDeterminantEquiv
    (hn : (Fintype.card ι : K) ≠ 0) (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    arithmeticUnramifiedTraceZeroClasses a ρ hρ P ≃ₗ[K]
      arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P :=
  LinearEquiv.ofBijective (arithmeticUnramifiedTraceZeroToFixedDeterminant a ρ hρ P)
    ⟨arithmeticUnramifiedTraceZeroToFixedDeterminant_injective hn a ρ hρ P,
      arithmeticUnramifiedTraceZeroToFixedDeterminant_surjective hn a ρ hρ P⟩

/-- The actual local trace-zero comparison retains the same original full-adjoint cohomology class. -/
theorem arithmeticUnramifiedTraceZeroFixedDeterminantEquiv_apply
    (hn : (Fintype.card ι : K) ≠ 0) (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a)))
    (x : arithmeticUnramifiedTraceZeroClasses a ρ hρ P) :
    (arithmeticUnramifiedTraceZeroFixedDeterminantEquiv hn a ρ hρ P x).val =
      continuousTraceZeroH1Inclusion ρ hρ x.val := rfl

/-- The genuine trace-zero inertia kernel has exactly the dimension of the same original simultaneous determinant and inertia condition. -/
theorem arithmeticUnramifiedTraceZeroClasses_finrank
    (hn : (Fintype.card ι : K) ≠ 0) (a : 𝓞 ℚ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Module.finrank K (arithmeticUnramifiedTraceZeroClasses a ρ hρ P) =
      Module.finrank K (arithmeticUnramifiedFixedDeterminantClasses a ρ hρ P) :=
  (arithmeticUnramifiedTraceZeroFixedDeterminantEquiv hn a ρ hρ P).finrank_eq

/-- The actual trace-zero inertia kernel is finite-dimensional using the proved finiteness of the original arithmetic cohomology. -/
theorem arithmeticUnramifiedTraceZeroClasses_finiteDimensional
    [Finite K] [DiscreteTopology K] (hn : (Fintype.card ι : K) ≠ 0)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Module.Finite K (arithmeticUnramifiedTraceZeroClasses a ρ hρ P) := by
  letI := arithmeticUnramifiedFixedDeterminantClasses_finiteDimensional K a ha p hp hpa ρ hρ P
  exact Module.Finite.equiv
    (arithmeticUnramifiedTraceZeroFixedDeterminantEquiv hn a ρ hρ P).symm

end
end Dubon2026
