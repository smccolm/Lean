import Dubon2026.ArithmeticFirstOrderFinite
import Dubon2026.ContinuousAdjointCohomology
import Mathlib.RingTheory.Finiteness.Basic

/-! # Actual finite continuous arithmetic adjoint cocycles and first cohomology -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
  [TopologicalSpace K] [DiscreteTopology K]

/-- The actual continuous adjoint cocycles of the original finite-field arithmetic representation form a finite set. Every such cocycle is realized by the original continuous first-order construction. -/
theorem arithmeticContinuousAdjointCocycles_finite
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    Finite (continuousMatrixAdjointCocycles ρ) := by
  letI := arithmeticContinuousFirstOrderLift_finite a ha p hp hpa ρ hρ
  let F : {τ : MatrixFirstOrderLift ρ // Continuous τ.val} →
      continuousMatrixAdjointCocycles ρ := fun τ =>
    ⟨matrixFirstOrderCocycle ρ τ.val,
      matrixFirstOrderCocycle_continuous ρ hρ τ.val τ.property⟩
  apply Finite.of_surjective F
  intro c
  refine ⟨⟨firstOrderLiftFromCocycle ρ c.val,
    firstOrderLiftFromCocycle_continuous ρ hρ c.val c.property⟩, ?_⟩
  apply Subtype.ext
  exact matrixFirstOrderCocycle_fromCocycle ρ c.val

/-- The actual continuous first adjoint cohomology of the original arithmetic representation is finite. It is the proved original cocycle quotient by genuine continuous coboundaries. -/
theorem arithmeticContinuousAdjointH1_finite
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    Finite (ContinuousMatrixAdjointH1 ρ hρ) := by
  letI := arithmeticContinuousFirstOrderLift_finite a ha p hp hpa ρ hρ
  exact Finite.of_surjective
    (fun τ : {τ : MatrixFirstOrderLift ρ // Continuous τ.val} =>
      continuousMatrixFirstOrderClass ρ hρ τ.val τ.property)
    (continuousMatrixFirstOrderClass_surjective ρ hρ)

/-- The original continuous arithmetic adjoint cohomology is finite dimensional over its actual original finite coefficient field. -/
theorem arithmeticContinuousAdjointH1_finiteDimensional
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    Module.Finite K (ContinuousMatrixAdjointH1 ρ hρ) := by
  letI := arithmeticContinuousAdjointH1_finite a ha p hp hpa ρ hρ
  exact Module.Finite.of_finite

end
end Dubon2026
