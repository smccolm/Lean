import Dubon2026.FiniteBaseCMSymmetricRepresentation
import Dubon2026.PolarizedContinuousFirstOrder
import Dubon2026.FiniteSymmetricIrreducible

/-! The actual odd rank-two arithmetic representation feeds the continuous
polarized tangent classification. The source residue characteristic bound
discharges factorial nonvanishing; the original CM restriction retains the
literal homogeneous symmetric-power adjoint. This supplies the coefficient
and tangent input to DUB-17's still-open local crystalline/Hecke comparison. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the arithmetic tangent consumer. -/
local instance finiteBaseCMSymmetricTangentUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  {L : Type} [Field L] [Finite L] [TopologicalSpace L] [DiscreteTopology L]
  (q n : ℕ) [Fact q.Prime] [CharP L q] (hn : n < q)
  (ρ : finiteBaseArithmeticGaloisGroup a F →ₜ* GeneralLinearGroup (Fin 2) L)
  (hodd : (ρ (finiteBaseRealConjugation a F)).val.det = -1)

/-- The actual symmetric-power continuous fiber is classified by the original continuous full adjoint cocycles. -/
def finiteBaseCMSymmetricFirstOrderEquiv :
    ContinuousPolarizedFirstOrderLift
      (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
        (factorial_cast_ne_zero_of_lt_char q n hn) hodd).toMonoidHom ≃
      continuousRepresentationCocyclesOne (polarizedAdjointRep
        (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
          (factorial_cast_ne_zero_of_lt_char q n hn) hodd).toMonoidHom) :=
  continuousPolarizedFirstOrderLiftEquiv _
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
      (factorial_cast_ne_zero_of_lt_char q n hn) hodd).continuous

/-- The original CM subgroup acts on the tangent coefficients through the literal symmetric-power matrices. -/
theorem finiteBaseCMSymmetricAdjoint_kernel (g : FiniteBaseCMKernel a F K)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) L) :
    (polarizedAdjointRep (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
      (factorial_cast_ne_zero_of_lt_char q n hn) hodd).toMonoidHom).ρ g.val X =
      (homogeneousSymmetricGL n (ρ g.val)).val * X *
        (homogeneousSymmetricGL n (ρ g.val)).inv := by
  change polarizedAdjointRepresentation
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
      (factorial_cast_ne_zero_of_lt_char q n hn) hodd g.val) X = _
  rw [finiteBaseCMSymmetricPolarizedRepresentation_kernel, polarizedAdjointRepresentation_identity]

/-- The original arithmetic symmetric-power strict classes are exactly the continuous full-adjoint H1 classes. -/
theorem finiteBaseCMSymmetricFirstOrderClass_eq_iff
    (τ σ : ContinuousPolarizedFirstOrderLift
      (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
        (factorial_cast_ne_zero_of_lt_char q n hn) hodd).toMonoidHom) :
    continuousPolarizedFirstOrderClass _
      (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
        (factorial_cast_ne_zero_of_lt_char q n hn) hodd).continuous τ =
    continuousPolarizedFirstOrderClass _
      (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
        (factorial_cast_ne_zero_of_lt_char q n hn) hodd).continuous σ ↔
      PolarizedFirstOrderStrictlyConjugate _ τ.val σ.val :=
  continuousPolarizedFirstOrderClass_eq_iff _ _ τ σ

end
end Dubon2026
