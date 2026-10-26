import Dubon2026.SourceOriginalNormLocalResidual
import Dubon2026.SourceAbsoluteArithmeticDescent
import Dubon2026.SourceArithmeticLocalEmbeddingExtension

/-! DUB-17/18 -> original weight-two residual association.
The constructed prescribed reduction descends to the actual arithmetic
Galois group with the fixed original norm-local restrictions. The same
continuous representation has the exact good-prime characteristic
polynomial, trace, determinant, and trivial inertia. The parabolic
consumer and all-weight restoration remain separate source obligations. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open Matrix Polynomial
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
variable (N ell : ℕ) [NeZero N] (hell : ell.Prime) [Fact ell.Prime]
variable (K : Type) [Field K] [TopologicalSpace K] [DiscreteTopology K] [CharP K ell]
variable (f : PrimitiveCuspForm N 2) (φ : integralClosure ℤ ℂ →+* K)

include hell in
theorem originalPrimitive_prescribed_arithmetic_residual_realization :
    ∃ ρ : rationalArithmeticGaloisGroup (N * ell : ℕ) →* GeneralLinearGroup (Fin 2) K,
      Continuous ρ ∧ (Set.range ρ).Finite ∧
      ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ N * ell →
        (∀ g ∈ rationalPrimeNormInertia q hq,
          ρ (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g) = 1) ∧
        ∀ g : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq),
          (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing (rationalPrimeLocalClosure q hq)),
            g • z = z ^ q) →
          let a : integralClosure ℤ ℂ := ⟨cuspCoefficients f.toCuspForm q,
            sourcePrimitiveCoefficient_isIntegral f (by norm_num) q⟩
          (ρ (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g)).val.charpoly =
              X ^ 2 - C (φ a) * X + C (q : K) ∧
            (ρ (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g)).val.trace = φ a ∧
            (ρ (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g)).val.det = (q : K) := by
  have hsrc := originalPrimitive_prescribed_normLocal_residual_realization N ell hell K f φ
  rcases hsrc with ⟨ρ, hc, _, hlocal⟩
  let χ : Gal(Qbar/ℚ) →ₜ* GeneralLinearGroup (Fin 2) K := ⟨ρ, hc⟩
  obtain ⟨η, hη⟩ := absolute_continuous_normInertia_arithmetic_descent (N * ell) χ
    (fun q hq hqN e g hg => (hlocal q hq hqN e).1 g hg)
  refine ⟨η.toMonoidHom, η.continuous, (isCompact_range η.continuous).finite_of_discrete, ?_⟩
  intro q hq hqN
  obtain ⟨e, he⟩ := sourceArithmeticLocalEmbedding_exists_extension (N * ell : ℕ) q hq
  have hs (g : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)) :
      η (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g) =
        ρ (embeddedNormalGaloisRestriction e g) := by
    rw [← sourceAbsoluteArithmeticRestriction_local (N * ell : ℕ) q hq e he g]
    exact hη _
  constructor
  · intro g hg
    change η (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g) = 1
    rw [hs]
    exact (hlocal q hq hqN e).1 g hg
  · intro g hg
    change (η (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g)).val.charpoly = _ ∧
      (η (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g)).val.trace = _ ∧
      (η (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g)).val.det = _
    rw [hs]
    exact (hlocal q hq hqN e).2 g hg

end
end Dubon2026.SourceFunctionField.OriginalChart
