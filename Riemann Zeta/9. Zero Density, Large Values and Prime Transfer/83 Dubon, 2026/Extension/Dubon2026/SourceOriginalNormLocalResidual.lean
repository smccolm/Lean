import Dubon2026.SourceOriginalAlgebraicIntegerResidual
import Dubon2026.SourceRationalLocalValuation

/-! DUB-17/18 -> prescribed residual association -> the actual original
norm-local interfaces. One finite-image continuous original residual
representation has the required inertia and Frobenius identities through
every genuine global-to-local embedding. The fixed arithmetic quotient
and its chosen embeddings remain to be assembled by finite-field descent. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open Matrix Polynomial
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
variable (N ell : ℕ) [NeZero N] (hell : ell.Prime) [Fact ell.Prime]
variable (K : Type) [Field K] [TopologicalSpace K] [CharP K ell]
variable (f : PrimitiveCuspForm N 2) (φ : integralClosure ℤ ℂ →+* K)

include hell in
theorem originalPrimitive_prescribed_normLocal_residual_realization :
    ∃ ρ : Gal(Qbar/ℚ) →* GeneralLinearGroup (Fin 2) K,
      Continuous ρ ∧ (Set.range ρ).Finite ∧
      ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ N * ell →
        ∀ e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq,
          (∀ g ∈ rationalPrimeNormInertia q hq,
            ρ (embeddedNormalGaloisRestriction e g) = 1) ∧
          ∀ g : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq),
            (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing (rationalPrimeLocalClosure q hq)),
              g • z = z ^ q) →
            let a : integralClosure ℤ ℂ := ⟨cuspCoefficients f.toCuspForm q,
              sourcePrimitiveCoefficient_isIntegral f (by norm_num) q⟩
            (ρ (embeddedNormalGaloisRestriction e g)).val.charpoly =
                X ^ 2 - C (φ a) * X + C (q : K) ∧
              (ρ (embeddedNormalGaloisRestriction e g)).val.trace = φ a ∧
              (ρ (embeddedNormalGaloisRestriction e g)).val.det = (q : K) := by
  have hsrc := originalPrimitive_algebraicInteger_reduction_residual_realization N ell hell K f φ
  rcases hsrc with ⟨ρ, hc, hf, hi, hfr⟩
  refine ⟨ρ, hc, hf, ?_⟩
  intro q hq hNq e
  constructor
  · intro g hg
    exact hi q hq hNq (sourceRationalLocalValuation q hq e)
      (sourceRationalLocalValuation_prime q hq e) (embeddedNormalGaloisRestriction e g)
      (sourceRationalLocalValuation_inertia q hq e g hg)
  · intro g hg
    exact hfr q hq hNq (sourceRationalLocalValuation q hq e)
      (sourceRationalLocalValuation_prime q hq e) (embeddedNormalGaloisRestriction e g)
      (sourceRationalLocalValuation_frobenius q hq e g hg)

end
end Dubon2026.SourceFunctionField.OriginalChart
