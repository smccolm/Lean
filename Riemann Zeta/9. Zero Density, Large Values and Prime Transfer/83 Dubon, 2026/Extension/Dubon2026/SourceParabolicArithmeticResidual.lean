import Dubon2026.SourceParabolicPrimitiveDivisor
import Dubon2026.SourceOriginalDivisorArithmeticResidual

/-! DUB-17/18 -> close the actual weight-two parabolic branch.
The original parabolic H1 eigensystem supplies a genuine primitive
form at a dividing level. Its actual prescribed reduction gives the
arithmetic representation, inflated to the original support with exact
local polynomial and inertia properties. No geometric-lift or residual
association assumption remains in this branch. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology SourceCuspBoundary Matrix Polynomial
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

theorem sourceTrivialParabolicEigen_prescribed_galoisRep
    (N p : ℕ) [NeZero N] (hp : p.Prime)
    (K : Type) [Field K] [TopologicalSpace K] [DiscreteTopology K] [CharP K p]
    (θ : sourceBinaryHeckePrime N → integralClosure ℤ ℂ)
    (φ : integralClosure ℤ ℂ →+* K)
    (v : H1 (Rep.trivial ℂ (Gamma0 N) ℂ)) (hv : v ≠ 0)
    (hpar : (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).hom v ∈ parabolicHoms N)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators ℂ N ell v = (θ ell : ℂ) • v) :
    ∃ ρ : rationalArithmeticGaloisGroup (N * p : ℕ) →* GeneralLinearGroup (Fin 2) K,
      Continuous ρ ∧ (Set.range ρ).Finite ∧
      (∀ ell : sourceBinaryHeckePrime N, ell.val ≠ p →
        ∀ g : Gal(rationalPrimeLocalClosure ell.val ell.property.1 /
          rationalPrimeLocalField ell.val ell.property.1),
          (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
            (rationalPrimeLocalClosure ell.val ell.property.1)), g • z = z ^ ell.val) →
          (ρ (rationalPrimeArithmeticRestriction (N * p : ℕ) ell.val ell.property.1 g)).val.charpoly =
              X ^ 2 - C (φ (θ ell)) * X + C (ell.val : K) ∧
            (ρ (rationalPrimeArithmeticRestriction (N * p : ℕ) ell.val ell.property.1 g)).val.trace =
              φ (θ ell) ∧
            (ρ (rationalPrimeArithmeticRestriction (N * p : ℕ) ell.val ell.property.1 g)).val.det =
              (ell.val : K)) ∧
      ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ N → q ≠ p →
        ∀ g ∈ rationalPrimeNormInertia q hq,
          ρ (rationalPrimeArithmeticRestriction (N * p : ℕ) q hq g) = 1 := by
  have hprim := sourceTrivialParabolicEigen_exists_primitive_divisor N
    (fun ell => (θ ell : ℂ)) v hv hpar heig
  rcases hprim with ⟨M, hM, hMN, f, hcoeff⟩
  letI := hM
  letI : Fact p.Prime := ⟨hp⟩
  have hsrc := SourceFunctionField.OriginalChart.originalPrimitive_divisor_arithmetic_residual_realization
    N M p hp K hMN f φ
  rcases hsrc with ⟨ρ, hc, hf, hlocal⟩
  have hnot (q : ℕ) (hq : q.Prime) (hqN : ¬q ∣ N) (hqp : q ≠ p) :
      ¬q ∣ N * p := by
    intro h
    rcases hq.dvd_mul.mp h with hN | hp'
    · exact hqN hN
    · exact hqp ((Nat.dvd_prime hp).mp hp' |>.resolve_left hq.ne_one)
  refine ⟨ρ, hc, hf, ?_, ?_⟩
  · intro ell hep g hg
    have hbad := hnot ell.val ell.property.1
      (ell.property.1.coprime_iff_not_dvd.mp ell.property.2) hep
    have hh := (hlocal ell.val ell.property.1 hbad).2 g hg
    have hec : (⟨cuspCoefficients f.toCuspForm ell.val,
        sourcePrimitiveCoefficient_isIntegral f (by norm_num) ell.val⟩ :
        integralClosure ℤ ℂ) = θ ell := Subtype.ext (hcoeff ell)
    dsimp only at hh
    rwa [hec] at hh
  · intro q hq hqN hqp g hg
    exact (hlocal q hq (hnot q hq hqN hqp)).1 g hg

end
end Dubon2026
