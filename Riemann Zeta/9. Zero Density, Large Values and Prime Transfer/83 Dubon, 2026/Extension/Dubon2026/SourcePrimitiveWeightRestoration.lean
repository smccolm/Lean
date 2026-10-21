import Dubon2026.SourcePrimitiveGaloisAlternative
import Dubon2026.SourceArithmeticWeightTwist
import Dubon2026.SourcePrimitiveWeightTwo

/-! DUB-17/18 -> residual Galois association -> restore the original
primitive form's exact Fourier coefficients and determinant weight.
The proved cyclotomic twist removes the weight-two factor, and the
original level divisibility restores every good prime of the original
level. Geometric realization of the parabolic alternative and original
arithmetic support comparison remain required.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
open CongruenceSubgroup groupCohomology SourceCuspBoundary
attribute [local instance] rationalPrimeLocalField_charZero rationalPrimeOriginalNorm
  rationalPrimeOriginalNorm_ultrametric rationalPrimeOriginalClosureNorm
  rationalPrimeOriginalClosureNormedAlgebra rationalPrimeOriginalClosureNorm_ultrametric
  algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
open scoped NumberField

variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- The original primitive form supplies a weight-two class satisfying the
parabolic-lift alternative or a genuine residual Galois representation with the
original Fourier coefficients, original good primes and exact weight determinant. -/
theorem sourcePrimitive_exists_parabolicLift_or_residualGalois
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    {K : Type} [Field K] [IsAlgClosed K] [TopologicalSpace K] [IsTopologicalRing K] [Algebra 𝓀[E] K]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    ∃ (M : ℕ), Q ∣ M ∧ M ∣ Q * p ^ 2 ∧
      ∃ (values : sourceBinaryHeckePrime M → K)
        (y : H1 (Rep.trivial K (Gamma0 M) K)), y ≠ 0 ∧
        (∀ ell : sourceBinaryHeckePrime M,
          algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
            ⟨cuspHeckeLinear Q k ell.val, Algebra.subset_adjoin
              ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩) =
            (ell.val : K) ^ ((k - 2).toNat / 2) * values ell) ∧
        (∀ ell, sourceTrivialCoefficientHeckeOperators K M ell y = values ell • y) ∧
        ((∃ (θ : sourceBinaryHeckePrime M → integralClosure ℤ ℂ)
          (φ : integralClosure ℤ ℂ →+* K)
          (v : H1 (Rep.trivial ℂ (Gamma0 M) ℂ)), v ≠ 0 ∧
          (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 M) ℂ)).hom v ∈ parabolicHoms M ∧
          (∀ ell, sourceTrivialCoefficientHeckeOperators ℂ M ell v = (θ ell : ℂ) • v) ∧
          ∀ ell, φ (θ ell) = values ell) ∨
          (let a : 𝓞 ℚ := (M * p : ℕ)
           ∃ ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) (K),
             Continuous ρ ∧
             (∀ (ell : sourceBinaryHeckePrime Q), ell.val ≠ p →
               ∀ g : Gal(rationalPrimeLocalClosure ell.val ell.property.1 /
                 rationalPrimeLocalField ell.val ell.property.1),
                 (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
                   (rationalPrimeLocalClosure ell.val ell.property.1)), g • z = z ^ ell.val) →
                 Matrix.trace (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
                   algebraMap 𝓀[E] K (IsLocalRing.residue 𝒪[E]
                     ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
                       sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩) ∧
                 Matrix.det (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
                   (ell.val : K) ^ (k - 1).toNat) ∧
             ∀ (ell : ℕ) (hell : ell.Prime), ¬ell ∣ Q → ell ≠ p →
               ∀ g ∈ rationalPrimeNormInertia ell hell,
                 ρ (rationalPrimeArithmeticRestriction a ell hell g) = 1)) := by
  obtain ⟨M, hQM, hM, values, y, hy, hvalues, heig, halt⟩ :=
    sourcePrimitive_exists_weightTwo_parabolicLift_or_galoisRep (K := K) p hp f hk τ
  refine ⟨M, hQM, hM, values, y, hy, hvalues, heig, ?_⟩
  rcases halt with hlift | ⟨ρ, hρ, hFrob, hI⟩
  · exact Or.inl hlift
  right
  letI : NeZero p := ⟨hp.ne_zero⟩
  let a : 𝓞 ℚ := (M * p : ℕ)
  have hpa : (p : 𝓞 ℚ) ∣ a := ⟨(M : 𝓞 ℚ), by simp [a, mul_comm]⟩
  let j := (k - 2).toNat / 2
  have hweight : 2 * j + 1 = (k - 1).toNat := by
    obtain ⟨n, hn⟩ := sourcePrimitive_binaryDegree_even f hk
    dsimp [j]
    omega
  have hgood (ell : ℕ) (hell : ell.Prime) (hellQ : ¬ell ∣ Q) (hellp : ell ≠ p) :
      ¬ell ∣ M := by
    intro hd
    rcases hell.dvd_mul.mp (hd.trans hM) with hQ | hp2
    · exact hellQ hQ
    · exact hellp ((Nat.prime_dvd_prime_iff_eq hell hp).mp (hell.dvd_of_dvd_pow hp2))
  refine ⟨sourceArithmeticWeightTwist p a hpa j ρ,
    sourceArithmeticWeightTwist_continuous p a hpa j ρ hρ, ?_, ?_⟩
  · intro ell hellp g hg
    have hellQ := ell.property.1.coprime_iff_not_dvd.mp ell.property.2
    have hellM := hgood ell.val ell.property.1 hellQ hellp
    let ellM : sourceBinaryHeckePrime M :=
      ⟨ell.val, ell.property.1, ell.property.1.coprime_iff_not_dvd.mpr hellM⟩
    have hv := hFrob ellM hellp g hg
    refine ⟨?_, ?_⟩
    · rw [sourceArithmeticWeightTwist_frobenius_trace p a hpa j ρ hp
        ell.val ell.property.1 hellp g hg, hv.1]
      have hc := hvalues ellM
      exact hc.symm.trans (congrArg (algebraMap 𝓀[E] K)
        (sourcePrimitiveResidualHeckeCharacter_hecke f hk τ
          ⟨ell.val, ell.property.1.pos⟩))
    · rw [sourceArithmeticWeightTwist_frobenius_det p a hpa j ρ hp
        ell.val ell.property.1 hellp g hg, hv.2, ← pow_succ, hweight]
  · intro ell hell hellQ hellp g hg
    exact sourceArithmeticWeightTwist_inertia p a hpa j ρ hp ell hell hellp g hg
      (hI ell hell (hgood ell hell hellQ hellp) hellp g hg)

end
end Dubon2026
