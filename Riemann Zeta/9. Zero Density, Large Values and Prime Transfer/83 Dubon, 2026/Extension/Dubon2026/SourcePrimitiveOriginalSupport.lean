import Dubon2026.SourcePrimitiveWeightRestoration
import Dubon2026.SourceArithmeticSupportLocalValues

/-! DUB-17/18 -> residual Galois association -> original arithmetic support.
The actual source level bounds give equality of the original arithmetic
extensions. Existing local conjugacy transports the exact restored
Fourier coefficients, determinant exponent and inertia to support Qp.
The alternative parabolic complex class still requires geometric realization.
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
original Fourier coefficients, original good primes, exact weight determinant and original support. -/
theorem sourcePrimitive_exists_originalSupport_parabolicLift_or_residualGalois
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
          (let a : 𝓞 ℚ := (Q * p : ℕ)
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
    sourcePrimitive_exists_parabolicLift_or_residualGalois (K := K) p hp f hk τ
  refine ⟨M, hQM, hM, values, y, hy, hvalues, heig, ?_⟩
  rcases halt with hlift | ⟨ρ, hρ, hFrob, hI⟩
  · exact Or.inl hlift
  right
  let a : 𝓞 ℚ := (Q * p : ℕ)
  let b : 𝓞 ℚ := (M * p : ℕ)
  have hab : a ∣ b := by
    obtain ⟨c, hc⟩ := Nat.mul_dvd_mul_right hQM p
    exact ⟨(c : 𝓞 ℚ), by dsimp [a, b]; exact_mod_cast hc⟩
  obtain ⟨η, hη⟩ := sourceArithmeticSupport_exists_representation a b hab
    (sourceWeightTwo_arithmeticExtension_eq hQM hM) ⟨ρ, hρ⟩
  refine ⟨η.toMonoidHom, η.continuous, ?_, ?_⟩
  · intro ell hellp g hg
    have hv := hFrob ell hellp g hg
    exact ⟨(sourceArithmeticSupport_local_trace a b hab η.toMonoidHom ρ hη
      ell.val ell.property.1 g).trans hv.1,
      (sourceArithmeticSupport_local_det a b hab η.toMonoidHom ρ hη
        ell.val ell.property.1 g).trans hv.2⟩
  · intro ell hell hellQ hellp g hg
    exact sourceArithmeticSupport_local_eq_one a b hab η.toMonoidHom ρ hη
      ell hell g (hI ell hell hellQ hellp g hg)

end
end Dubon2026
