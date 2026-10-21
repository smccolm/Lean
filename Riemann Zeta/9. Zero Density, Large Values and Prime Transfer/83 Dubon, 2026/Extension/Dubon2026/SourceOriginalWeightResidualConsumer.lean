import Dubon2026.SourcePrimitiveOriginalSupport
import Dubon2026.SourcePrimitiveWeightTwo

/-! DUB-17/18 -> residual Galois association -> original primitive form
at every prescribed prime. The source coefficient field constructs its
genuine local field and discrete residual coefficients. The resulting
Galois branch has the original Fourier coefficients, original good primes,
exact original weight determinant, original arithmetic support and original
norm-inertia triviality. The parabolic geometric alternative remains open.
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

/-- Every original primitive form and every prescribed prime construct the
genuine local field and original Fourier-normalized residual Galois alternative. -/
theorem sourcePrimitive_exists_parabolicLift_or_residualGalois_charP
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : ℕ) (hp : p.Prime) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero p hp
    let F := rationalPrimeLocalField p hp
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (u : UniformSpace L) (_ : ValuativeRel L),
      letI : TopologicalSpace L := u.toTopologicalSpace
      letI : TopologicalSpace (AlgebraicClosure 𝓀[L]) := ⊥
      letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
        @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧ Finite 𝓀[L] ∧
      ∃ hchar : CharP (AlgebraicClosure 𝓀[L]) p,
      letI := hchar
      ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L)
        (M : ℕ), Q ∣ M ∧ M ∣ Q * p ^ 2 ∧
        ∃ (values : sourceBinaryHeckePrime M → AlgebraicClosure 𝓀[L])
          (y : H1 (Rep.trivial (AlgebraicClosure 𝓀[L]) (Gamma0 M) (AlgebraicClosure 𝓀[L]))),
          y ≠ 0 ∧
          (∀ ell : sourceBinaryHeckePrime M,
            algebraMap 𝓀[L] (AlgebraicClosure 𝓀[L])
              (sourcePrimitiveResidualHeckeCharacter f hk τ
                ⟨cuspHeckeLinear Q k ell.val, Algebra.subset_adjoin
                  ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩) =
              (ell.val : AlgebraicClosure 𝓀[L]) ^ ((k - 2).toNat / 2) * values ell) ∧
          (∀ ell, sourceTrivialCoefficientHeckeOperators (AlgebraicClosure 𝓀[L]) M ell y =
            values ell • y) ∧
          ((∃ (θ : sourceBinaryHeckePrime M → integralClosure ℤ ℂ)
            (φ : integralClosure ℤ ℂ →+* AlgebraicClosure 𝓀[L])
            (v : H1 (Rep.trivial ℂ (Gamma0 M) ℂ)), v ≠ 0 ∧
            (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 M) ℂ)).hom v ∈ parabolicHoms M ∧
            (∀ ell, sourceTrivialCoefficientHeckeOperators ℂ M ell v = (θ ell : ℂ) • v) ∧
            ∀ ell, φ (θ ell) = values ell) ∨
          (let a : 𝓞 ℚ := (Q * p : ℕ)
           ∃ ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) (AlgebraicClosure 𝓀[L]),
             Continuous ρ ∧
             (∀ (ell : sourceBinaryHeckePrime Q), ell.val ≠ p →
               ∀ g : Gal(rationalPrimeLocalClosure ell.val ell.property.1 /
                 rationalPrimeLocalField ell.val ell.property.1),
                 (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
                   (rationalPrimeLocalClosure ell.val ell.property.1)), g • z = z ^ ell.val) →
                 Matrix.trace (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
                   algebraMap 𝓀[L] (AlgebraicClosure 𝓀[L]) (IsLocalRing.residue 𝒪[L]
                     ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
                       sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩) ∧
                 Matrix.det (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
                   (ell.val : AlgebraicClosure 𝓀[L]) ^ (k - 1).toNat) ∧
             ∀ (ell : ℕ) (hell : ell.Prime), ¬ell ∣ Q → ell ≠ p →
               ∀ g ∈ rationalPrimeNormInertia ell hell,
                 ρ (rationalPrimeArithmeticRestriction a ell hell g) = 1)) := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p hp
  let F := rationalPrimeLocalField p hp
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hc := sourcePrimitive_exists_residualWeightTwo_charP f hk p hp
  dsimp only at hc
  obtain ⟨u, v, hu, hlocal, hext, hdim, hfinite, hchar, τ, _⟩ := hc
  letI : UniformSpace L := u
  letI : TopologicalSpace L := u.toTopologicalSpace
  letI : ValuativeRel L := v
  letI : TopologicalSpace (AlgebraicClosure 𝓀[L]) := ⊥
  letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
    @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
  letI : CharP (AlgebraicClosure 𝓀[L]) p := hchar
  letI : DiscreteTopology (AlgebraicClosure 𝓀[L]) := ⟨rfl⟩
  letI : IsTopologicalRing (AlgebraicClosure 𝓀[L]) := inferInstance
  have h := sourcePrimitive_exists_originalSupport_parabolicLift_or_residualGalois
    (K := AlgebraicClosure 𝓀[L]) p hp f hk τ
  exact ⟨u, v, hu, hlocal, hext, hdim, hfinite, hchar, τ, h⟩

end
end Dubon2026
