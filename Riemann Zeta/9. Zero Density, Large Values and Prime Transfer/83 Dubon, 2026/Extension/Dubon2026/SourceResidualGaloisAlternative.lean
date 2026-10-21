import Dubon2026.SourceBoundaryGaloisLocal
import Dubon2026.SourceResidualWeightTwoAlternatives

/-! DUB-17/18 -> residual Galois association -> original weight-two class.
The actual residual Dirichlet branch now constructs its continuous
arithmetic Galois representation, exact original Frobenius traces and
determinants, and original inertia triviality. Only the parabolic complex
branch still requires its geometric Galois realization.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
open CongruenceSubgroup groupCohomology SourceCuspBoundary

attribute [local instance] rationalPrimeLocalField_charZero rationalPrimeOriginalNorm
  rationalPrimeOriginalNorm_ultrametric rationalPrimeOriginalClosureNorm
  rationalPrimeOriginalClosureNormedAlgebra rationalPrimeOriginalClosureNorm_ultrametric
  algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- Every actual original residual weight-two eigenclass either has an
actual parabolic complex lift with exact reduction or has a constructed
continuous arithmetic Galois realization with the precise original local
trace, determinant and inertia statements. -/
theorem sourceTrivialH1Eigen_parabolicLift_or_galoisRep
    (F : Type) [Field F] [IsAlgClosed F] [TopologicalSpace F]
    (N p : ℕ) [NeZero N] (hp : p.Prime) [CharP F p]
    (values : sourceBinaryHeckePrime N → F)
    (x : H1 (Rep.trivial F (Gamma0 N) F)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F N ell x = values ell • x) :
    (∃ (θ : sourceBinaryHeckePrime N → integralClosure ℤ ℂ)
      (φ : integralClosure ℤ ℂ →+* F)
      (v : H1 (Rep.trivial ℂ (Gamma0 N) ℂ)), v ≠ 0 ∧
      (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).hom v ∈ parabolicHoms N ∧
      (∀ ell, sourceTrivialCoefficientHeckeOperators ℂ N ell v = (θ ell : ℂ) • v) ∧
      ∀ ell, φ (θ ell) = values ell) ∨
    (let a : 𝓞 ℚ := (N * p : ℕ)
     ∃ ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) F,
       Continuous ρ ∧
       (∀ (ell : sourceBinaryHeckePrime N), ell.val ≠ p →
         ∀ g : Gal(rationalPrimeLocalClosure ell.val ell.property.1 /
           rationalPrimeLocalField ell.val ell.property.1),
           (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
             (rationalPrimeLocalClosure ell.val ell.property.1)), g • z = z ^ ell.val) →
           Matrix.trace (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
             values ell ∧
           Matrix.det (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
             (ell.val : F)) ∧
       ∀ (ell : ℕ) (hell : ell.Prime), ¬ell ∣ N → ell ≠ p →
         ∀ g ∈ rationalPrimeNormInertia ell hell,
           ρ (rationalPrimeArithmeticRestriction a ell hell g) = 1) := by
  rcases sourceTrivialH1Eigen_parabolicLift_or_dirichletPair F N values x hx heig with
    hlift | ⟨ψ₁, ψ₂, hψ, hvalues⟩
  · exact Or.inl hlift
  right
  letI : NeZero p := ⟨hp.ne_zero⟩
  let a : 𝓞 ℚ := (N * p : ℕ)
  have hNa : (N : 𝓞 ℚ) ∣ a := ⟨(p : 𝓞 ℚ), by simp [a]⟩
  have hpa : (p : 𝓞 ℚ) ∣ a := ⟨(N : 𝓞 ℚ), by simp [a, mul_comm]⟩
  refine ⟨sourceBoundaryGaloisRepresentation N p a hNa hpa ψ₁ ψ₂,
    sourceBoundaryGaloisRepresentation_continuous N p a hNa hpa ψ₁ ψ₂, ?_, ?_⟩
  · intro ell hellp g hg
    have hellN : ¬ell.val ∣ N :=
      ell.property.1.coprime_iff_not_dvd.mp ell.property.2
    refine ⟨?_, sourceBoundaryGalois_frobenius_det N p a hNa hpa ψ₁ ψ₂ hψ
      hp ell.val ell.property.1 hellp g hg⟩
    rw [sourceBoundaryGalois_frobenius_trace N p a hNa hpa ψ₁ ψ₂ hp
      ell.val ell.property.1 hellN hellp g hg, hvalues ell]
  · intro ell hell hellN hellp g hg
    exact sourceBoundaryGalois_inertia N p a hNa hpa ψ₁ ψ₂ hp ell hell hellN hellp g hg

end
end Dubon2026
