import Dubon2026.SourceTrivialComplexEigenlift
import Dubon2026.SourceResidualBoundaryCharacters

/-! DUB-17/18 -> residual Galois association -> two actual weight-two
branches. Every original residual eigenclass either has an actual
parabolic complex lift with exact integral reduction, or constructs
two residual unit characters with product one and the prescribed
eigenvalues. The finite-order Eisenstein case is absorbed by the
trivial characters. Neither branch is an extra source premise.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology SourceCuspBoundary

/-- The original nonzero residual weight-two eigensystem reduces to an
actual parabolic complex lift or an actual residual Dirichlet pair,
with its exact original values and all good primes preserved. -/
theorem sourceTrivialH1Eigen_parabolicLift_or_dirichletPair
    (F : Type) [Field F] [IsAlgClosed F] (N : ℕ) [NeZero N]
    (values : sourceBinaryHeckePrime N → F)
    (x : H1 (Rep.trivial F (Gamma0 N) F)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F N ell x = values ell • x) :
    (∃ (θ : sourceBinaryHeckePrime N → integralClosure ℤ ℂ)
      (φ : integralClosure ℤ ℂ →+* F)
      (v : H1 (Rep.trivial ℂ (Gamma0 N) ℂ)), v ≠ 0 ∧
      (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).hom v ∈ parabolicHoms N ∧
      (∀ ell, sourceTrivialCoefficientHeckeOperators ℂ N ell v = (θ ell : ℂ) • v) ∧
      ∀ ell, φ (θ ell) = values ell) ∨
    (∃ ψ₁ ψ₂ : (ZMod N)ˣ →* Fˣ,
      (∀ u, (ψ₁ u : F) * (ψ₂ u : F) = 1) ∧
      ∀ ell : sourceBinaryHeckePrime N,
        values ell = (ψ₁ (ZMod.unitOfCoprime ell.val ell.property.2) : F) +
          (ell.val : F) * (ψ₂ (ZMod.unitOfCoprime ell.val ell.property.2) : F)) := by
  classical
  rcases sourceTrivialH1Eigen_complexLift_or_eisenstein F N values x hx heig with
    ⟨θ, φ, v, hv, hT, hred⟩ | hE
  · by_cases hp : (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).hom v ∈ parabolicHoms N
    · exact Or.inl ⟨θ, φ, v, hv, hp, hT, hred⟩
    · obtain ⟨ψ₁, ψ₂, hprod, hsum⟩ :=
        sourceComplexH1_residual_dirichletPair F N θ φ v hp hT
      exact Or.inr ⟨ψ₁, ψ₂, hprod, fun ell => (hred ell).symm.trans (hsum ell)⟩
  · refine Or.inr ⟨1, 1, ?_, ?_⟩
    · intro u
      simp only [MonoidHom.one_apply, Units.val_one, one_mul]
    · intro ell
      rw [hE ell]
      simp only [MonoidHom.one_apply, Units.val_one, mul_one, add_comm]

end
end Dubon2026
