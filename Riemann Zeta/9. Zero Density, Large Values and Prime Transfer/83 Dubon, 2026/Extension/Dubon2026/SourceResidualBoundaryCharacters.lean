import Dubon2026.SourceNativeBoundaryCharacters
import Dubon2026.SourceFiniteCharacterReduction

/-! DUB-17/18 -> residual Galois association -> the nonparabolic original
complex weight-two lift -> its actual residual Dirichlet pair. The same
reduction map used for all original eigenvalues reduces the constructed
characters, preserving their product and the exact prime-value formula.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology SourceCuspBoundary

/-- The actual nonparabolic complex eigenclass and its original reduction
construct residual unit characters with product one and the exact reduced
eigenvalues at every original good prime. -/
theorem sourceComplexH1_residual_dirichletPair
    (F : Type) [Field F] (N : ℕ) [NeZero N]
    (θ : sourceBinaryHeckePrime N → integralClosure ℤ ℂ)
    (φ : integralClosure ℤ ℂ →+* F)
    (x : H1 (Rep.trivial ℂ (Gamma0 N) ℂ))
    (hpar : (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).hom x ∉ parabolicHoms N)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators ℂ N ell x = (θ ell : ℂ) • x) :
    ∃ ψ₁ ψ₂ : (ZMod N)ˣ →* Fˣ,
      (∀ u, (ψ₁ u : F) * (ψ₂ u : F) = 1) ∧
      ∀ ell : sourceBinaryHeckePrime N,
        φ (θ ell) = (ψ₁ (ZMod.unitOfCoprime ell.val ell.property.2) : F) +
          (ell.val : F) * (ψ₂ (ZMod.unitOfCoprime ell.val ell.property.2) : F) := by
  obtain ⟨ψ₁, ψ₂, hprod, hsum⟩ :=
    sourceComplexH1_nonparabolic_dirichletPair N (fun ell => (θ ell : ℂ)) x hpar heig
  refine ⟨sourceFiniteCharacterReduction φ ψ₁.toUnitHom,
    sourceFiniteCharacterReduction φ ψ₂.toUnitHom, ?_, ?_⟩
  · intro u
    rw [sourceFiniteCharacterReduction_apply, sourceFiniteCharacterReduction_apply,
      ← map_mul, ← map_one φ]
    congr 1
    apply Subtype.ext
    change (ψ₁.toUnitHom u : ℂ) * (ψ₂.toUnitHom u : ℂ) = 1
    rw [MulChar.coe_toUnitHom, MulChar.coe_toUnitHom, hprod]
  · intro ell
    rw [sourceFiniteCharacterReduction_apply, sourceFiniteCharacterReduction_apply]
    let u := ZMod.unitOfCoprime ell.val ell.property.2
    have hi : θ ell =
        (⟨(ψ₁.toUnitHom u : ℂ), sourceFiniteCharacter_isIntegral _ _⟩ :
          integralClosure ℤ ℂ) +
          ell.val * ⟨(ψ₂.toUnitHom u : ℂ), sourceFiniteCharacter_isIntegral _ _⟩ := by
      apply Subtype.ext
      change (θ ell : ℂ) = (ψ₁.toUnitHom u : ℂ) +
        (ell.val : ℂ) * (ψ₂.toUnitHom u : ℂ)
      rw [MulChar.coe_toUnitHom, MulChar.coe_toUnitHom]
      exact hsum ell
    rw [hi, map_add, map_mul, map_natCast]

end
end Dubon2026
