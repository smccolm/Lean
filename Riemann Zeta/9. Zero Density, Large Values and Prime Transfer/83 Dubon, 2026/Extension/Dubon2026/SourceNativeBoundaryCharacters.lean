import Dubon2026.SourceNativeCuspHecke
import Dubon2026.SourceBoundaryCharacters

/-! DUB-17/18 -> residual Galois association -> the nonparabolic branch
of the actual constructed complex weight-two eigenclass. Its original
native Hecke action and actual nonzero cusp boundary construct the
Dirichlet pair, with product one and exactly the original eigenvalues.
No boundary function, nonzeroness or Hecke comparison is supplied.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology SourceCuspBoundary

/-- Every actual nonparabolic complex weight-two H1 eigensystem is the
sum of a genuine Dirichlet character and ell times its inverse character. -/
theorem sourceComplexH1_nonparabolic_dirichletPair
    (N : ℕ) [NeZero N] (values : sourceBinaryHeckePrime N → ℂ)
    (x : H1 (Rep.trivial ℂ (Gamma0 N) ℂ))
    (hpar : (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).hom x ∉ parabolicHoms N)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators ℂ N ell x = values ell • x) :
    ∃ ψ₁ ψ₂ : DirichletCharacter ℂ N,
      (∀ u : (ZMod N)ˣ, ψ₁ (u : ZMod N) * ψ₂ (u : ZMod N) = 1) ∧
      ∀ ell : sourceBinaryHeckePrime N,
        values ell = ψ₁ (ell.val : ZMod N) + (ell.val : ℂ) * ψ₂ (ell.val : ZMod N) := by
  let φ := (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).hom x
  apply exists_dirichlet_pair values (bOf φ) _ (bOf_ne_zero φ hpar)
  constructor
  · intro ell p
    have h := bOf_native_hecke ℂ x ell p
    have hs : (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).hom
        (values ell • x) = values ell • φ := map_smul _ _ _
    rw [sourceTrivialRingHeckeOperators_field, heig, hs, bOf_smul] at h
    simpa only [nsmul_eq_mul, smul_eq_mul] using h.symm
  · exact bOf_diagonal φ

end
end Dubon2026
