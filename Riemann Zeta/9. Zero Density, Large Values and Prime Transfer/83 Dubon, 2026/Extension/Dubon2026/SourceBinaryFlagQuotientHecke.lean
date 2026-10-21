import Dubon2026.SourceBinaryFlagQuotientRepresentation
import Dubon2026.SourcePrimeHeckeNaturality
import Dubon2026.SourceIntegralHeckeConjugation

/-! Original Hecke compatibility of the residual coefficient-flag quotient.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> eigenvalue descent through the exact original flag. The quotient Hecke
coefficient is the literal scalar ell^j, and both maps of the flag sequence
intertwine the original coefficient diagonals.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (F : Type) [Field F] (p Q : ℕ) [CharP F p] (hpQ : p ∣ Q) (n j : ℕ)

/-- Original diagonal conjugation preserves the actual coefficient-quotient character. -/
theorem sourceBinaryFlagCharacter_conjugate {ell : ℕ} [NeZero ell] (hell : ell.Prime)
    (u : heckeUpperSubgroup Q ell) :
    sourceBinaryFlagCharacter F p Q hpQ n j (sourceHeckeConjugation hell u) =
      sourceBinaryFlagCharacter F p Q hpQ n j u.val := by
  rw [← sourceIntegralHeckeConjugate_eq_prime hell u]
  rfl

/-- The original coefficient action of the prime Hecke diagonal on the
one-dimensional quotient is the scalar ell^j. -/
def sourceBinaryFlagQuotientDiagonal (ell : ℕ) : Module.End F F :=
  (ell : F) ^ j • LinearMap.id

/-- The computed quotient Hecke scalar intertwines the original subgroup conjugation. -/
theorem sourceBinaryFlagQuotientDiagonal_intertwine {ell : ℕ} [NeZero ell] (hell : ell.Prime)
    (u : heckeUpperSubgroup Q ell) :
    (sourceBinaryFlagQuotientDiagonal F j ell).comp
        ((sourceBinaryFlagQuotientRep F p Q hpQ n j).ρ (sourceHeckeConjugation hell u)) =
      ((sourceBinaryFlagQuotientRep F p Q hpQ n j).ρ u.val).comp
        (sourceBinaryFlagQuotientDiagonal F j ell) := by
  apply LinearMap.ext
  intro x
  change F at x
  change (ell : F) ^ j * (sourceBinaryFlagCharacter F p Q hpQ n j
    (sourceHeckeConjugation hell u) * x) =
      sourceBinaryFlagCharacter F p Q hpQ n j u.val * ((ell : F) ^ j * x)
  rw [sourceBinaryFlagCharacter_conjugate]
  ring

/-- The genuine full prime correspondence on native H1 of the actual
one-dimensional coefficient quotient. -/
def sourceBinaryFlagQuotientHeckeH1 {ell : ℕ} [NeZero ell] (hell : ell.Prime) :
    Module.End F (groupCohomology.H1 (sourceBinaryFlagQuotientRep F p Q hpQ n j)) :=
  sourcePrimeHeckeH1 hell (sourceBinaryFlagQuotientRep F p Q hpQ n j)
    (sourceBinaryFlagQuotientDiagonal F j ell)
    (sourceBinaryFlagQuotientDiagonal_intertwine F p Q hpQ n j hell)

/-- Original coefficient extraction intertwines the full original Hecke diagonal
with the computed ell^j quotient scalar. -/
theorem sourceBinaryFlagQuotientMap_diagonal (ell : ℕ) :
    (sourceBinaryFlagQuotientMap F p Q hpQ n j).hom.toLinearMap.comp
        (sourceBinaryFlagDiagonal F n j ell) =
      (sourceBinaryFlagQuotientDiagonal F j ell).comp
        (sourceBinaryFlagQuotientMap F p Q hpQ n j).hom.toLinearMap := by
  apply LinearMap.ext
  intro P
  exact sourceBinaryFlag_hecke_graded F n j ell P.val P.property

/-- The actual next-step inclusion intertwines the original restricted Hecke diagonals. -/
theorem sourceBinaryFlagInclusion_diagonal (ell : ℕ) :
    (sourceBinaryFlagInclusion F p Q hpQ n j).hom.toLinearMap.comp
        (sourceBinaryFlagDiagonal F n (j + 1) ell) =
      (sourceBinaryFlagDiagonal F n j ell).comp
        (sourceBinaryFlagInclusion F p Q hpQ n j).hom.toLinearMap := by
  apply LinearMap.ext
  intro P
  rfl

end
end Dubon2026
