import Dubon2026.SourceBinaryFlagQuotientHecke
import Dubon2026.SourcePrimeHeckeScalar
import Dubon2026.SourceBinaryH1HeckeAlgebra

/-! Removing the exact coefficient scalar from the actual character Hecke action.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> the character eigensystem with original eigenvalues divided by ell^j.
The native H1, original coset action, character and nonzero class are retained.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (F : Type) [Field F] (p Q : ℕ) [CharP F p] (hpQ : p ∣ Q) (n j : ℕ)

/-- The identity coefficient map intertwines the actual character action
with the original prime subgroup conjugation. -/
theorem sourceBinaryFlagIdentity_intertwine {ell : ℕ} [NeZero ell] (hell : ell.Prime)
    (u : heckeUpperSubgroup Q ell) :
    (LinearMap.id : Module.End F (sourceBinaryFlagQuotientRep F p Q hpQ n j)).comp
        ((sourceBinaryFlagQuotientRep F p Q hpQ n j).ρ (sourceHeckeConjugation hell u)) =
      ((sourceBinaryFlagQuotientRep F p Q hpQ n j).ρ u.val).comp LinearMap.id := by
  apply LinearMap.ext
  intro x
  change F at x
  change sourceBinaryFlagCharacter F p Q hpQ n j (sourceHeckeConjugation hell u) * x =
    sourceBinaryFlagCharacter F p Q hpQ n j u.val * x
  rw [sourceBinaryFlagCharacter_conjugate]

/-- The full original prime Hecke action on the actual quotient character,
with identity coefficient morphism. -/
def sourceBinaryFlagUntwistedHeckeH1 {ell : ℕ} [NeZero ell] (hell : ell.Prime) :
    Module.End F (groupCohomology.H1 (sourceBinaryFlagQuotientRep F p Q hpQ n j)) :=
  sourcePrimeHeckeH1 hell (sourceBinaryFlagQuotientRep F p Q hpQ n j) LinearMap.id
    (sourceBinaryFlagIdentity_intertwine F p Q hpQ n j hell)

/-- The flag quotient's Hecke action is exactly ell^j times the identity-coefficient
character action, on every native H1 class. -/
theorem sourceBinaryFlagQuotientHeckeH1_eq_smul {ell : ℕ} [NeZero ell] (hell : ell.Prime)
    (x : groupCohomology.H1 (sourceBinaryFlagQuotientRep F p Q hpQ n j)) :
    sourceBinaryFlagQuotientHeckeH1 F p Q hpQ n j hell x =
      (ell : F) ^ j • sourceBinaryFlagUntwistedHeckeH1 F p Q hpQ n j hell x :=
  sourcePrimeHeckeH1_smul hell _ LinearMap.id
    (sourceBinaryFlagIdentity_intertwine F p Q hpQ n j hell) ((ell : F) ^ j)
    (sourceBinaryFlagQuotientDiagonal_intertwine F p Q hpQ n j hell) x

private local instance untwistedPrimeNeZero (ell : sourceBinaryHeckePrime Q) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

/-- All original good-prime identity-coefficient operators on the actual
one-dimensional flag quotient character. -/
def sourceBinaryFlagUntwistedOperators :
    sourceBinaryHeckePrime Q →
      Module.End F (groupCohomology.H1 (sourceBinaryFlagQuotientRep F p Q hpQ n j)) :=
  fun ell => sourceBinaryFlagUntwistedHeckeH1 F p Q hpQ n j ell.property.1

include hpQ in
/-- Every original good prime is nonzero in the prescribed residual field
when its characteristic divides the original level. -/
theorem sourceBinaryFlag_goodPrime_cast_ne_zero (hp : p.Prime) (ell : sourceBinaryHeckePrime Q) :
    (ell.val : F) ≠ 0 := by
  intro hzero
  have hpell : p ∣ ell.val := (CharP.cast_eq_zero_iff F p ell.val).mp hzero
  have hcop : Nat.Coprime ell.val p := ell.property.2.of_dvd_right hpQ
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop hpell (dvd_refl p))

end
end Dubon2026
