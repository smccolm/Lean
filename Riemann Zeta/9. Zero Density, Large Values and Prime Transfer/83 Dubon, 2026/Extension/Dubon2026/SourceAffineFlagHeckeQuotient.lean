import Dubon2026.SourceAffineFlagRepresentation
import Dubon2026.SourcePrimeHeckeNaturality

/-! The exact Hecke scalar on the actual affine flag's character quotient.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> lifting the original character eigenvalues into the function flag.
Native full-correspondence naturality and scalar compatibility identify the
quotient action; no independently supplied Hecke comparison is used.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p] (hpQ : p ∣ Q)
    (j : Fin p)

/-- The exact inverse-prime power on the original function flag's leading coordinate. -/
def sourceAffineFlagHeckeScalar (ell : ℕ) : F :=
  (ZMod.castHom (dvd_refl p) F ((ell : ZMod p)⁻¹)) ^ j.val

/-- The original character quotient coefficient map, with its computed inverse-prime scalar. -/
def sourceAffineFlagQuotientDiagonal (ell : ℕ) :
    Module.End F (sourceBinaryFlagQuotientRep F p Q hpQ (2 * j.val) 0) :=
  sourceAffineFlagHeckeScalar F p j ell • LinearMap.id

private local instance affineQuotientPrimeNeZero (ell : sourceBinaryHeckePrime Q) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

/-- The computed character coefficient map intertwines the actual subgroup conjugation. -/
theorem sourceAffineFlagQuotientDiagonal_intertwine (ell : sourceBinaryHeckePrime Q)
    (u : heckeUpperSubgroup Q ell.val) :
    (sourceAffineFlagQuotientDiagonal F p Q hpQ j ell.val).comp
        ((sourceBinaryFlagQuotientRep F p Q hpQ (2 * j.val) 0).ρ
          (sourceHeckeConjugation ell.property.1 u)) =
      ((sourceBinaryFlagQuotientRep F p Q hpQ (2 * j.val) 0).ρ u.val).comp
        (sourceAffineFlagQuotientDiagonal F p Q hpQ j ell.val) := by
  unfold sourceAffineFlagQuotientDiagonal
  rw [LinearMap.smul_comp, LinearMap.comp_smul,
    sourceBinaryFlagIdentity_intertwine F p Q hpQ (2 * j.val) 0 ell.property.1 u]

/-- Original leading-coordinate extraction intertwines the exact coefficient maps. -/
theorem sourceAffineFlagQuotientMap_diagonal (ell : ℕ) :
    (sourceAffineFlagQuotientMap F p Q hpQ j).hom.toLinearMap.comp
        (sourceAffineFlagDiagonal F p j ell) =
      (sourceAffineFlagQuotientDiagonal F p Q hpQ j ell).comp
        (sourceAffineFlagQuotientMap F p Q hpQ j).hom.toLinearMap := by
  apply LinearMap.ext
  intro f
  exact sourceAffineFunctionCoordinate_diagonal F p j ell f.property

/-- The full actual character H1 family with the exact computed quotient scalar. -/
def sourceAffineFlagCharacterOperators :
    sourceBinaryHeckePrime Q → Module.End F
      (groupCohomology.H1 (sourceBinaryFlagQuotientRep F p Q hpQ (2 * j.val) 0)) :=
  fun ell => sourceAffineFlagHeckeScalar F p j ell.val •
    sourceBinaryFlagUntwistedOperators F p Q hpQ (2 * j.val) 0 ell

/-- The actual native H1 quotient map intertwines all original good-prime operators,
including the exact inverse-prime twist. -/
theorem sourceAffineFlagQuotientMap_hecke (ell : sourceBinaryHeckePrime Q) :
    ((groupCohomology.functor F (Gamma0 Q) 1).map
      (sourceAffineFlagQuotientMap F p Q hpQ j)).hom.comp
        (sourceAffineFlagHeckeOperators F p Q hpQ j ell) =
      (sourceAffineFlagCharacterOperators F p Q hpQ j ell).comp
        ((groupCohomology.functor F (Gamma0 Q) 1).map
          (sourceAffineFlagQuotientMap F p Q hpQ j)).hom := by
  apply LinearMap.ext
  intro x
  change ((groupCohomology.functor F (Gamma0 Q) 1).map
      (sourceAffineFlagQuotientMap F p Q hpQ j))
        (sourcePrimeHeckeH1 ell.property.1 _ _
          (sourceAffineFlagDiagonal_intertwine F p Q hpQ j ell) x) = _
  rw [sourcePrimeHeckeH1_naturality ell.property.1 _ _
    (sourceAffineFlagQuotientMap F p Q hpQ j) _
    (sourceAffineFlagQuotientDiagonal F p Q hpQ j ell.val)
    (sourceAffineFlagDiagonal_intertwine F p Q hpQ j ell)
    (sourceAffineFlagQuotientDiagonal_intertwine F p Q hpQ j ell)
    (sourceAffineFlagQuotientMap_diagonal F p Q hpQ j ell.val)]
  exact sourcePrimeHeckeH1_smul ell.property.1 _ LinearMap.id
    (sourceBinaryFlagIdentity_intertwine F p Q hpQ (2 * j.val) 0 ell.property.1)
    (sourceAffineFlagHeckeScalar F p j ell.val)
    (sourceAffineFlagQuotientDiagonal_intertwine F p Q hpQ j ell) _

end
end Dubon2026
