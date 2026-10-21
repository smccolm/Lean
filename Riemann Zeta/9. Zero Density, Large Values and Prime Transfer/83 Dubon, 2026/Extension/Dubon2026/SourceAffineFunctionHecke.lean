import Dubon2026.SourceAffineFunctionRepresentation
import Dubon2026.SourceBinaryFlagUntwisted
import Dubon2026.SourceIntegralHeckeConjugation

/-! Full original Hecke correspondences on the affine function representation.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> prescribed eigenclass lifting in the actual finite-function flag.
The literal matrix calculation is adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.lean.txt
(Apache-2.0; retained LICENSE and NOTICE). The already proved native
full-coset correspondence supplies H1 and its commutativity.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] (hpQ : p ∣ Q)

private local instance affinePrimeNeZero (ell : sourceBinaryHeckePrime Q) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

/-- The actual affine coefficient map intertwines the original subgroup conjugation. -/
theorem sourceAffineFunctionDiagonal_intertwine (ell : sourceBinaryHeckePrime Q)
    (u : heckeUpperSubgroup Q ell.val) :
    (sourceAffineFunctionDiagonal p F ell.val).comp
        ((sourceAffineFunctionRep p Q F hpQ).ρ (sourceHeckeConjugation ell.property.1 u)) =
      ((sourceAffineFunctionRep p Q F hpQ).ρ u.val).comp
        (sourceAffineFunctionDiagonal p F ell.val) := by
  have hne : (ell.val : ZMod p) ≠ 0 :=
    sourceBinaryFlag_goodPrime_cast_ne_zero (ZMod p) p Q hpQ (Fact.out : p.Prime) ell
  have hd : sourceAffineD p Q (sourceHeckeConjugation ell.property.1 u) =
      sourceAffineD p Q u.val := by
    rw [← sourceIntegralHeckeConjugate_eq_prime]
    rfl
  have hb : sourceAffineB p Q (sourceHeckeConjugation ell.property.1 u) =
      (ell.val : ZMod p)⁻¹ * sourceAffineB p Q u.val := by
    rw [← sourceIntegralHeckeConjugate_eq_prime]
    change (((u.val.val 0 1 / (ell.val : ℤ)) : ℤ) : ZMod p) =
      (ell.val : ZMod p)⁻¹ * ((u.val.val 0 1 : ℤ) : ZMod p)
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ ell.val).mp u.property
    change u.val.val 0 1 = (ell.val : ℤ) * k at hk
    rw [hk, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr ell.property.1.ne_zero)]
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  apply LinearMap.ext
  intro f
  change ZMod p → F at f
  funext w
  change f (sourceAffineD p Q (sourceHeckeConjugation ell.property.1 u) *
    (sourceAffineD p Q (sourceHeckeConjugation ell.property.1 u) *
      ((ell.val : ZMod p)⁻¹ * w) - sourceAffineB p Q (sourceHeckeConjugation ell.property.1 u))) =
    f ((ell.val : ZMod p)⁻¹ *
      (sourceAffineD p Q u.val * (sourceAffineD p Q u.val * w - sourceAffineB p Q u.val)))
  rw [hd, hb]
  congr 1
  ring

/-- All good-prime Hecke operators on native H1 of the original affine function representation. -/
def sourceAffineFunctionHeckeOperators :
    sourceBinaryHeckePrime Q → Module.End F
      (groupCohomology.H1 (sourceAffineFunctionRep p Q F hpQ)) :=
  fun ell => sourcePrimeHeckeH1 ell.property.1 (sourceAffineFunctionRep p Q F hpQ)
    (sourceAffineFunctionDiagonal p F ell.val)
    (sourceAffineFunctionDiagonal_intertwine F p Q hpQ ell)

/-- The original full Hecke actions on finite-function H1 commute at all good primes. -/
theorem sourceAffineFunctionHeckeOperators_commute (a b : sourceBinaryHeckePrime Q) :
    Commute (sourceAffineFunctionHeckeOperators F p Q hpQ a)
      (sourceAffineFunctionHeckeOperators F p Q hpQ b) := by
  by_cases he : a.val = b.val
  · have hab : a = b := Subtype.ext he
    subst b
    exact Commute.refl _
  · exact sourcePrimeHeckeH1_commute a.property.1 (sourceAffineFunctionRep p Q F hpQ)
      (sourceAffineFunctionDiagonal p F a.val)
      (sourceAffineFunctionDiagonal_intertwine F p Q hpQ a)
      b.property.1 a.property.2 b.property.2 he
      (sourceAffineFunctionDiagonal p F b.val)
      (sourceAffineFunctionDiagonal_intertwine F p Q hpQ b)
      (sourceAffineFunctionDiagonal_commute p F a.val b.val)

end
end Dubon2026
