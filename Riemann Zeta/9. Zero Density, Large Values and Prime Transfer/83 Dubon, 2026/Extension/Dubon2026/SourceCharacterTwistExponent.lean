import Dubon2026.SourceCharacterExponentReduction
import Dubon2026.SourceAffineFlagHeckeQuotient

/-! Exact original exponents in the character-to-weight-two twist.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> the required scalar ell^t. Prime-field unit powers and the
actual inverse-prime flag scalar are compared explicitly.
-/

namespace Dubon2026
noncomputable section

/-- The actual inverse twist degree lies below p-1 and represents minus t modulo p-1. -/
theorem sourceCharacter_exists_twist_index (p : ℕ) (hp : p.Prime) (t : ℕ) :
    ∃ j : Fin p, j.val < p - 1 ∧ (p - 1) ∣ j.val + t := by
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  let n := ((p - 2) * t) % (p - 1)
  have hn : n < p - 1 := Nat.mod_lt _ hp1
  refine ⟨⟨n, by omega⟩, hn, ?_⟩
  have h1 : n ≡ (p - 2) * t [MOD (p - 1)] := Nat.mod_modEq _ _
  have h2 := h1.add_right t
  rw [show (p - 2) * t + t = (p - 1) * t by
    rw [show p - 1 = (p - 2) + 1 by have := hp.two_le; omega, Nat.add_mul, one_mul]] at h2
  exact Nat.modEq_zero_iff_dvd.mp
    (h2.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)))

/-- The exact source congruence gives the diagonal exponent required by the original flag. -/
theorem sourceCharacter_twist_exponent {p e t j : ℕ}
    (het : (p - 1) ∣ e + 2 * t) (hjt : (p - 1) ∣ j + t) :
    e ≡ 2 * j [MOD (p - 1)] := by
  have h1 : e + 2 * t ≡ 0 [MOD (p - 1)] := Nat.modEq_zero_iff_dvd.mpr het
  have h2 : 2 * j + 2 * t ≡ 0 [MOD (p - 1)] := by
    rw [← mul_add]
    exact Nat.modEq_zero_iff_dvd.mpr (hjt.mul_left 2)
  exact Nat.ModEq.add_right_cancel' (2 * t) (h1.trans h2.symm)

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p] (hpQ : p ∣ Q)

include hpQ

/-- Every original good prime has order dividing p-1 in the actual coefficient prime field. -/
theorem sourceCharacter_goodPrime_pow_order (ell : sourceBinaryHeckePrime Q) :
    (ell.val : F) ^ (p - 1) = 1 := by
  have hn := sourceBinaryFlag_goodPrime_cast_ne_zero (ZMod p) p Q hpQ (Fact.out : p.Prime) ell
  have he := congrArg (ZMod.castHom (dvd_refl p) F) (ZMod.pow_card_sub_one_eq_one hn)
  simpa only [map_pow, map_natCast, map_one] using he

/-- The actual inverse-prime flag scalar is exactly the source positive twist ell^t. -/
theorem sourceCharacter_flagScalar_eq_pow (j : Fin p) (t : ℕ)
    (hjt : (p - 1) ∣ j.val + t) (ell : sourceBinaryHeckePrime Q) :
    sourceAffineFlagHeckeScalar F p j ell.val = (ell.val : F) ^ t := by
  rw [sourceAffineFlagHeckeScalar, map_inv₀, map_natCast, inv_pow]
  have he : (ell.val : F) ^ (j.val + t) = 1 := by
    simpa only [pow_zero] using pow_eq_pow_of_modEq
      (Nat.modEq_zero_iff_dvd.mpr hjt) (sourceCharacter_goodPrime_pow_order F p Q hpQ ell)
  rw [pow_add] at he
  exact inv_eq_of_mul_eq_one_right he

/-- A twist divisible by the actual prime-field unit order is exactly one at all original good primes. -/
theorem sourceCharacter_goodPrime_pow_eq_one (t : ℕ) (ht : (p - 1) ∣ t)
    (ell : sourceBinaryHeckePrime Q) :
    (ell.val : F) ^ t = 1 := by
  simpa only [pow_zero] using pow_eq_pow_of_modEq
    (Nat.modEq_zero_iff_dvd.mpr ht) (sourceCharacter_goodPrime_pow_order F p Q hpQ ell)

end
end Dubon2026
