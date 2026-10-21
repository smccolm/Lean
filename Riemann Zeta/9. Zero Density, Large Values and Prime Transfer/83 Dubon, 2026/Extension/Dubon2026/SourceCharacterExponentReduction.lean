import Dubon2026.SourceBinaryFlagExponent
import Dubon2026.SourceAffineFunctionRepresentation
import Dubon2026.SourceBinaryFlagUntwisted
import Dubon2026.SourceTrivialCoefficientHecke

/-! Exact prime-field normalization of the original diagonal characters.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> the character d^(2*j) used by the proved function flag.
The actual determinant and finite prime-field unit order prove each
representation equality, including the trivial-character boundary cases.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p] (hpQ : p ∣ Q)

include hpQ in
/-- Every actual lower-diagonal entry has prime-field unit order dividing p-1. -/
theorem sourceCharacterLower_pow_order (g : Gamma0 Q) :
    (((g.val 1 1 : ℤ) : F)) ^ (p - 1) = 1 := by
  have hn : sourceAffineD p Q g ≠ 0 := by
    intro hz
    have h := sourceAffine_ad p Q hpQ g
    rw [hz, mul_zero] at h
    exact zero_ne_one h
  have hd : ((g.val 1 1 : ℤ) : F) =
      ZMod.castHom (dvd_refl p) F (sourceAffineD p Q g) :=
    (map_intCast (ZMod.castHom (dvd_refl p) F) _).symm
  rw [hd, ← map_pow, ZMod.pow_card_sub_one_eq_one hn, map_one]

/-- Congruent original lower-diagonal exponents give exactly the same native coefficient representation. -/
theorem sourceCharacterRep_eq_of_modEq {e e' : ℕ} (he : e ≡ e' [MOD (p - 1)]) :
    sourceBinaryFlagQuotientRep F p Q hpQ e 0 =
      sourceBinaryFlagQuotientRep F p Q hpQ e' 0 := by
  unfold sourceBinaryFlagQuotientRep
  apply congrArg Rep.of
  apply congrArg ((Algebra.lsmul F F F).toMonoidHom.comp)
  apply MonoidHom.ext
  intro g
  change ((g.val 0 0 : ℤ) : F) ^ 0 * ((g.val 1 1 : ℤ) : F) ^ (e - 0) =
    ((g.val 0 0 : ℤ) : F) ^ 0 * ((g.val 1 1 : ℤ) : F) ^ (e' - 0)
  simp only [pow_zero, one_mul, Nat.sub_zero]
  exact pow_eq_pow_of_modEq he (sourceCharacterLower_pow_order F p Q hpQ g)

/-- The actual original binary-flag character is exactly its computed lower-diagonal representation. -/
theorem sourceCharacterRep_eq_lower (n j : ℕ) (hj : j ≤ n) :
    sourceBinaryFlagQuotientRep F p Q hpQ n j =
      sourceBinaryFlagQuotientRep F p Q hpQ (sourceBinaryFlagExponentOf p n j) 0 := by
  unfold sourceBinaryFlagQuotientRep
  apply congrArg Rep.of
  apply congrArg ((Algebra.lsmul F F F).toMonoidHom.comp)
  apply MonoidHom.ext
  intro g
  rw [sourceBinaryFlagCharacter_eq_lower_pow F p Q hpQ n j (Fact.out : p.Prime) hj]
  change _ = ((g.val 0 0 : ℤ) : F) ^ 0 *
    ((g.val 1 1 : ℤ) : F) ^ (sourceBinaryFlagExponentOf p n j - 0)
  simp

/-- A lower-diagonal exponent divisible by the actual prime-field unit order
gives precisely the native trivial coefficient representation. -/
theorem sourceCharacterRep_eq_trivial (e : ℕ) (he : (p - 1) ∣ e) :
    sourceBinaryFlagQuotientRep F p Q hpQ e 0 = Rep.trivial F (Gamma0 Q) F := by
  rw [sourceCharacterRep_eq_of_modEq F p Q hpQ (Nat.modEq_zero_iff_dvd.mpr he)]
  apply congrArg Rep.of
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change (((g.val 0 0 : ℤ) : F) ^ 0 * ((g.val 1 1 : ℤ) : F) ^ (0 - 0)) * v = v
  simp

end
end Dubon2026
