import Dubon2026.SourceBinaryFlagQuotientRepresentation
import Mathlib.FieldTheory.Finite.Basic

/-! Exact characteristic-p exponents of the original residual flag characters.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> character-piece normalization. The determinant and the actual prime-field
entries identify the original character, including characteristics two and
three. Adapted from anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_HeckeEis_exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

/-- The nonnegative exponent of the actual lower-diagonal character
on the j-th residual binary quotient. -/
def sourceBinaryFlagExponentOf (p n j : ℕ) : ℕ := n + (p - 3) * j

/-- The character exponent plus twice the Hecke scalar exponent agrees
with the original binary degree modulo the prime-field unit order. -/
theorem sourceBinaryFlagExponentOf_modEq {p : ℕ} (hp : p.Prime) (n j : ℕ) :
    sourceBinaryFlagExponentOf p n j + 2 * j ≡ n [MOD (p - 1)] := by
  have hp2 := hp.two_le
  rcases Nat.lt_or_ge p 3 with h3 | h3
  · have he : p = 2 := by omega
    subst p
    simp [Nat.ModEq, Nat.mod_one]
  · rw [sourceBinaryFlagExponentOf,
      show n + (p - 3) * j + 2 * j = n + (p - 1) * j by
        rw [show p - 1 = (p - 3) + 2 by omega]
        ring]
    exact (Nat.modEq_iff_dvd' (Nat.le_add_right n _)).mpr (by simp) |>.symm

variable (F : Type) [Field F] (p Q : ℕ) [CharP F p] (hpQ : p ∣ Q) (n j : ℕ)

/-- The actual flag character equals the corresponding lower-diagonal
power. Both the determinant relation and finite prime-field unit relation
are proved for the original congruence-group entries. -/
theorem sourceBinaryFlagCharacter_eq_lower_pow (hp : p.Prime) (hj : j ≤ n)
    (g : Gamma0 Q) :
    sourceBinaryFlagCharacter F p Q hpQ n j g =
      ((g.val 1 1 : ℤ) : F) ^ sourceBinaryFlagExponentOf p n j := by
  letI : Fact p.Prime := ⟨hp⟩
  let a : F := ((g.val 0 0 : ℤ) : F)
  let d : F := ((g.val 1 1 : ℤ) : F)
  change a ^ j * d ^ (n - j) = d ^ sourceBinaryFlagExponentOf p n j
  have had : a * d = 1 := by
    have hdet := Matrix.det_fin_two g.val.val
    rw [g.val.property] at hdet
    have h := congrArg (fun z : ℤ => (z : F)) hdet
    simp only [Int.cast_one, Int.cast_sub, Int.cast_mul,
      sourceBinaryFlag_lower_zero F p Q hpQ g, mul_zero, sub_zero] at h
    exact h.symm
  have hdp : d ^ (p - 1) = 1 := by
    have hd : d = ZMod.castHom (dvd_refl p) F ((g.val 1 1 : ℤ) : ZMod p) :=
      (map_intCast (ZMod.castHom (dvd_refl p) F) _).symm
    have hne : ((g.val 1 1 : ℤ) : ZMod p) ≠ 0 := by
      intro hzero
      rw [hd, hzero, map_zero, mul_zero] at had
      exact zero_ne_one had
    rw [hd, ← map_pow, ZMod.pow_card_sub_one_eq_one hne, map_one]
  have hp2 := hp.two_le
  rcases Nat.lt_or_ge p 3 with h3 | h3
  · have he : p = 2 := by omega
    have hd : d = 1 := by rw [he] at hdp; simpa using hdp
    have ha : a = 1 := by rw [hd, mul_one] at had; exact had
    rw [ha, hd, one_pow, one_pow, one_pow, mul_one]
  · have ha : d ^ (p - 2) = a := by
      have he : d ^ (p - 2) * d = a * d := by
        rw [← pow_succ, show p - 2 + 1 = p - 1 by omega, hdp, had]
      have hd : d ≠ 0 := by
        intro hzero
        rw [hzero, mul_zero] at had
        exact zero_ne_one had
      exact mul_right_cancel₀ hd he
    rw [sourceBinaryFlagExponentOf,
      show n + (p - 3) * j = (n - j) + (p - 2) * j by
        rw [show p - 2 = (p - 3) + 1 by omega]
        ring_nf
        omega,
      pow_add, pow_mul, ha, mul_comm]

end
end Dubon2026
