import Dubon2026.SourceCharacterWeightTwo
import Dubon2026.SourceThreeWeightTwo

/-! Original character-to-weight-two reduction at every residue prime.
DUB-17/18 -> residual modular Galois association -> all-prime weight-two
reduction. The characteristic-at-least-five construction, exact trivial
character cases and proved characteristic-three odd twist are assembled
without excluding either small prime or assuming a surviving eigenclass.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p]
    [NeZero Q] (hpQ : p ∣ Q)

/-- Every actual character eigensystem satisfying the source exponent
congruence reaches original trivial-coefficient H1 at a level between Q
and Q*p with exactly the source good-prime twist, at every residue prime. -/
theorem sourceCharacter_to_weightTwo_all_primes (e t : ℕ)
    (het : (p - 1) ∣ e + 2 * t)
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceBinaryFlagQuotientRep F p Q hpQ e 0)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ e 0 ell x = values ell • x) :
    ∃ (M : ℕ) (hQM : Q ∣ M), M ∣ Q * p ∧
      ∃ y : H1 (Rep.trivial F (Gamma0 M) F), y ≠ 0 ∧
        ∀ ell : sourceBinaryHeckePrime M,
          sourceTrivialCoefficientHeckeOperators F M ell y =
            ((ell.val : F) ^ t * values (sourceBinaryGoodPrimeOfLevel hQM ell)) • y := by
  by_cases hp2 : p = 2
  · subst p
    obtain ⟨y, hy, hey⟩ := sourceCharacter_to_weightTwo_trivial F 2 Q hpQ
      e t (one_dvd e) (one_dvd t) values x hx heig
    exact ⟨Q, dvd_refl Q, dvd_mul_right Q 2, y, hy, hey⟩
  by_cases hp3 : p = 3
  · subst p
    have he : (3 - 1) ∣ e := (Nat.dvd_add_iff_left (dvd_mul_right 2 t)).mpr het
    by_cases ht : 2 ∣ t
    · obtain ⟨y, hy, hey⟩ := sourceCharacter_to_weightTwo_trivial F 3 Q hpQ
        e t he ht values x hx heig
      exact ⟨Q, dvd_refl Q, dvd_mul_right Q 3, y, hy, hey⟩
    · obtain ⟨w, hw, hew⟩ :=
        sourceCharacterEigen_to_trivial F 3 Q hpQ e he values x hx heig
      obtain ⟨M, hQM, hM, y, hy, hey⟩ :=
        sourceThreeWeightTwo_twist F Q hpQ values w hw hew
      refine ⟨M, hQM, hM, y, hy, fun ell => ?_⟩
      have htmod : t ≡ 1 [MOD 2] := by
        rw [Nat.ModEq]
        have hn := Nat.mod_lt t (by decide : 0 < 2)
        have hne : t % 2 ≠ 0 := by
          intro hz
          exact ht (Nat.dvd_of_mod_eq_zero hz)
        omega
      have hporder := sourceCharacter_goodPrime_pow_order F 3 Q hpQ
        (sourceBinaryGoodPrimeOfLevel hQM ell)
      have hpow : (ell.val : F) ^ t = (ell.val : F) :=
        (pow_eq_pow_of_modEq htmod hporder).trans (pow_one _)
      rw [hpow]
      exact hey ell
  · have hp5 : 5 ≤ p := by
      have hp : p.Prime := Fact.out
      have h2 := hp.two_le
      have hn4 : p ≠ 4 := by
        intro he
        subst p
        norm_num at hp
      omega
    obtain ⟨y, hy, hey⟩ := sourceCharacter_to_weightTwo_of_five_le F p Q hpQ
      hp5 e t het values x hx heig
    exact ⟨Q * p, dvd_mul_right Q p, dvd_refl _, y, hy, hey⟩

/-- The actual original binary-flag character output feeds the complete
all-prime weight-two reduction with its exact exponent and Hecke values. -/
theorem sourceBinaryCharacter_to_weightTwo_all_primes (n j t : ℕ) (hj : j ≤ n)
    (het : (p - 1) ∣ sourceBinaryFlagExponentOf p n j + 2 * t)
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceBinaryFlagQuotientRep F p Q hpQ n j)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ n j ell x = values ell • x) :
    ∃ (M : ℕ) (hQM : Q ∣ M), M ∣ Q * p ∧
      ∃ y : H1 (Rep.trivial F (Gamma0 M) F), y ≠ 0 ∧
        ∀ ell : sourceBinaryHeckePrime M,
          sourceTrivialCoefficientHeckeOperators F M ell y =
            ((ell.val : F) ^ t * values (sourceBinaryGoodPrimeOfLevel hQM ell)) • y := by
  obtain ⟨w, hw, hew⟩ := sourceCharacterEigen_to_lower F p Q hpQ n j hj values x hx heig
  exact sourceCharacter_to_weightTwo_all_primes F p Q hpQ
    (sourceBinaryFlagExponentOf p n j) t het values w hw hew

end
end Dubon2026
