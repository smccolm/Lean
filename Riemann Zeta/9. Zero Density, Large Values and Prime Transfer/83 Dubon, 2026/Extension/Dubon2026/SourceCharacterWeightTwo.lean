import Dubon2026.SourceAffineCharacterSurvival
import Dubon2026.SourceCharacterTwistExponent

/-! Original character-to-weight-two reduction with the exact source twist.
DUB-17/18 -> residual modular Galois association -> actual trivial-coefficient
Hecke eigenclass. The characteristic-at-least-five branch now discharges
the Eisenstein exception and the exact inverse/positive exponent comparison.
The trivial-character-and-twist branch includes every characteristic-two case.
Characteristic-three odd twists remain a separate required obligation.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p] [NeZero Q]
    (hpQ : p ∣ Q)

/-- In every prime characteristic at least five, the exact source character
congruence produces a nonzero original weight-two H1 eigensystem at level Q*p
with eigenvalues ell^t times the original character eigenvalues. -/
theorem sourceCharacter_to_weightTwo_of_five_le (hp5 : 5 ≤ p)
    (e t : ℕ) (het : (p - 1) ∣ e + 2 * t)
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceBinaryFlagQuotientRep F p Q hpQ e 0)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ e 0 ell x = values ell • x) :
    ∃ y : H1 (Rep.trivial F (Gamma0 (Q * p)) F), y ≠ 0 ∧
      ∀ ell : sourceBinaryHeckePrime (Q * p),
        sourceTrivialCoefficientHeckeOperators F (Q * p) ell y =
          ((ell.val : F) ^ t *
            values (sourceBinaryGoodPrimeOfLevel (dvd_mul_right Q p) ell)) • y := by
  obtain ⟨j, _, hjt⟩ := sourceCharacter_exists_twist_index p (Fact.out : p.Prime) t
  have he : e ≡ 2 * j.val [MOD (p - 1)] := sourceCharacter_twist_exponent het hjt
  obtain ⟨w, hw, hwE⟩ := sourceCharacterEigen_of_modEq F p Q hpQ he values x hx heig
  obtain ⟨y, hy, heY⟩ := sourceAffineCharacter_raiseLevel F p Q hpQ hp5 j values w hw hwE
  refine ⟨y, hy, fun ell => ?_⟩
  rw [heY]
  have hs := sourceCharacter_flagScalar_eq_pow F p Q hpQ j t hjt
    (sourceBinaryGoodPrimeOfLevel (dvd_mul_right Q p) ell)
  change sourceAffineFlagHeckeScalar F p j ell.val = (ell.val : F) ^ t at hs
  rw [hs]

/-- The actual character output of binary-flag descent feeds the proved
characteristic-at-least-five weight-two reduction, with its original character
and all good-prime eigenvalues retained. -/
theorem sourceBinaryCharacter_to_weightTwo_of_five_le (hp5 : 5 ≤ p)
    (n j t : ℕ) (hj : j ≤ n)
    (het : (p - 1) ∣ sourceBinaryFlagExponentOf p n j + 2 * t)
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceBinaryFlagQuotientRep F p Q hpQ n j)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ n j ell x = values ell • x) :
    ∃ y : H1 (Rep.trivial F (Gamma0 (Q * p)) F), y ≠ 0 ∧
      ∀ ell : sourceBinaryHeckePrime (Q * p),
        sourceTrivialCoefficientHeckeOperators F (Q * p) ell y =
          ((ell.val : F) ^ t *
            values (sourceBinaryGoodPrimeOfLevel (dvd_mul_right Q p) ell)) • y := by
  obtain ⟨w, hw, hwE⟩ := sourceCharacterEigen_to_lower F p Q hpQ n j hj values x hx heig
  exact sourceCharacter_to_weightTwo_of_five_le F p Q hpQ hp5
    (sourceBinaryFlagExponentOf p n j) t het values w hw hwE

omit [NeZero Q] in
/-- If both original character and twist exponents are divisible by p-1,
the required original weight-two eigenclass already exists at the same level. -/
theorem sourceCharacter_to_weightTwo_trivial (e t : ℕ)
    (he : (p - 1) ∣ e) (ht : (p - 1) ∣ t)
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceBinaryFlagQuotientRep F p Q hpQ e 0)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ e 0 ell x = values ell • x) :
    ∃ y : H1 (Rep.trivial F (Gamma0 Q) F), y ≠ 0 ∧
      ∀ ell, sourceTrivialCoefficientHeckeOperators F Q ell y =
        ((ell.val : F) ^ t * values ell) • y := by
  obtain ⟨y, hy, heY⟩ := sourceCharacterEigen_to_trivial F p Q hpQ e he values x hx heig
  refine ⟨y, hy, fun ell => ?_⟩
  rw [sourceCharacter_goodPrime_pow_eq_one F p Q hpQ t ht ell, one_mul]
  exact heY ell

end
end Dubon2026
