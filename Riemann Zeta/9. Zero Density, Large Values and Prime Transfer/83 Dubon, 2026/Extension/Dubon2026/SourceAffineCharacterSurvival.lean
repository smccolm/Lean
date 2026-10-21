import Dubon2026.SourceRaisedLevelEigensystem
import Dubon2026.SourceCharacterEigenReduction
import Dubon2026.SourceGamma0Eisenstein

/-! Removal of the exact Eisenstein exception in characteristic at least five.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> an actual nonzero original trivial-coefficient eigenclass.
The proved Eisenstein class is lifted at the next actual flag degree.
A second exception would force p-1 to divide two. This directly covers
both exceptional exponent cases, using terminal-flag survival already proved.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p] [NeZero Q]
    (hpQ : p ∣ Q)

/-- Six is nonzero in the actual residual field whenever its prime characteristic is at least five. -/
theorem sourceCharacter_six_ne_zero (hp5 : 5 ≤ p) : (6 : F) ≠ 0 := by
  intro hz
  have hd : p ∣ 6 := (CharP.cast_eq_zero_iff F p 6).mp hz
  have hp : p.Prime := Fact.out
  rcases hp.dvd_mul.mp (show p ∣ 2 * 3 from hd) with h2 | h3
  · have := Nat.le_of_dvd (by norm_num : 0 < 2) h2
    omega
  · have := Nat.le_of_dvd (by norm_num : 0 < 3) h3
    omega

/-- Every actual d^(2*j) character eigenclass in characteristic at least five
gives a nonzero original trivial-coefficient eigenclass at level Q*p with
the exact inverse-prime twist. The Eisenstein alternative is fully removed. -/
theorem sourceAffineCharacter_raiseLevel (hp5 : 5 ≤ p) (j : Fin p)
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceBinaryFlagQuotientRep F p Q hpQ (2 * j.val) 0)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ (2 * j.val) 0 ell x =
      values ell • x) :
    ∃ y : H1 (Rep.trivial F (Gamma0 (Q * p)) F), y ≠ 0 ∧
      ∀ ell : sourceBinaryHeckePrime (Q * p),
        sourceTrivialCoefficientHeckeOperators F (Q * p) ell y =
          (sourceAffineFlagHeckeScalar F p j ell.val *
            values (sourceBinaryGoodPrimeOfLevel (dvd_mul_right Q p) ell)) • y := by
  have h6 := sourceCharacter_six_ne_zero F p hp5
  rcases sourceAffineCharacter_raiseLevel_or_exception F p Q hpQ j h6 values x hx heig with
    hy | ⟨hj, hd, hvalues⟩
  · exact hy
  · have hQ2 : 2 ≤ Q := le_trans (Fact.out : p.Prime).two_le
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne Q)) hpQ)
    obtain ⟨z, hz, he⟩ := sourceGamma0_exists_Eisenstein_eigenclass F Q hQ2
    obtain ⟨w, hw, hwE⟩ := sourceTrivialEigen_to_character F p Q hpQ
      (2 * (j.val + 1)) hd (fun ell => (ell.val : F) + 1) z hz he
    let j' : Fin p := ⟨j.val + 1, hj⟩
    rcases sourceAffineCharacter_raiseLevel_or_exception F p Q hpQ j' h6
        (fun ell => (ell.val : F) + 1) w hw hwE with
      ⟨y, hy, heY⟩ | ⟨_, hd', _⟩
    · refine ⟨y, hy, fun ell => ?_⟩
      rw [heY]
      have hval := hvalues (sourceBinaryGoodPrimeOfLevel (dvd_mul_right Q p) ell)
      change sourceAffineFlagHeckeScalar F p j ell.val *
          values (sourceBinaryGoodPrimeOfLevel (dvd_mul_right Q p) ell) =
        ((ell.val : F) + 1) *
          (ZMod.castHom (dvd_refl p) F ((ell.val : ZMod p)⁻¹)) ^ (j.val + 1) at hval
      rw [hval]
      congr 1
      change sourceAffineFlagHeckeScalar F p j' ell.val * ((ell.val : F) + 1) =
        ((ell.val : F) + 1) *
          (ZMod.castHom (dvd_refl p) F ((ell.val : ZMod p)⁻¹)) ^ (j.val + 1)
      exact mul_comm _ _
    · have hnext : (p - 1) ∣ 2 * (j.val + 1) + 2 := by
        convert hd' using 1
      have htwo : (p - 1) ∣ 2 := (Nat.dvd_add_right hd).mp hnext
      have := Nat.le_of_dvd (by norm_num : 0 < 2) htwo
      omega

end
end Dubon2026
