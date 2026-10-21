import Dubon2026.SourceBinaryLevelEigensystem
import Dubon2026.SourceBinaryCharacterDescent

/-! Actual residual character descent at every prescribed prime and source level.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> a nonzero original character H1 eigensystem at a level dividing Q*p.
Level raising now removes the residue-prime-divisibility premise without
changing the original good-prime Fourier eigenvalues.
-/

namespace Dubon2026
noncomputable section

variable (F : Type) [Field F] (Q p n : ℕ) [CharP F p]

private theorem prime_divisible_level [NeZero Q] (hp : p.Prime)
    (eigenvalues : sourceBinaryHeckePrime Q → F)
    (x : groupCohomology.H1 (sourceBinaryCoefficientRep F Q n)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryH1PrimeOperators F Q n ell x = eigenvalues ell • x) :
    ∃ (M : ℕ) (hQM : Q ∣ M), p ∣ M ∧ M ∣ Q * p ∧
      ∃ y : groupCohomology.H1 (sourceBinaryCoefficientRep F M n),
        y ≠ 0 ∧ ∀ ell, sourceBinaryH1PrimeOperators F M n ell y =
          eigenvalues (sourceBinaryGoodPrimeOfLevel hQM ell) • y := by
  by_cases hpQ : p ∣ Q
  · exact ⟨Q, dvd_refl Q, hpQ, dvd_mul_right Q p, x, hx, heig⟩
  · obtain ⟨y, hy, he⟩ := sourceBinaryH1_raiseLevel F Q p n hp
      (hp.coprime_iff_not_dvd.mpr hpQ) eigenvalues x hx heig
    exact ⟨Q * p, dvd_mul_right Q p, dvd_mul_left p Q, dvd_refl _, y, hy, he⟩

/-- For every original level and prescribed residue prime, a nonzero
original binary H1 eigensystem descends to a nonzero actual character H1
eigensystem at a prime-divisible level M with Q dividing M and M dividing
Q*p. The character exponent, congruence and every original good-prime
eigenvalue twist are derived. No level-divisibility condition is supplied. -/
theorem sourceBinaryH1_exists_characterLevel [NeZero Q] (hp : p.Prime)
    (eigenvalues : sourceBinaryHeckePrime Q → F)
    (x : groupCohomology.H1 (sourceBinaryCoefficientRep F Q n)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryH1PrimeOperators F Q n ell x = eigenvalues ell • x) :
    ∃ (M : ℕ) (hQM : Q ∣ M) (hpM : p ∣ M), M ∣ Q * p ∧
      ∃ j : ℕ, j ≤ n ∧
        (sourceBinaryFlagExponentOf p n j + 2 * j ≡ n [MOD (p - 1)]) ∧
        (∀ g : CongruenceSubgroup.Gamma0 M, sourceBinaryFlagCharacter F p M hpM n j g =
          ((g.val 1 1 : ℤ) : F) ^ sourceBinaryFlagExponentOf p n j) ∧
        ∃ (values : sourceBinaryHeckePrime M → F)
          (y : groupCohomology.H1 (sourceBinaryFlagQuotientRep F p M hpM n j)),
          y ≠ 0 ∧
          (∀ ell, eigenvalues (sourceBinaryGoodPrimeOfLevel hQM ell) =
            (ell.val : F) ^ j * values ell) ∧
          ∀ ell, sourceBinaryFlagUntwistedOperators F p M hpM n j ell y = values ell • y := by
  obtain ⟨M, hQM, hpM, hM, y, hy, he⟩ :=
    prime_divisible_level F Q p n hp eigenvalues x hx heig
  letI : NeZero M := ⟨by
    intro hzero
    rw [hzero, zero_dvd_iff] at hM
    exact mul_ne_zero (NeZero.ne Q) hp.ne_zero hM⟩
  obtain ⟨j, hj, hmod, hchar, values, z, hz, hvalues, hze⟩ :=
    sourceBinaryH1_exists_untwistedCharacterPiece F p M hpM n hp _ y hy he
  exact ⟨M, hQM, hpM, hM, j, hj, hmod, hchar, values, z, hz, hvalues, hze⟩

end
end Dubon2026
