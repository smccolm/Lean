import Dubon2026.SourceCharacterWeightTwoAllPrimes
import Dubon2026.SourceWeightTwoTwistNormalization
import Dubon2026.SourceBinaryCharacterLevel

/-! Original binary H1 eigensystems descend to actual weight-two eigensystems.
DUB-17/18 -> residual modular Galois association -> residual weight/level
reduction. The original character descent, all-prime character reduction
and exact exponent restoration are composed. The final level divides Q*p^2,
and the original eigenvalue is ell^(n/2) times the weight-two eigenvalue.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] (Q p n : ℕ) [NeZero Q] [CharP F p]

/-- Every original nonzero binary H1 eigensystem of even degree, and every
degree in characteristic two, gives an actual nonzero weight-two eigensystem
at a level dividing Q*p squared with the exact original prime-power factor. -/
theorem sourceBinaryH1_exists_weightTwo (hp : p.Prime) (hn : Even n ∨ p = 2)
    (eigenvalues : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceBinaryCoefficientRep F Q n)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryH1PrimeOperators F Q n ell x = eigenvalues ell • x) :
    ∃ (N : ℕ) (hQN : Q ∣ N), N ∣ Q * p ^ 2 ∧
      ∃ (values : sourceBinaryHeckePrime N → F)
        (y : H1 (Rep.trivial F (Gamma0 N) F)), y ≠ 0 ∧
        (∀ ell : sourceBinaryHeckePrime N,
          eigenvalues (sourceBinaryGoodPrimeOfLevel hQN ell) = (ell.val : F) ^ (n / 2) * values ell) ∧
        ∀ ell, sourceTrivialCoefficientHeckeOperators F N ell y = values ell • y := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨M, hQM, hpM, hM, j, hj, hmod, _, values, z, hz, hzvalues, hez⟩ :=
    sourceBinaryH1_exists_characterLevel F Q p n hp eigenvalues x hx heig
  letI : NeZero M := ⟨by
    intro hm
    rw [hm, zero_dvd_iff] at hM
    exact mul_ne_zero (NeZero.ne Q) hp.ne_zero hM⟩
  let t := j + (p - 2) * (n / 2)
  have ht : (p - 1) ∣ sourceBinaryFlagExponentOf p n j + 2 * t :=
    sourceWeightTwoTwist_divisible p hp n j _ hn hmod
  obtain ⟨N, hMN, hN, y, hy, hey⟩ :=
    sourceBinaryCharacter_to_weightTwo_all_primes F p M hpM n j t hj ht values z hz hez
  have hQN : Q ∣ N := hQM.trans hMN
  have hNbound : N ∣ Q * p ^ 2 := by
    rw [pow_two, ← mul_assoc]
    exact hN.trans (mul_dvd_mul_right hM p)
  let valuesN : sourceBinaryHeckePrime N → F :=
    fun ell => (ell.val : F) ^ t * values (sourceBinaryGoodPrimeOfLevel hMN ell)
  refine ⟨N, hQN, hNbound, valuesN, y, hy, ?_, hey⟩
  intro ell
  have hvalues := hzvalues (sourceBinaryGoodPrimeOfLevel hMN ell)
  change eigenvalues (sourceBinaryGoodPrimeOfLevel hQN ell) =
    (ell.val : F) ^ j * values (sourceBinaryGoodPrimeOfLevel hMN ell) at hvalues
  rw [hvalues]
  change _ = (ell.val : F) ^ (n / 2) *
    ((ell.val : F) ^ t * values (sourceBinaryGoodPrimeOfLevel hMN ell))
  rw [← mul_assoc, ← pow_add, show n / 2 + t = j + (p - 1) * (n / 2) from
    sourceWeightTwoTwist_sum p hp n j, pow_add, pow_mul]
  have horder := sourceCharacter_goodPrime_pow_order F p M hpM
    (sourceBinaryGoodPrimeOfLevel hMN ell)
  change (ell.val : F) ^ (p - 1) = 1 at horder
  rw [horder, one_pow, mul_one]

end
end Dubon2026
