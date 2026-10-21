import Dubon2026.SourceBinaryLevelHecke
import Dubon2026.SourceBinaryH1HeckeAlgebra

/-! The original residual binary eigensystem at the required raised level.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> prime-divisible level with original good-prime eigenvalues. The actual
restriction, its injectivity, and its full Hecke compatibility construct
the new nonzero native H1 class.
-/

namespace Dubon2026
noncomputable section

/-- A prime good at a multiple of the original level is good at the original level. -/
def sourceBinaryGoodPrimeOfLevel {Q M : ℕ} (hQM : Q ∣ M)
    (ell : sourceBinaryHeckePrime M) : sourceBinaryHeckePrime Q :=
  ⟨ell.val, ell.property.1, ell.property.2.of_dvd_right hQM⟩

variable (F : Type) [Field F] (Q p n : ℕ) [CharP F p]

/-- At a prime outside the original level, every original nonzero residual
binary H1 eigensystem survives at level Q*p, with its original eigenvalues
at all primes good at Q*p. No nonvanishing or Hecke comparison is assumed. -/
theorem sourceBinaryH1_raiseLevel (hp : p.Prime) (hpQ : Nat.Coprime p Q)
    (eigenvalues : sourceBinaryHeckePrime Q → F)
    (x : groupCohomology.H1 (sourceBinaryCoefficientRep F Q n)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryH1PrimeOperators F Q n ell x = eigenvalues ell • x) :
    ∃ y : groupCohomology.H1 (sourceBinaryCoefficientRep F (Q * p) n),
      y ≠ 0 ∧ ∀ ell : sourceBinaryHeckePrime (Q * p),
        sourceBinaryH1PrimeOperators F (Q * p) n ell y =
          eigenvalues (sourceBinaryGoodPrimeOfLevel (dvd_mul_right Q p) ell) • y := by
  refine ⟨sourceBinaryLevelRestriction F Q p n x, ?_, ?_⟩
  · intro hzero
    exact hx (sourceBinaryLevelRestriction_injective F Q p n hp hpQ
      (hzero.trans (map_zero (sourceBinaryLevelRestriction F Q p n)).symm))
  · intro ell
    letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
    change sourceBinaryHeckeH1 F ell.property.1 n (sourceBinaryLevelRestriction F Q p n x) = _
    rw [← sourceBinaryLevelRestriction_hecke F Q p n ell.property.1 ell.property.2]
    have he := heig (sourceBinaryGoodPrimeOfLevel (dvd_mul_right Q p) ell)
    change sourceBinaryHeckeH1 F ell.property.1 n x = _ at he
    rw [he, map_smul]

end
end Dubon2026
