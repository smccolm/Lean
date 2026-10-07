import Dubon2026.PrimitiveFullCoefficients
import Dubon2026.CuspSelfTwists

/-! # Prime self-twists and the actual full coprime coefficient system -/

namespace Dubon2026

noncomputable section

/-- Character values on natural indices respect multiplication. -/
theorem characterCoefficients_mul {D : ℕ} (χ : DirichletCharacter ℂ D) (n m : ℕ) :
    characterCoefficients χ (n * m) = characterCoefficients χ n * characterCoefficients χ m := by
  simp only [characterCoefficients, Nat.cast_mul, map_mul]

/-- Character values on natural indices respect every nonnegative power. -/
theorem characterCoefficients_pow {D : ℕ} (χ : DirichletCharacter ℂ D) (n r : ℕ) :
    characterCoefficients χ (n ^ r) = characterCoefficients χ n ^ r := by
  simp only [characterCoefficients, Nat.cast_pow, map_pow]

/-- A quadratic character squares to one at every index coprime to its modulus. -/
theorem quadratic_characterCoefficients_sq {D n : ℕ} (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsQuadratic) (hn : n.Coprime D) : characterCoefficients χ n ^ 2 = 1 := by
  rcases hχ (n : ZMod D) with hz | ho | hm
  · have hnorm := norm_characterCoefficients_of_coprime χ hn
    change characterCoefficients χ n = 0 at hz
    rw [hz, norm_zero] at hnorm
    exact (zero_ne_one hnorm).elim
  · change characterCoefficients χ n = 1 at ho
    rw [ho, one_pow]
  · change characterCoefficients χ n = -1 at hm
    rw [hm]
    norm_num

/-- The true Hecke recurrence extends a quadratic prime self-twist to its good prime powers. -/
theorem primitiveCuspForm_selfTwist_primePower {Q D : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic)
    (ht : IsCoefficientSelfTwist Q χ (cuspCoefficients f.toCuspForm))
    {p : ℕ} (hp : Nat.Prime p) (hpQD : p.Coprime (Q * D)) (r : ℕ) :
    characterCoefficients χ (p ^ r) * cuspCoefficients f.toCuspForm (p ^ r) =
      cuspCoefficients f.toCuspForm (p ^ r) := by
  have hs := quadratic_characterCoefficients_sq χ hχ (Nat.coprime_mul_iff_right.mp hpQD).2
  have ht' := ht p hp hpQD
  simp only [characterCoefficients_pow]
  induction r using Nat.twoStepInduction with
  | zero => rw [pow_zero, one_mul]
  | one => simpa only [pow_one] using ht'
  | more r ih0 ih1 =>
    rw [primitiveCuspForm_primePower_recurrence f hp, mul_sub]
    congr 1
    · calc
        _ = (characterCoefficients χ p * cuspCoefficients f.toCuspForm p) *
            (characterCoefficients χ p ^ (r + 1) * cuspCoefficients f.toCuspForm (p ^ (r + 1))) := by
          rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
          ring
        _ = _ := by rw [ht', ih1]
    · rw [pow_add, hs, mul_one]
      calc
        _ = heckeDivisorWeight Q k p *
            (characterCoefficients χ p ^ r * cuspCoefficients f.toCuspForm (p ^ r)) := by ring
        _ = _ := by rw [ih0]

/-- A quadratic prime self-twist of a genuine primitive form fixes every coprime coefficient. -/
theorem primitiveCuspForm_selfTwist_coefficients {Q D : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic)
    (ht : IsCoefficientSelfTwist Q χ (cuspCoefficients f.toCuspForm)) (n : ℕ)
    (hn : n.Coprime (Q * D)) :
    characterCoefficients χ n * cuspCoefficients f.toCuspForm n = cuspCoefficients f.toCuspForm n := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => rw [cuspCoefficients_zero, mul_zero]
  | prime_pow p r hp =>
    by_cases hr : r = 0
    · subst r
      rw [pow_zero, characterCoefficients_one, one_mul]
    · exact primitiveCuspForm_selfTwist_primePower f χ hχ ht hp
        (hn.of_dvd_left (dvd_pow_self p hr)) r
  | coprime n m _ _ hnm ihn ihm =>
    have hn' := (Nat.coprime_mul_iff_left.mp hn).1
    have hm' := (Nat.coprime_mul_iff_left.mp hn).2
    rw [characterCoefficients_mul, primitiveCuspForm_coefficient_mul_all f n m hnm]
    calc
      _ = (characterCoefficients χ n * cuspCoefficients f.toCuspForm n) *
          (characterCoefficients χ m * cuspCoefficients f.toCuspForm m) := by ring
      _ = _ := by rw [ihn hn', ihm hm']

/-- The good-prime and full coprime formulations of quadratic self-twist agree on primitive forms. -/
theorem primitiveCuspForm_selfTwist_iff {Q D : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic) :
    IsCoefficientSelfTwist Q χ (cuspCoefficients f.toCuspForm) ↔
      ∀ n : ℕ, n.Coprime (Q * D) →
        characterCoefficients χ n * cuspCoefficients f.toCuspForm n = cuspCoefficients f.toCuspForm n := by
  exact ⟨fun ht n hn => primitiveCuspForm_selfTwist_coefficients f χ hχ ht n hn,
    fun ht p _ hp => ht p hp⟩

end
end Dubon2026
