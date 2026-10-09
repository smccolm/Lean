import Dubon2026.MatrixIdealPowerProducts
import Mathlib.Algebra.CharP.Lemmas

/-! # Actual prime-power improvement of matrix congruences -/

namespace Dubon2026

open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Raising an original matrix congruent to one to the residue prime improves its actual ideal-power congruence. -/
theorem matrix_prime_congruence (I : Ideal R) {p r : ℕ}
    (hp : p.Prime) (hpI : (p : R) ∈ I) (hr : 1 ≤ r)
    (X : Matrix ι ι R) (hX : X - 1 ∈ (I ^ r).matrix ι) :
    X ^ p - 1 ∈ (I ^ (r + 1)).matrix ι := by
  let Y := X - 1
  have hY : Y ∈ (I ^ r).matrix ι := hX
  have hexponent : r + 1 ≤ r * p := calc
    r + 1 ≤ r + r := Nat.add_le_add_left hr r
    _ = r * 2 := by omega
    _ ≤ r * p := Nat.mul_le_mul_left r hp.two_le
  have hYp : Y ^ p ∈ (I ^ (r + 1)).matrix ι := by
    apply Ideal.matrix_monotone ι (Ideal.pow_le_pow_right hexponent)
    simpa only [pow_mul] using matrixIdeal_pow_mem (I ^ r) hY p
  have hpY : (p : Matrix ι ι R) * Y ∈ (I ^ (r + 1)).matrix ι := by
    rw [pow_succ']
    exact matrixIdeal_mul_mem I (I ^ r) (matrixIdeal_natCast_mem I p hpI) hY
  obtain ⟨Z, hZ⟩ := (Commute.one_left Y).exists_add_pow_prime_eq hp
  have hsum : (1 : Matrix ι ι R) + Y = X := by dsimp [Y]; abel_nf
  rw [hsum, one_pow, mul_one] at hZ
  have hdifference : X ^ p - 1 = Y ^ p + ((p : Matrix ι ι R) * Y) * Z := by
    rw [hZ]
    abel_nf
  rw [hdifference]
  exact ((I ^ (r + 1)).matrix ι).add_mem hYp
    (matrixIdeal_mul_right_mem (I ^ (r + 1)) hpY Z)

/-- Every original matrix congruent to one gains one actual ideal-power order at each prime-power iteration. -/
theorem matrix_primePower_congruence (I : Ideal R) {p : ℕ}
    (hp : p.Prime) (hpI : (p : R) ∈ I)
    (X : Matrix ι ι R) (hX : X - 1 ∈ I.matrix ι) (n : ℕ) :
    X ^ (p ^ n) - 1 ∈ (I ^ (n + 1)).matrix ι := by
  induction n with
  | zero => simpa using hX
  | succ n ih =>
    rw [pow_succ p n, pow_mul]
    exact matrix_prime_congruence I hp hpI (Nat.succ_pos n) (X ^ (p ^ n)) ih

/-- Nilpotence of the original coefficient ideal forces a genuine prime-power order for each original congruence matrix. -/
theorem matrix_primePower_eq_one_of_nilpotent (I : Ideal R) {p N : ℕ}
    (hp : p.Prime) (hpI : (p : R) ∈ I) (hI : I ^ N = ⊥)
    (X : Matrix ι ι R) (hX : X - 1 ∈ I.matrix ι) : X ^ (p ^ N) = 1 := by
  have h := matrix_primePower_congruence I hp hpI X hX N
  have hm : X ^ (p ^ N) - 1 ∈ (I ^ N).matrix ι :=
    Ideal.matrix_monotone ι (Ideal.pow_le_pow_right (Nat.le_succ N)) h
  rw [hI, Ideal.matrix_bot] at hm
  exact sub_eq_zero.mp hm

end Dubon2026
