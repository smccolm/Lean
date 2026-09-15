import Tao2026.SylvesterSchurSqrtEnvelope

/-!
# An explicit central Sylvester--Schur tail

This file discharges the numerical gap exported by
`SylvesterSchurSqrtEnvelope` on the full central region `2k ≤ n ≤ 3k`, with
the concrete cutoff `34134 ≤ k`.  The proof is deliberately integral.  It
bounds `x` by `2^(sqrt x / 16)` once `sqrt x ≥ 320`, absorbs the resulting
subexponential factor into a quarter power of two, and proves the remaining
fixed-base exponential comparison by induction.
-/

namespace Tao2026

/-- A blockwise exponential bound used to dominate a quadratic polynomial. -/
theorem twoFiftySix_mul_succ_sq_le_two_pow {q : ℕ} (hq : 20 ≤ q) :
    256 * (q + 1) ^ 2 ≤ 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
      calc
        256 * (q + 1 + 1) ^ 2 ≤ 2 * (256 * (q + 1) ^ 2) := by
          nlinarith [sq_nonneg (q : ℤ)]
        _ ≤ 2 * 2 ^ q := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (q + 1) := by rw [pow_succ]; ring

/-- Above square-root `320`, an integer is bounded by an exponential in one
sixteenth of its square root. -/
theorem self_le_two_pow_sqrt_div_sixteen {x : ℕ}
    (hsqrt : 320 ≤ x.sqrt) :
    x ≤ 2 ^ (x.sqrt / 16) := by
  let s := x.sqrt
  let q := s / 16
  have hq : 20 ≤ q := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).2
    dsimp [q, s]
    omega
  have hsLt : s < 16 * (q + 1) := by
    simpa [q] using Nat.lt_mul_div_succ s (by norm_num : 0 < 16)
  have hsq : (s + 1) ^ 2 ≤ 256 * (q + 1) ^ 2 := by
    have hsLe : s + 1 ≤ 16 * (q + 1) := by omega
    calc
      (s + 1) ^ 2 ≤ (16 * (q + 1)) ^ 2 :=
        Nat.pow_le_pow_left hsLe 2
      _ = 256 * (q + 1) ^ 2 := by ring
  calc
    x ≤ (s + 1) ^ 2 := by
      dsimp [s]
      exact (Nat.lt_succ_sqrt' x).le
    _ ≤ 256 * (q + 1) ^ 2 := hsq
    _ ≤ 2 ^ q := twoFiftySix_mul_succ_sq_le_two_pow hq
    _ = 2 ^ (x.sqrt / 16) := by rfl

/-- The square-root factor at the endpoint `3k` is absorbed by `2^(k/4)`
from the explicit cutoff onward. -/
theorem three_mul_pow_sqrt_le_two_pow_quarter {k : ℕ}
    (hk : 34134 ≤ k) :
    (3 * k) ^ (3 * k).sqrt ≤ 2 ^ (k / 4) := by
  let s := (3 * k).sqrt
  let q := s / 16
  have hsqrt : 320 ≤ (3 * k).sqrt := by
    rw [Nat.le_sqrt]
    nlinarith
  have hx : 3 * k ≤ 2 ^ q := by
    simpa [q] using
      (self_le_two_pow_sqrt_div_sixteen (x := 3 * k) hsqrt)
  have hqMul : 16 * q ≤ s := by
    dsimp [q]
    exact Nat.mul_div_le s 16
  have hsSq : s * s ≤ 3 * k := by
    simpa [s, pow_two] using Nat.sqrt_le' (3 * k)
  have h16 : 16 * (q * s) ≤ 3 * k := by
    calc
      16 * (q * s) = (16 * q) * s := by ring
      _ ≤ s * s := Nat.mul_le_mul_right s hqMul
      _ ≤ 3 * k := hsSq
  have h4 : 4 * (q * s) ≤ k := by omega
  have hqs : q * s ≤ k / 4 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
    simpa [mul_comm] using h4
  calc
    (3 * k) ^ (3 * k).sqrt = (3 * k) ^ s := by rfl
    _ ≤ (2 ^ q) ^ s := Nat.pow_le_pow_left hx s
    _ = 2 ^ (q * s) := by rw [Nat.pow_mul]
    _ ≤ 2 ^ (k / 4) := Nat.pow_le_pow_right (by norm_num) hqs

/-- The fixed-base exponential comparison left after the square-root
absorption. -/
theorem eightyOne_mul_linear_mul_162_pow_lt_256_pow
    {q : ℕ} (hq : 20 ≤ q) :
    81 * (4 * q + 3) * 162 ^ q < 256 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
      have hratio : (4 * (q + 1) + 3) * 162 < (4 * q + 3) * 256 := by
        omega
      calc
        81 * (4 * (q + 1) + 3) * 162 ^ (q + 1) =
            (81 * 162 ^ q) * ((4 * (q + 1) + 3) * 162) := by
              rw [pow_succ]
              ring
        _ < (81 * 162 ^ q) * ((4 * q + 3) * 256) :=
          (Nat.mul_lt_mul_left (by positivity)).2 hratio
        _ = (81 * (4 * q + 3) * 162 ^ q) * 256 := by ring
        _ < 256 ^ q * 256 :=
          (Nat.mul_lt_mul_right (by norm_num : 0 < 256)).2 ih
        _ = 256 ^ (q + 1) := by rw [pow_succ]

/-- The elementary fixed-base gap needed after replacing the square-root
factor by `2^(k/4)`. -/
theorem two_pow_quarter_mul_three_pow_gap {k : ℕ} (hk : 80 ≤ k) :
    k * (2 ^ (k / 4) * 3 ^ (k + 1)) < 4 ^ k := by
  let q := k / 4
  have hq : 20 ≤ q := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
    simpa [q] using hk
  have hkLt : k < 4 * (q + 1) := by
    simpa [q] using Nat.lt_mul_div_succ k (by norm_num : 0 < 4)
  have hkLe : k ≤ 4 * q + 3 := by omega
  have hpowThree : 3 ^ (k + 1) ≤ 3 ^ (4 * (q + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hupper :
      k * (2 ^ q * 3 ^ (k + 1)) ≤ 81 * (4 * q + 3) * 162 ^ q := by
    calc
      k * (2 ^ q * 3 ^ (k + 1)) ≤
          (4 * q + 3) * (2 ^ q * 3 ^ (4 * (q + 1))) := by gcongr
      _ = 81 * (4 * q + 3) * 162 ^ q := by
        rw [show 4 * (q + 1) = 4 * q + 4 by ring, pow_add,
          Nat.pow_mul, show 3 ^ 4 = 81 by norm_num,
          ← mul_assoc (2 ^ q) (81 ^ q) 81,
          ← Nat.mul_pow 2 81 q]
        ring
  calc
    k * (2 ^ (k / 4) * 3 ^ (k + 1)) =
        k * (2 ^ q * 3 ^ (k + 1)) := by rfl
    _ ≤ 81 * (4 * q + 3) * 162 ^ q := hupper
    _ < 256 ^ q := eightyOne_mul_linear_mul_162_pow_lt_256_pow hq
    _ = 4 ^ (4 * q) := by rw [Nat.pow_mul]
    _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_div_le k 4)

/-- The explicit square-root/Hanson gap at the endpoint `n=3k`. -/
theorem sylvesterSchur_central_gap_at_triple {k : ℕ} (hk : 34134 ≤ k) :
    k * ((3 * k) ^ (3 * k).sqrt * 3 ^ (k + 1)) < 4 ^ k := by
  calc
    k * ((3 * k) ^ (3 * k).sqrt * 3 ^ (k + 1)) ≤
        k * (2 ^ (k / 4) * 3 ^ (k + 1)) := by
      have h := Nat.mul_le_mul_right (3 ^ (k + 1))
        (three_mul_pow_sqrt_le_two_pow_quarter hk)
      exact Nat.mul_le_mul_left k h
    _ < 4 ^ k := two_pow_quarter_mul_three_pow_gap (by omega)

/-- The gap is monotone throughout the full central region `n ≤ 3k`. -/
theorem sylvesterSchur_central_gap_of_le_triple
    {n k : ℕ} (hk : 34134 ≤ k) (hn : n ≤ 3 * k) :
    k * (n ^ n.sqrt * 3 ^ (n / 3 + 1)) < 4 ^ k := by
  have hsqrt : n.sqrt ≤ (3 * k).sqrt := Nat.sqrt_le_sqrt hn
  have hbase : n ^ n.sqrt ≤ (3 * k) ^ n.sqrt :=
    Nat.pow_le_pow_left hn n.sqrt
  have hexponent : (3 * k) ^ n.sqrt ≤ (3 * k) ^ (3 * k).sqrt :=
    Nat.pow_le_pow_right (by omega) hsqrt
  have hthird : n / 3 ≤ k := by omega
  have hthree : 3 ^ (n / 3 + 1) ≤ 3 ^ (k + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  calc
    k * (n ^ n.sqrt * 3 ^ (n / 3 + 1)) ≤
        k * ((3 * k) ^ (3 * k).sqrt * 3 ^ (k + 1)) := by
      exact Nat.mul_le_mul_left k
        (Nat.mul_le_mul (hbase.trans hexponent) hthree)
    _ < 4 ^ k := sylvesterSchur_central_gap_at_triple hk

/-- Every central binomial coefficient in the explicit tail has a prime
divisor above its lower index. -/
theorem exists_large_prime_dvd_choose_of_central_tail
    {n k : ℕ} (hk : 34134 ≤ k) (hhalf : 2 * k ≤ n)
    (hn : n ≤ 3 * k) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.choose k := by
  exact exists_large_prime_dvd_choose_of_sqrt_three_third_gap
    (by omega) hhalf (sylvesterSchur_central_gap_of_le_triple hk hn)

/-- Consecutive-product endpoint: all starts `k < N ≤ 2k` are closed once
`k ≥ 34134`. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_central_tail
    {N H : ℕ} (hH : 34134 ≤ H) (hHN : H < N) (hN : N ≤ 2 * H) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  exact exists_large_prime_dvd_consecutiveProduct_of_sqrt_three_third_gap
    (by omega) hHN (sylvesterSchur_central_gap_of_le_triple hH (by omega))

end Tao2026
