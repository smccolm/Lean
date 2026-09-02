import GafniTao.FordLemma34Parameters

/-!
# Ford Lemma 3.4: factorial constants

The final line of Ford Lemma 3.4 uses the explicit inequality
`4 k^3 k! ≤ k^k` for `k ≥ 11`.  We prove it by induction, keeping the
integer inequality exact before casting it into the analytic estimate.
-/

namespace GafniTao

theorem four_mul_cube_mul_factorial_le_self_pow
    {k : ℕ} (hk : 11 ≤ k) :
    4 * k ^ 3 * k.factorial ≤ k ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
      have hn3 : 3 ≤ n := by omega
      have hn0 : 0 < n := by omega
      have hmono : n ^ (n - 3) ≤ (n + 1) ^ (n - 3) :=
        Nat.pow_le_pow_left (Nat.le_succ n) _
      have hnSplit : n ^ n = n ^ (n - 3) * n ^ 3 := by
        rw [← pow_add]
        congr 1
        omega
      have hsuccSplit : (n + 1) ^ (n + 1) =
          (n + 1) ^ (n - 3) * (n + 1) ^ 4 := by
        rw [← pow_add]
        congr 1
        omega
      apply Nat.le_of_mul_le_mul_right (c := n ^ 3) _ (pow_pos hn0 3)
      calc
        (4 * (n + 1) ^ 3 * (n + 1).factorial) * n ^ 3 =
            (4 * n ^ 3 * n.factorial) * (n + 1) ^ 4 := by
          rw [Nat.factorial_succ]
          ring
        _ ≤ n ^ n * (n + 1) ^ 4 :=
          Nat.mul_le_mul_right _ ih
        _ = (n ^ (n - 3) * n ^ 3) * (n + 1) ^ 4 := by rw [hnSplit]
        _ ≤ ((n + 1) ^ (n - 3) * n ^ 3) * (n + 1) ^ 4 := by
          gcongr
        _ = (n + 1) ^ (n + 1) * n ^ 3 := by
          rw [hsuccSplit]
          ring

theorem four_mul_cube_mul_factorial_cast_le_self_pow
    {k : ℕ} (hk : 11 ≤ k) :
    (4 : ℝ) * k ^ 3 * k.factorial ≤ (k : ℝ) ^ k := by
  exact_mod_cast four_mul_cube_mul_factorial_le_self_pow hk

theorem two_mul_self_pow_le_succ_pow
    {k : ℕ} (hk : 1 ≤ k) :
    2 * k ^ k ≤ (k + 1) ^ k := by
  have hbern := pow_add_mul_le_add_pow (R := ℕ) (a := k) (b := 1)
    (Nat.zero_le k) (Nat.zero_le (2 * k + 1)) k
  have hpow : k * k ^ (k - 1) = k ^ k := by
    rw [← pow_succ']
    congr 1
    omega
  simpa [hpow, two_mul, add_comm, add_left_comm, add_assoc] using hbern

theorem four_mul_lower_power_le_succ_power
    {k : ℕ} (hk : 3 ≤ k) :
    4 * k ^ (2 * k - 3) ≤ (k + 1) ^ (2 * k - 2) := by
  have hfirst : 2 * k ^ k ≤ (k + 1) ^ k :=
    two_mul_self_pow_le_succ_pow (by omega)
  have hsecondA : 2 * k ^ (k - 3) ≤ k * k ^ (k - 3) := by
    gcongr
    omega
  have hsecondB : k * k ^ (k - 3) = k ^ (k - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have hsecond : 2 * k ^ (k - 3) ≤ (k + 1) ^ (k - 2) :=
    hsecondA.trans (by
      rw [hsecondB]
      exact Nat.pow_le_pow_left (Nat.le_succ k) _)
  have hmul := Nat.mul_le_mul hfirst hsecond
  have hexpLeft : k + (k - 3) = 2 * k - 3 := by omega
  have hexpRight : k + (k - 2) = 2 * k - 2 := by omega
  calc
    4 * k ^ (2 * k - 3) =
        (2 * k ^ k) * (2 * k ^ (k - 3)) := by
      rw [show (2 * k ^ k) * (2 * k ^ (k - 3)) =
          4 * (k ^ k * k ^ (k - 3)) by ring, ← pow_add, hexpLeft]
    _ ≤ (k + 1) ^ k * (k + 1) ^ (k - 2) := hmul
    _ = (k + 1) ^ (2 * k - 2) := by
      rw [← pow_add, hexpRight]

/-- Squared, denominator-cleared form of the first factorial inequality in
Ford Lemma 3.4. -/
theorem sixteen_mul_four_pow_cube_factorial_le_square_pow
    {k : ℕ} (hk : 8 ≤ k) :
    16 * 4 ^ k * k ^ 3 * k.factorial ≤ k ^ (2 * k) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
      have hn3 : 3 ≤ n := by omega
      have hn0 : 0 < n := by omega
      have hratio := four_mul_lower_power_le_succ_power hn3
      apply Nat.le_of_mul_le_mul_right (c := n ^ 3) _ (pow_pos hn0 3)
      calc
        (16 * 4 ^ (n + 1) * (n + 1) ^ 3 * (n + 1).factorial) * n ^ 3 =
            (16 * 4 ^ n * n ^ 3 * n.factorial) *
              (4 * (n + 1) ^ 4) := by
          rw [Nat.factorial_succ, pow_succ]
          ring
        _ ≤ n ^ (2 * n) * (4 * (n + 1) ^ 4) :=
          Nat.mul_le_mul_right _ ih
        _ = (4 * n ^ (2 * n - 3)) * (n ^ 3 * (n + 1) ^ 4) := by
          rw [show n ^ (2 * n) = n ^ (2 * n - 3) * n ^ 3 by
            rw [← pow_add]
            congr 1
            omega]
          ring
        _ ≤ (n + 1) ^ (2 * n - 2) * (n ^ 3 * (n + 1) ^ 4) := by
          exact Nat.mul_le_mul_right _ hratio
        _ = (n + 1) ^ (2 * (n + 1)) * n ^ 3 := by
          rw [show (n + 1) ^ (2 * (n + 1)) =
              (n + 1) ^ (2 * n - 2) * (n + 1) ^ 4 by
            rw [← pow_add]
            congr 1
            omega]
          ring

/-- Ford's first displayed factorial estimate, in the exact real form used
inside the square-root branch of Lemma 3.3. -/
theorem four_mul_sqrt_cube_factorial_le_two_pow_inv_mul_self_pow
    {k : ℕ} (hk : 8 ≤ k) :
    4 * √((k : ℝ) ^ 3 * k.factorial) ≤
      (k : ℝ) ^ k / (2 : ℝ) ^ k := by
  have hnat := sixteen_mul_four_pow_cube_factorial_le_square_pow hk
  have hcast :
      (16 : ℝ) * 4 ^ k * (k : ℝ) ^ 3 * k.factorial ≤
        (k : ℝ) ^ (2 * k) := by
    exact_mod_cast hnat
  have hA : 0 ≤ (k : ℝ) ^ 3 * k.factorial := by positivity
  have htwo : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) _
  rw [le_div_iff₀ htwo]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    (4 * √((k : ℝ) ^ 3 * k.factorial) * (2 : ℝ) ^ k) ^ 2 =
        (16 : ℝ) * 4 ^ k * (k : ℝ) ^ 3 * k.factorial := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA]
      have hpow : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
        rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        congr 1
        omega
      rw [hpow]
      ring
    _ ≤ (k : ℝ) ^ (2 * k) := hcast
    _ = ((k : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega

#print axioms four_mul_cube_mul_factorial_le_self_pow
#print axioms four_mul_cube_mul_factorial_cast_le_self_pow
#print axioms two_mul_self_pow_le_succ_pow
#print axioms four_mul_lower_power_le_succ_power
#print axioms sixteen_mul_four_pow_cube_factorial_le_square_pow
#print axioms four_mul_sqrt_cube_factorial_le_two_pow_inv_mul_self_pow

end GafniTao
