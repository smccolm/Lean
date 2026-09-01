import GafniTao.FordJacobianAvoidance
import Mathlib.Data.Nat.Choose.Basic

/-!
# Ford Lemma 3.2: exact arithmetic ledger

This file records the two simplifications used between Ford equations (3.4)
and (3.7).  In particular, the half-integral-looking source exponent is kept
as an equality over `ℝ`; no ceiling or silently enlarged power is introduced.
-/

namespace GafniTao

/-- The exponent in Ford equation (3.7) is exactly the exponent displayed in
Lemma 3.2. -/
theorem ford_lemma_3_2_exponent_identity
    {r d s : ℕ} (hdr : d < r) (hds : d ≤ s) :
    (2 * s - d : ℕ) +
          ((r - d - 1) * (r - d) : ℕ) / 2 + r * d =
        2 * (s : ℝ) +
          ((r : ℝ) ^ 2 - r + (d : ℝ) ^ 2 - d) / 2 := by
  push_cast [Nat.cast_sub (show d ≤ 2 * s by omega),
    Nat.cast_sub hdr.le, Nat.cast_sub (show 1 ≤ r - d by omega)]
  ring

/-- The factorial simplification `d! (k-d)! ≤ k!` used in (3.7). -/
theorem ford_factorial_mul_factorial_sub_le_factorial
    {d k : ℕ} (hdk : d ≤ k) :
    d.factorial * (k - d).factorial ≤ k.factorial := by
  exact Nat.le_of_dvd (Nat.factorial_pos k)
    (Nat.factorial_mul_factorial_dvd_factorial hdk)

#print axioms ford_lemma_3_2_exponent_identity
#print axioms ford_factorial_mul_factorial_sub_le_factorial

end GafniTao
