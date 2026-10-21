import Dubon2026.SourceCharacterTwistExponent

/-! Exact final exponent normalization for original binary-to-weight-two descent.
DUB-17/18 -> residual modular Galois association -> all-prime weight-two
reduction -> restoration of the original Fourier eigenvalue twist.
The actual descent congruence determines the source exponent; no
independent normalization relation is assumed.
-/

namespace Dubon2026

/-- The source twist exponent has exactly the complementary power modulo p-1. -/
theorem sourceWeightTwoTwist_sum (p : ℕ) (hp : p.Prime) (n j : ℕ) :
    n / 2 + (j + (p - 2) * (n / 2)) = j + (p - 1) * (n / 2) := by
  have hp2 := hp.two_le
  rw [show p - 1 = (p - 2) + 1 by omega]
  ring

/-- The actual binary-character congruence implies the required source
weight-two character-and-twist congruence, including characteristic two. -/
theorem sourceWeightTwoTwist_divisible (p : ℕ) (hp : p.Prime) (n j e : ℕ)
    (hn : Even n ∨ p = 2) (he : e + 2 * j ≡ n [MOD (p - 1)]) :
    (p - 1) ∣ e + 2 * (j + (p - 2) * (n / 2)) := by
  rcases hn with hn | rfl
  · obtain ⟨a, ha⟩ := hn
    have hn2 : 2 * (n / 2) = n := by omega
    have hp2 := hp.two_le
    apply Nat.modEq_zero_iff_dvd.mp
    calc
      e + 2 * (j + (p - 2) * (n / 2)) ≡
          (e + 2 * j) + (p - 2) * n [MOD (p - 1)] := by
        have hcalc : e + 2 * (j + (p - 2) * (n / 2)) =
            (e + 2 * j) + (p - 2) * n := by
          calc
            _ = (e + 2 * j) + (p - 2) * (2 * (n / 2)) := by ring
            _ = _ := by rw [hn2]
        exact congrArg (fun a => a % (p - 1)) hcalc
      _ ≡ n + (p - 2) * n [MOD (p - 1)] := he.add_right _
      _ ≡ 0 [MOD (p - 1)] := by
        apply Nat.modEq_zero_iff_dvd.mpr
        rw [show n + (p - 2) * n = (p - 1) * n by
          rw [show p - 1 = (p - 2) + 1 by omega]
          ring]
        exact dvd_mul_right _ _
  · exact one_dvd _

end Dubon2026
