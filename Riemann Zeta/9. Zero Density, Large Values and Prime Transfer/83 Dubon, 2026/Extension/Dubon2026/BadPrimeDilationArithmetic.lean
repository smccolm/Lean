import Dubon2026.HeckeDegeneracyPrime

/-! # Exact coefficient identities for bad-prime degeneracy maps -/

namespace Dubon2026

/-- The secondary prime term of a sparse dilation is exactly a dilation by the product. -/
theorem primeCoefficient_dilation_secondary (p d : ℕ) (a : ℕ → ℂ) (w : ℂ) (m : ℕ) :
    (if p ∣ m then w * (if d ∣ m / p then a (m / p / d) else 0) else 0) =
      w * (if p * d ∣ m then a (m / (p * d)) else 0) := by
  by_cases hpm : p ∣ m
  · rw [if_pos hpm]
    simp only [Nat.dvd_div_iff_mul_dvd hpm, Nat.div_div_eq_div_mul]
  · have hpd : ¬p * d ∣ m := fun h => hpm ((dvd_mul_right p d).trans h)
    rw [if_neg hpm, if_neg hpd, mul_zero]

/-- The exact defect between two prime transforms under a coprime coefficient dilation. -/
theorem primeCoefficient_dilation_defect {p d : ℕ} (hp : 0 < p) (hd : 0 < d)
    (hpd : Nat.Coprime p d) (a : ℕ → ℂ) (u w : ℂ) (m : ℕ) :
    (if d ∣ p * m then a (p * m / d) else 0) +
        (if p ∣ m then u * (if d ∣ m / p then a (m / p / d) else 0) else 0) =
      (if d ∣ m then a (p * (m / d)) +
        (if p ∣ m / d then w * a (m / d / p) else 0) else 0) +
      (u - w) * (if p * d ∣ m then a (m / (p * d)) else 0) := by
  have h := primeCoefficient_dilation hp hd hpd a w m
  rw [primeCoefficient_dilation_secondary] at h
  rw [primeCoefficient_dilation_secondary, ← h]
  ring1

/-- A bad prime dividing the dilation removes one copy of that prime from its support. -/
theorem primeCoefficient_dilation_divide {p d : ℕ} (hp : 0 < p) (hpd : p ∣ d)
    (a : ℕ → ℂ) (m : ℕ) :
    (if d ∣ p * m then a (p * m / d) else 0) =
      if d / p ∣ m then a (m / (d / p)) else 0 := by
  obtain ⟨r, rfl⟩ := hpd
  simp only [Nat.mul_div_cancel_left _ hp, Nat.mul_dvd_mul_iff_left hp,
    Nat.mul_div_mul_left _ _ hp]

end Dubon2026
