import TaoTrudgianYang2025.PrimitiveTripleGcd

/-! Exact normalization of an arbitrary integer triple by its actual common gcd. -/

namespace TaoTrudgianYang2025

def integerTripleGcd (a b c : ℤ) : ℕ := Int.gcd (Int.gcd a b : ℤ) c

theorem integerTripleGcd_dvd (a b c : ℤ) :
    (integerTripleGcd a b c:ℤ) ∣ a ∧
      (integerTripleGcd a b c:ℤ) ∣ b ∧
      (integerTripleGcd a b c:ℤ) ∣ c := by
  have hg := Int.gcd_dvd_left (Int.gcd a b:ℤ) c
  exact ⟨dvd_trans hg (Int.gcd_dvd_left a b),
    dvd_trans hg (Int.gcd_dvd_right a b),
    Int.gcd_dvd_right (Int.gcd a b:ℤ) c⟩

theorem integerTripleGcd_pos {a b c : ℤ} (ha : a ≠ 0) :
    0 < integerTripleGcd a b c := by
  apply Int.gcd_pos_of_ne_zero_left
  exact_mod_cast (Int.gcd_pos_of_ne_zero_left b ha).ne'

theorem integerTripleGcd_le_natAbs {a b c : ℤ} (ha : a ≠ 0) :
    integerTripleGcd a b c ≤ a.natAbs := by
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr ha)
  simpa only [Int.natAbs_natCast] using
    Int.natAbs_dvd_natAbs.mpr (integerTripleGcd_dvd a b c).1

theorem integerTripleGcd_mul_nat (g : ℕ) (a b c : ℤ) :
    integerTripleGcd ((g:ℤ)*a) ((g:ℤ)*b) ((g:ℤ)*c) =
      g*integerTripleGcd a b c := by
  unfold integerTripleGcd
  rw [Int.gcd_mul_left,Int.natAbs_natCast,Nat.cast_mul,
    Int.gcd_mul_left,Int.natAbs_natCast]

theorem integerTripleGcd_quotient_primitive {a b c : ℤ} (ha : a ≠ 0) :
    integerTripleGcd
      (a/(integerTripleGcd a b c:ℤ))
      (b/(integerTripleGcd a b c:ℤ))
      (c/(integerTripleGcd a b c:ℤ)) = 1 := by
  let g := integerTripleGcd a b c
  have hd := integerTripleGcd_dvd a b c
  have he := integerTripleGcd_mul_nat g (a/(g:ℤ)) (b/(g:ℤ)) (c/(g:ℤ))
  rw [Int.mul_ediv_cancel_of_dvd hd.1,Int.mul_ediv_cancel_of_dvd hd.2.1,
    Int.mul_ediv_cancel_of_dvd hd.2.2] at he
  apply Nat.eq_of_mul_eq_mul_left (integerTripleGcd_pos ha)
  simpa only [Nat.mul_one] using he.symm

end TaoTrudgianYang2025

