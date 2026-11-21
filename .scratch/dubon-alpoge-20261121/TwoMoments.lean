import Dubon2026.CuspSatoTateConcentration
import Dubon2026.PrimitiveNormalizedRecurrence

/-! # Modular concentration from the second and sixth prime-power averages -/

namespace Dubon2026

open Filter Set MeasureTheory Polynomial
open scoped Topology

noncomputable section

/-- This signed combination of just two characters is nonpositive outside the
source coefficient band, including outside the entire tempered interval. -/
private theorem two_character_band_bound (x : ℝ) :
    1 + 2 * (Chebyshev.S ℝ 2).eval x - (Chebyshev.S ℝ 6).eval x ≤
      if 1 ≤ |x| ∧ |x| ≤ 2 then 9 else 0 := by
  have hid : 1 + 2 * (Chebyshev.S ℝ 2).eval x - (Chebyshev.S ℝ 6).eval x =
      x^2 * ((x^2 - 1) * (4 - x^2)) := by
    rw [show (6 : ℤ) = 4 + 2 by decide, Chebyshev.S_add_two,
      show (4 + 1 : ℤ) = 3 + 2 by decide, Chebyshev.S_add_two,
      show (4 : ℤ) = 2 + 2 by decide, Chebyshev.S_add_two,
      show (3 : ℤ) = 1 + 2 by decide, Chebyshev.S_add_two]
    norm_num [Chebyshev.S_two, Chebyshev.S_one, Chebyshev.S_zero] <;> ring
  rw [hid, ← sq_abs x]
  split_ifs with h
  · have ht : |x| ^ 2 ≤ 4 := by nlinarith [sq_nonneg (2 - |x|), mul_self_le_mul_self (abs_nonneg x) h.2]
    have hb : (|x| ^ 2 - 1) * (4 - |x| ^ 2) ≤ 9 / 4 := by nlinarith [sq_nonneg (|x| ^ 2 - 5 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg |x|)]
  · push_neg at h
    apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    by_cases hl : 1 ≤ |x|
    · have ht := h hl
      have ht' := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2) ht.le
      apply mul_nonpos_of_nonneg_of_nonpos <;> nlinarith
    · have hx := abs_nonneg x
      have ht := mul_self_le_mul_self hx (le_of_not_ge hl)
      apply mul_nonpos_of_nonpos_of_nonneg <;> nlinarith

/-- A prime-count normalized mean transfers to the open/closed dyadic interval. -/
private theorem dyadic_prime_sum_of_mean {u : ℕ → ℝ} {c : ℝ}
    (hu : Tendsto (fun N => (∑ p ∈ Nat.primesLE N, u p) / Nat.primeCounting N)
      atTop (𝓝 c)) :
    Tendsto (fun N => (∑ p ∈ dyadicPrimes N, u p) / ((N : ℝ) / Real.log N))
      atTop (𝓝 (c / 2)) := by
  have hf : Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) /
      ((N : ℝ) / Real.log N)) atTop (𝓝 1) := by
    simpa only [one_mul, Nat.floor_natCast] using tendsto_primeCounting_scaled (c := 1) (by norm_num)
  have hh : Tendsto (fun N : ℕ => (Nat.primeCounting (N / 2) : ℝ) /
      ((N : ℝ) / Real.log N)) atTop (𝓝 (1 / 2)) := by
    have he (N : ℕ) : (1 / 2 : ℝ) * N = (N : ℝ) / (2 : ℕ) := by push_cast; ring
    simpa only [he, Nat.floor_div_eq_div] using tendsto_primeCounting_scaled (c := 1/2) (by norm_num)
  have h := (hu.mul hf).sub ((hu.comp tendsto_nat_half_atTop).mul hh)
  rw [show c * 1 - c * (1 / 2) = c / 2 by ring] at h
  apply h.congr'
  filter_upwards [Nat.tendsto_primeCounting.eventually_ge_atTop 1,
    (Nat.tendsto_primeCounting.comp tendsto_nat_half_atTop).eventually_ge_atTop 1] with N hN hM
  change 1 ≤ Nat.primeCounting (N / 2) at hM
  have hsub : Nat.primesLE (N / 2) ⊆ Nat.primesLE N := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.div_le_self N 2),
      (Nat.mem_primesLE.mp hp).2⟩
  have he := Finset.sum_sdiff hsub (f := u)
  rw [dyadicPrimes_eq_sdiff, ← he, add_div]
  have hp : (Nat.primeCounting N : ℝ) ≠ 0 := by exact_mod_cast (show Nat.primeCounting N ≠ 0 by omega)
  have hq : (Nat.primeCounting (N / 2) : ℝ) ≠ 0 := by exact_mod_cast (show Nat.primeCounting (N / 2) ≠ 0 by omega)
  simp only [Function.comp_apply]
  field_simp
  <;> ring

end
end Dubon2026
