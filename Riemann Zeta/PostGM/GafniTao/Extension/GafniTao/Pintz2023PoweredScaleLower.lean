import GafniTao.Pintz2023Equation416

/-!
# Pintz (2023), powered-block lower scale

Equation (4.16) records the strict logarithmic inequality selecting the first
power past the ell-threshold.  This file converts that statement back to the
physical lower bound for the actual second dyadic block `2^q U^h`.
-/

namespace GafniTao

noncomputable section

/-- A strict logarithmic lower bound for `U^h` gives the corresponding
physical `T`-power lower bound, and the dyadic factor can only enlarge it. -/
theorem pintz2023_critical_rpow_lt_powered_dyadic
    {T a : ℝ} {U q h : ℕ}
    (hT : 1 < T) (hU : 0 < U)
    (hScale : a < (h : ℝ) * pintz2023LogScale T U) :
    T ^ a < ((2 ^ q * U ^ h : ℕ) : ℝ) := by
  have hTPos : 0 < T := zero_lt_one.trans hT
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hUReal : (0 : ℝ) < U := by exact_mod_cast hU
  have hlog :
      a * Real.log T < (h : ℝ) * Real.log (U : ℝ) := by
    unfold pintz2023LogScale at hScale
    have hmul := mul_lt_mul_of_pos_right hScale hlogT
    field_simp [hlogT.ne'] at hmul
    nlinarith
  have hTaPos : 0 < T ^ a := Real.rpow_pos_of_pos hTPos a
  have hUhPos : 0 < (U : ℝ) ^ h := pow_pos hUReal h
  have hBase : T ^ a < (U : ℝ) ^ h := by
    rw [← Real.log_lt_log_iff hTaPos hUhPos]
    rw [Real.log_rpow hTPos, Real.log_pow]
    simpa [mul_comm] using hlog
  have hDyadicOne : (1 : ℝ) ≤ (2 : ℝ) ^ q := one_le_pow₀ (by norm_num)
  calc
    T ^ a < (U : ℝ) ^ h := hBase
    _ ≤ (2 : ℝ) ^ q * (U : ℝ) ^ h := by
      exact le_mul_of_one_le_left (pow_nonneg hUReal.le h) hDyadicOne
    _ = ((2 ^ q * U ^ h : ℕ) : ℝ) := by
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- Literal lower scale for the block selected by equation (4.16). -/
theorem pintz2023_equation416_critical_scale_lt
    {eta epsilon T : ℝ} {ell U q h : ℕ}
    (hT : 1 < T) (hU : 0 < U)
    (hScale : pintz2023EllThreshold eta epsilon ell <
      (h : ℝ) * pintz2023LogScale T U) :
    T ^ pintz2023EllThreshold eta epsilon ell <
      ((2 ^ q * U ^ h : ℕ) : ℝ) :=
  pintz2023_critical_rpow_lt_powered_dyadic hT hU hScale

#print axioms pintz2023_critical_rpow_lt_powered_dyadic
#print axioms pintz2023_equation416_critical_scale_lt

end

end GafniTao
