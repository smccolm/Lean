import GafniTao.SharpPerronEdges

/-!
# Physical-variable sharp Perron bounds

This file transports the exact scalar contour estimates to the ratio `x/n`
appearing in the von Mangoldt Dirichlet series.  The strict inequalities are
kept visible because the discontinuity at an integral endpoint is handled
separately in the sharp explicit formula.
-/

namespace GafniTao

/-- Below the physical endpoint, the finite Perron kernel differs from the
sharp cutoff value one by the classical logarithmic error. -/
theorem norm_sharpPerronKernel_sub_one_le_of_natCast_lt
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hT : 0 < T)
    (hx : 0 < x) (hn : 1 ≤ n) (hnx : (n : ℝ) < x) :
    ‖sharpPerronKernel c T x n - 1‖ ≤
      (x / (n : ℝ)) ^ c /
        (Real.pi * T * Real.log (x / (n : ℝ))) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hratio : 1 < x / (n : ℝ) := (one_lt_div hnpos).2 hnx
  rw [sharpPerronKernel_eq_ratioKernel hx hn]
  exact norm_sharpPerronRatioKernel_sub_one_le_of_one_lt hratio hc hT

/-- Above the physical endpoint, the finite Perron kernel differs from the
sharp cutoff value zero by the classical logarithmic error. -/
theorem norm_sharpPerronKernel_le_of_natCast_lt
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hT : 0 < T)
    (hx : 0 < x) (hn : 1 ≤ n) (hxn : x < (n : ℝ)) :
    ‖sharpPerronKernel c T x n‖ ≤
      (x / (n : ℝ)) ^ c /
        (Real.pi * T * (-Real.log (x / (n : ℝ)))) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hratioPos : 0 < x / (n : ℝ) := div_pos hx hnpos
  have hratio : x / (n : ℝ) < 1 := (div_lt_one hnpos).2 hxn
  rw [sharpPerronKernel_eq_ratioKernel hx hn]
  exact norm_sharpPerronRatioKernel_le_of_lt_one hratioPos hratio hc hT

/-- At an integral endpoint we retain an explicit, uniform bound rather than
silently choosing a value for the discontinuous sharp cutoff. -/
theorem norm_sharpPerronKernel_at_natCast_le
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hx : 0 < x)
    (hn : 1 ≤ n) (hxn : x = (n : ℝ)) :
    ‖sharpPerronKernel c T x n‖ ≤ |T| / (Real.pi * c) := by
  subst x
  have h := norm_sharpPerronKernel_le (T := T) hc hx hn
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hpow : 0 < (n : ℝ) ^ c := Real.rpow_pos_of_pos hnpos c
  simpa [hpow.ne'] using h

end GafniTao
