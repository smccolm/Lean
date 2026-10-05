import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The actual positive-index zeta sum

The zero coefficient is explicitly zero. All source sums start at one, and
the cutoff is the natural floor of the real argument, including arguments below one.
-/

namespace DongWangWangZhang2026

open Complex Finset
open scoped BigOperators

noncomputable section

/-- The completely multiplicative phase, extended by zero at the excluded index. -/
def zetaTerm (t : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (n : ℂ) ^ ((t : ℂ) * I)

@[simp] theorem zetaTerm_zero (t : ℝ) : zetaTerm t 0 = 0 := by
  simp [zetaTerm]

theorem zetaTerm_eq_cpow (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    zetaTerm t n = (n : ℂ) ^ ((t : ℂ) * I) := by
  simp [zetaTerm, hn]

@[simp] theorem zetaTerm_one (t : ℝ) : zetaTerm t 1 = 1 := by
  simp [zetaTerm]

theorem zetaTerm_eq_exp (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    zetaTerm t n = Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) := by
  rw [zetaTerm_eq_cpow t hn, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
    ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem norm_zetaTerm (t : ℝ) {n : ℕ} (hn : 0 < n) : ‖zetaTerm t n‖ = 1 := by
  rw [zetaTerm_eq_cpow t (Nat.ne_of_gt hn), Complex.norm_natCast_cpow_of_pos hn]
  simp

theorem zetaTerm_mul (t : ℝ) (m n : ℕ) :
    zetaTerm t (m * n) = zetaTerm t m * zetaTerm t n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [zetaTerm_eq_cpow t hm, zetaTerm_eq_cpow t hn,
    zetaTerm_eq_cpow t (mul_ne_zero hm hn), Nat.cast_mul]
  exact Complex.natCast_mul_natCast_cpow m n _

theorem zetaTerm_neg (t : ℝ) (n : ℕ) :
    zetaTerm (-t) n = star (zetaTerm t n) := by
  by_cases hn : n = 0
  · simp [hn]
  rw [zetaTerm_eq_exp _ hn, zetaTerm_eq_exp _ hn]
  change Complex.exp _ = (starRingEnd ℂ) (Complex.exp _)
  rw [← Complex.exp_conj]
  congr 1
  simp only [neg_mul, Complex.ofReal_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem zetaTerm_add (t u : ℝ) (n : ℕ) :
    zetaTerm (t + u) n = zetaTerm t n * zetaTerm u n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [zetaTerm_eq_exp _ hn, zetaTerm_eq_exp _ hn, zetaTerm_eq_exp _ hn,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem zetaTerm_sub (t u : ℝ) (n : ℕ) :
    zetaTerm (t - u) n = zetaTerm t n * star (zetaTerm u n) := by
  rw [sub_eq_add_neg, zetaTerm_add, zetaTerm_neg]

/-- `S(x,t)` from equation (1.1), with the source's positive-index convention. -/
def zetaSum (x t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, zetaTerm t n

theorem zetaSum_eq_sum_exp (x t : ℝ) :
    zetaSum x t = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) := by
  apply Finset.sum_congr rfl
  intro n hn
  exact zetaTerm_eq_exp t (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)

theorem zetaSum_eq_zero_of_lt_one {x : ℝ} (hx : x < 1) (t : ℝ) :
    zetaSum x t = 0 := by
  simp [zetaSum, Nat.floor_eq_zero.mpr hx]

theorem zetaSum_neg (x t : ℝ) : zetaSum x (-t) = star (zetaSum x t) := by
  simp [zetaSum, zetaTerm_neg]

theorem norm_zetaSum_neg (x t : ℝ) : ‖zetaSum x (-t)‖ = ‖zetaSum x t‖ := by
  rw [zetaSum_neg, norm_star]

theorem norm_zetaSum_le_floor (x t : ℝ) : ‖zetaSum x t‖ ≤ ⌊x⌋₊ := by
  calc
    ‖zetaSum x t‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖zetaTerm t n‖ := norm_sum_le _ _
    _ = ⌊x⌋₊ := by
      rw [Finset.sum_congr rfl (fun n hn => norm_zetaTerm t (Finset.mem_Icc.mp hn).1)]
      simp

theorem norm_zetaSum_le {x : ℝ} (hx : 0 ≤ x) (t : ℝ) : ‖zetaSum x t‖ ≤ x :=
  (norm_zetaSum_le_floor x t).trans (Nat.floor_le hx)

theorem norm_normalized_zetaSum_exp_le_one (y t : ℝ) :
    ‖zetaSum (Real.exp y) t / (Real.exp y : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos y).le]
  exact (div_le_one (Real.exp_pos y)).mpr (norm_zetaSum_le (Real.exp_pos y).le t)

/-- The phase shifts the spectral argument by `-it`, with no zero-index artifact. -/
theorem zetaTerm_div_cpow (t : ℝ) {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    zetaTerm t n / (n : ℂ) ^ s = 1 / (n : ℂ) ^ (s - (t : ℂ) * I) := by
  have hs' : 1 < (s - (t : ℂ) * I).re := by simpa using hs
  by_cases hn : n = 0
  · simp [hn, Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs')]
  rw [zetaTerm_eq_cpow t hn, ← Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hn),
    one_div, ← Complex.cpow_neg]
  congr 1
  ring

theorem summable_zetaTerm_div_cpow (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => zetaTerm t n / (n : ℂ) ^ s) := by
  simp_rw [zetaTerm_div_cpow t hs]
  apply Complex.summable_one_div_nat_cpow.mpr
  simpa using hs

/-- The absolutely convergent Dirichlet series in the introduction. -/
theorem tsum_zetaTerm_div_cpow (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, zetaTerm t n / (n : ℂ) ^ s) = riemannZeta (s - (t : ℂ) * I) := by
  simp_rw [zetaTerm_div_cpow t hs]
  exact (zeta_eq_tsum_one_div_nat_cpow (by simpa using hs)).symm

end
end DongWangWangZhang2026
