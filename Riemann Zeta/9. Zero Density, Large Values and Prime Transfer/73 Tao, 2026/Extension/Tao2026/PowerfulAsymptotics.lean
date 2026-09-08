import Tao2026.Asymptotics
import Tao2026.PowerfulNumbers
import Mathlib.Analysis.PSeries

/-!
# Elementary square-root asymptotics for one-term very-bad values

The square family (`b=1` in the unique `a²b³` representation) proves the
reverse-big-O half of square-root growth for both `VB¹` and `VB`.  The exact
finite sum for `VB¹` is dominated termwise by the convergent `b⁻³ᐟ²` series,
which supplies the matching upper half for `VB¹`. Identifying the exact
zeta-ratio leading constant remains a separate analytic task.
-/

open Filter Asymptotics

namespace Tao2026

private theorem power_half_sub_le_two_mul_veryBadOneTermCount
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖(n : ℝ) ^ ((1 / 2 : ℝ) - ε)‖ ≤
        2 * ‖(veryBadOneTermCount n : ℝ)‖ := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
  have hsqrtNat : 1 ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt']
    simpa using hn
  have hroot : Real.sqrt n ≤ 2 * (veryBadOneTermCount n : ℝ) := by
    calc
      Real.sqrt n ≤ (Nat.sqrt n : ℝ) + 1 :=
        Real.real_sqrt_le_nat_sqrt_succ
      _ ≤ 2 * (Nat.sqrt n : ℕ) := by
        norm_cast
        omega
      _ ≤ 2 * (veryBadOneTermCount n : ℝ) := by
        gcongr
        exact_mod_cast sqrt_le_veryBadOneTermCount n
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    Real.norm_of_nonneg
      (Nat.cast_nonneg (veryBadOneTermCount n) :
        0 ≤ (veryBadOneTermCount n : ℝ))]
  exact hpow.trans hroot

/-- The positive squares prove the reverse-big-O half of square-root growth
for the one-term very-bad count. -/
theorem veryBadOneTermCount_powerScale_lower :
    ∀ ε : ℝ, 0 < ε →
      ((fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - ε)) =O[atTop]
        fun n => (veryBadOneTermCount n : ℝ)) := by
  intro ε hε
  exact IsBigO.of_bound 2
    (power_half_sub_le_two_mul_veryBadOneTermCount ε hε)

/-- The reverse-big-O lower half transfers from `VB¹` to all very-bad
values. -/
theorem veryBadCount_powerScale_lower :
    ∀ ε : ℝ, 0 < ε →
      ((fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - ε)) =O[atTop]
        fun n => (veryBadCount n : ℝ)) := by
  intro ε hε
  refine IsBigO.of_bound 2 ?_
  filter_upwards
      [power_half_sub_le_two_mul_veryBadOneTermCount ε hε] with n hn
  calc
    ‖(n : ℝ) ^ ((1 / 2 : ℝ) - ε)‖ ≤
        2 * ‖(veryBadOneTermCount n : ℝ)‖ := hn
    _ ≤ 2 * ‖(veryBadCount n : ℝ)‖ := by
      rw [Real.norm_of_nonneg
          (Nat.cast_nonneg (veryBadOneTermCount n) :
            0 ≤ (veryBadOneTermCount n : ℝ)),
        Real.norm_of_nonneg
          (Nat.cast_nonneg (veryBadCount n) :
            0 ≤ (veryBadCount n : ℝ))]
      gcongr
      exact_mod_cast countUpTo_mono
        veryBadOneTermSet_subset_veryBadSet n

/-- A fixed convergent majorant for the squarefree-cube sum. Keeping the
zero term is harmless because real `rpow` assigns it value zero at a negative
exponent. -/
noncomputable def powerfulPSeriesConstant : ℝ :=
  ∑' b : ℕ, (b : ℝ) ^ (-(3 / 2 : ℝ))

theorem summable_powerfulPSeries :
    Summable (fun b : ℕ => (b : ℝ) ^ (-(3 / 2 : ℝ))) := by
  rw [Real.summable_nat_rpow]
  norm_num

theorem powerfulPSeriesConstant_nonneg : 0 ≤ powerfulPSeriesConstant := by
  exact tsum_nonneg fun b => Real.rpow_nonneg (Nat.cast_nonneg b) _

/-- Each summand in the exact `VB¹` count is bounded by the corresponding
term of the real `b⁻³ᐟ²` majorant. -/
theorem cast_sqrt_div_cube_le (x b : ℕ) :
    (Nat.sqrt (x / b ^ 3) : ℝ) ≤
      Real.sqrt x * (b : ℝ) ^ (-(3 / 2 : ℝ)) := by
  calc
    (Nat.sqrt (x / b ^ 3) : ℝ) ≤ Real.sqrt (x / b ^ 3 : ℕ) :=
      Real.nat_sqrt_le_real_sqrt
    _ ≤ Real.sqrt ((x : ℝ) / (b ^ 3 : ℕ)) := by
      exact Real.sqrt_le_sqrt Nat.cast_div_le
    _ = Real.sqrt x / Real.sqrt (b ^ 3 : ℕ) := by
      rw [Real.sqrt_div (Nat.cast_nonneg x)]
    _ = Real.sqrt x * (b : ℝ) ^ (-(3 / 2 : ℝ)) := by
      simp only [Real.sqrt_eq_rpow]
      rw [show ((b ^ 3 : ℕ) : ℝ) = (b : ℝ) ^ (3 : ℕ) by norm_cast,
        ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg b)]
      norm_num
      rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg b)]

/-- The exact finite powerful-number sum is at most a fixed multiple of
`√x`. -/
theorem veryBadOneTermCount_le_sqrt_mul_pSeries (x : ℕ) :
    (veryBadOneTermCount x : ℝ) ≤
      Real.sqrt x * powerfulPSeriesConstant := by
  rw [veryBadOneTermCount_eq_sum_sqrt_div_cube]
  push_cast
  calc
    ∑ b ∈ (Finset.Icc 1 x).filter Squarefree,
        (Nat.sqrt (x / b ^ 3) : ℝ) ≤
      ∑ b ∈ (Finset.Icc 1 x).filter Squarefree,
        Real.sqrt x * (b : ℝ) ^ (-(3 / 2 : ℝ)) := by
          exact Finset.sum_le_sum fun b _ => cast_sqrt_div_cube_le x b
    _ = Real.sqrt x * ∑ b ∈ (Finset.Icc 1 x).filter Squarefree,
        (b : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt x * powerfulPSeriesConstant := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact Summable.sum_le_tsum _
        (fun b _ => Real.rpow_nonneg (Nat.cast_nonneg b) _)
        summable_powerfulPSeries

/-- The one-term very-bad count is `O(√x)`. -/
theorem veryBadOneTermCount_isBigO_sqrt :
    ((fun n : ℕ => (veryBadOneTermCount n : ℝ)) =O[atTop]
      fun n : ℕ => Real.sqrt n) := by
  refine IsBigO.of_bound powerfulPSeriesConstant ?_
  filter_upwards [] with n
  rw [Real.norm_of_nonneg
      (Nat.cast_nonneg (veryBadOneTermCount n) :
        0 ≤ (veryBadOneTermCount n : ℝ)),
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact veryBadOneTermCount_le_sqrt_mul_pSeries n |>.trans_eq (mul_comm _ _)

private theorem sqrt_isBigO_rpow_add (ε : ℝ) (hε : 0 < ε) :
    ((fun n : ℕ => Real.sqrt n) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) + ε)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [one_mul,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/-- The convergent `b⁻³ᐟ²` majorant supplies the full epsilon-power upper
bound for the one-term very-bad count. -/
theorem veryBadOneTermCount_powerUpperBound :
    PowerUpperBound (fun n : ℕ => (veryBadOneTermCount n : ℝ)) (1 / 2 : ℝ) := by
  intro ε hε
  exact veryBadOneTermCount_isBigO_sqrt.trans (sqrt_isBigO_rpow_add ε hε)

/-- The exact `VB¹` count has square-root power scale. This is weaker than
the source's precise `ζ(3/2)/ζ(3)` asymptotic, which remains to be proved. -/
theorem veryBadOneTermCount_powerScale :
    PowerScale (fun n : ℕ => (veryBadOneTermCount n : ℝ)) (1 / 2 : ℝ) := by
  intro ε hε
  exact ⟨veryBadOneTermCount_powerUpperBound ε hε,
    veryBadOneTermCount_powerScale_lower ε hε⟩

end Tao2026
