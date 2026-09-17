import Tao2026.FourierDecay

open Complex Finset Filter
open scoped BigOperators Topology

namespace Tao2026

noncomputable section

def fourierDecayWeightFiveHalves (q : ℤ × ℤ) : ℝ :=
  (1 + |(q.1 : ℝ)| + |(q.2 : ℝ)|) ^ (-(5 / 2 : ℝ))

def intFourierDecayWeightFiveFourths (n : ℤ) : ℝ :=
  (1 + |(n : ℝ)|) ^ (-(5 / 4 : ℝ))

theorem intFourierDecayWeightFiveFourths_nonneg (n : ℤ) :
    0 ≤ intFourierDecayWeightFiveFourths n := by
  exact Real.rpow_nonneg (by positivity) _

theorem summable_intFourierDecayWeightFiveFourths :
    Summable intFourierDecayWeightFiveFourths := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · have h := (Real.summable_one_div_nat_add_rpow 1 (5 / 4 : ℝ)).2 (by norm_num)
    convert h using 1
    funext n
    rw [intFourierDecayWeightFiveFourths, Int.cast_natCast,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)),
      Real.rpow_neg, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
    ring_nf
    all_goals positivity
  · have h := (Real.summable_one_div_nat_add_rpow 1 (5 / 4 : ℝ)).2 (by norm_num)
    convert h using 1
    funext n
    rw [intFourierDecayWeightFiveFourths, Int.cast_neg, abs_neg, Int.cast_natCast,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)), Real.rpow_neg,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
    ring_nf
    all_goals positivity

theorem fourierDecayWeightFiveHalves_le_mul (q : ℤ × ℤ) :
    fourierDecayWeightFiveHalves q ≤
      intFourierDecayWeightFiveFourths q.1 *
        intFourierDecayWeightFiveFourths q.2 := by
  let x : ℝ := 1 + |(q.1 : ℝ)|
  let y : ℝ := 1 + |(q.2 : ℝ)|
  let z : ℝ := 1 + |(q.1 : ℝ)| + |(q.2 : ℝ)|
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hxy : x * y ≤ z ^ 2 := by
    dsimp [x, y, z]
    nlinarith [abs_nonneg (q.1 : ℝ), abs_nonneg (q.2 : ℝ),
      mul_nonneg (abs_nonneg (q.1 : ℝ)) (abs_nonneg (q.2 : ℝ))]
  have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hx hy) hxy
    (by norm_num : -(5 / 4 : ℝ) ≤ 0)
  change z ^ (-(5 / 2 : ℝ)) ≤
    x ^ (-(5 / 4 : ℝ)) * y ^ (-(5 / 4 : ℝ))
  rw [← Real.mul_rpow hx.le hy.le]
  calc
    z ^ (-(5 / 2 : ℝ)) = (z ^ 2) ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
      norm_num
    _ ≤ (x * y) ^ (-(5 / 4 : ℝ)) := hpow

theorem fourierDecayWeightFiveHalves_nonneg (q : ℤ × ℤ) :
    0 ≤ fourierDecayWeightFiveHalves q := by
  exact Real.rpow_nonneg (by positivity) _

theorem summable_fourierDecayWeightFiveHalves :
    Summable fourierDecayWeightFiveHalves := by
  have hproduct : Summable
      (fun q : ℤ × ℤ => intFourierDecayWeightFiveFourths q.1 *
        intFourierDecayWeightFiveFourths q.2) :=
    summable_intFourierDecayWeightFiveFourths.mul_of_nonneg
      summable_intFourierDecayWeightFiveFourths
      intFourierDecayWeightFiveFourths_nonneg
      intFourierDecayWeightFiveFourths_nonneg
  exact hproduct.of_nonneg_of_le fourierDecayWeightFiveHalves_nonneg
    fourierDecayWeightFiveHalves_le_mul

theorem fourierDecayWeight_le_radiusFactor_mul_fiveHalves
    (R : ℕ) (q : ℤ × ℤ) (hq : q ∉ fourierFrequencyBox R) :
    fourierDecayWeight q ≤
      ((R : ℝ) + 1) ^ (-(1 / 2 : ℝ)) *
        fourierDecayWeightFiveHalves q := by
  rw [mem_fourierFrequencyBox, not_and_or] at hq
  let z : ℝ := 1 + |(q.1 : ℝ)| + |(q.2 : ℝ)|
  have hz : 0 < z := by dsimp [z]; positivity
  have hR : 0 < (R : ℝ) + 1 := by positivity
  have hRz : (R : ℝ) + 1 ≤ z := by
    rcases hq with hq | hq
    · have hq' : (R : ℤ) < |q.1| := lt_of_not_ge hq
      have hq'' : (R : ℤ) + 1 ≤ |q.1| := by omega
      have hqreal : (R : ℝ) + 1 ≤ |(q.1 : ℝ)| := by
        calc
          (R : ℝ) + 1 = (((R : ℤ) + 1 : ℤ) : ℝ) := by norm_num
          _ ≤ ((|q.1| : ℤ) : ℝ) := by exact_mod_cast hq''
          _ = |(q.1 : ℝ)| := by norm_cast
      dsimp only [z]
      linarith [abs_nonneg (q.2 : ℝ)]
    · have hq' : (R : ℤ) < |q.2| := lt_of_not_ge hq
      have hq'' : (R : ℤ) + 1 ≤ |q.2| := by omega
      have hqreal : (R : ℝ) + 1 ≤ |(q.2 : ℝ)| := by
        calc
          (R : ℝ) + 1 = (((R : ℤ) + 1 : ℤ) : ℝ) := by norm_num
          _ ≤ ((|q.2| : ℤ) : ℝ) := by exact_mod_cast hq''
          _ = |(q.2 : ℝ)| := by norm_cast
      dsimp only [z]
      linarith [abs_nonneg (q.1 : ℝ)]
  have hhalf : z ^ (-(1 / 2 : ℝ)) ≤
      ((R : ℝ) + 1) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hR hRz (by norm_num)
  change z ^ (-(3 : ℝ)) ≤
    ((R : ℝ) + 1) ^ (-(1 / 2 : ℝ)) * z ^ (-(5 / 2 : ℝ))
  rw [show -(3 : ℝ) = -(1 / 2 : ℝ) + -(5 / 2 : ℝ) by norm_num,
    Real.rpow_add hz]
  exact mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hz.le _)

theorem fourierDecayTail_le_invSqrt (R : ℕ) :
    (∑' q : {q // q ∉ fourierFrequencyBox R}, fourierDecayWeight q) ≤
      ((R : ℝ) + 1) ^ (-(1 / 2 : ℝ)) *
        ∑' q : ℤ × ℤ, fourierDecayWeightFiveHalves q := by
  calc
    (∑' q : {q // q ∉ fourierFrequencyBox R}, fourierDecayWeight q) ≤
        ∑' q : {q // q ∉ fourierFrequencyBox R},
          ((R : ℝ) + 1) ^ (-(1 / 2 : ℝ)) *
            fourierDecayWeightFiveHalves q := by
      exact (summable_fourierDecayWeight.subtype _).tsum_le_tsum
        (fun q => fourierDecayWeight_le_radiusFactor_mul_fiveHalves R q q.property)
        ((summable_fourierDecayWeightFiveHalves.subtype _).mul_left _)
    _ = ((R : ℝ) + 1) ^ (-(1 / 2 : ℝ)) *
        ∑' q : {q // q ∉ fourierFrequencyBox R},
          fourierDecayWeightFiveHalves q := by
      rw [← tsum_mul_left]
    _ ≤ ((R : ℝ) + 1) ^ (-(1 / 2 : ℝ)) *
        ∑' q : ℤ × ℤ, fourierDecayWeightFiveHalves q := by
      gcongr
      exact Summable.tsum_subtype_le fourierDecayWeightFiveHalves _
        fourierDecayWeightFiveHalves_nonneg
        summable_fourierDecayWeightFiveHalves

end

end Tao2026
