import PrimeShell.TwoBandAmplitude
import Zeta23.PrimeSideB.PP
import Zeta23.XiPrime.PrimeSide.Concrete

namespace PrimeShell

noncomputable section

open scoped BigOperators
open Zeta23 Zeta23.PrimeSide

/-- The low component of the literal two-band source difference set,
evaluated at the logarithmic frequency attached to `n`. -/
def InTwoBandLowSource (P : Params) (T : ℝ) (n : ℕ) : Prop :=
  |Real.log n / P.L T| < 2 * shellBandOuterRadius

/-- The positive high component of the literal two-band source difference
set, evaluated at the logarithmic frequency attached to `n`.  The negative
component cannot occur because `log n ≥ 0` on `primeRange`. -/
def InTwoBandHighSource (P : Params) (T : ℝ) (n : ℕ) : Prop :=
  |Real.log n / P.L T - 2 * shellBandCenter| <
    2 * shellBandOuterRadius

instance (P : Params) (T : ℝ) (n : ℕ) :
    Decidable (InTwoBandLowSource P T n) := Classical.propDecidable _

instance (P : Params) (T : ℝ) (n : ℕ) :
    Decidable (InTwoBandHighSource P T n) := Classical.propDecidable _

/-- The exact low-shell part of the source diagonal sum. -/
def twoBandLowA2g (P : Params) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X,
    if InTwoBandLowSource P T n then
      (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 / n *
        (P.atV (amplitudeSq twoBandAmplitude) T).g T (Real.log n)
    else 0

/-- The exact positive-high-shell part of the source diagonal sum. -/
def twoBandHighA2g (P : Params) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X,
    if InTwoBandHighSource P T n then
      (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 / n *
        (P.atV (amplitudeSq twoBandAmplitude) T).g T (Real.log n)
    else 0

/-- The low-shell part of the actual generalized-coefficient diagonal sum
used by the `xi'` prime-side matrix. -/
def twoBandLowW2g
    (c : ℕ → ℂ) (P : Params) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X,
    if InTwoBandLowSource P T n then
      ‖c n‖ ^ 2 / n *
        (P.atV (amplitudeSq twoBandAmplitude) T).g T (Real.log n)
    else 0

/-- The positive-high-shell part of the actual generalized-coefficient
diagonal sum used by the `xi'` prime-side matrix. -/
def twoBandHighW2g
    (c : ℕ → ℂ) (P : Params) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X,
    if InTwoBandHighSource P T n then
      ‖c n‖ ^ 2 / n *
        (P.atV (amplitudeSq twoBandAmplitude) T).g T (Real.log n)
    else 0

theorem not_mem_negative_twoBandShell_of_nonneg
    {z : ℝ} (hz : 0 ≤ z) :
    ¬ |z + 2 * shellBandCenter| < 2 * shellBandOuterRadius := by
  rw [abs_of_nonneg]
  · norm_num [shellBandCenter, shellBandOuterRadius]
    linarith
  · norm_num [shellBandCenter]
    linarith

theorem twoBandLowSource_disjoint_highSource
    {P : Params} {T : ℝ} {n : ℕ}
    (hL : 0 < P.L T)
    (hn : n ∈ primeRange (P.X T))
    (hlow : InTwoBandLowSource P T n) :
    ¬ InTwoBandHighSource P T n := by
  have hnlog : 0 ≤ Real.log n := log_nonneg_of_mem_primeRange hn
  have hz : 0 ≤ Real.log n / P.L T := div_nonneg hnlog hL.le
  unfold InTwoBandLowSource at hlow
  unfold InTwoBandHighSource
  intro hhigh
  rw [abs_lt] at hlow hhigh
  norm_num [shellBandCenter, shellBandOuterRadius] at hlow hhigh
  linarith

/-- On the nonnegative logarithmic axis, the three-piece difference set of
the symmetric two-band amplitude reduces exactly to its low piece and its
positive high piece. -/
theorem inTwoBandDifferenceSet_iff_low_or_high_of_nonneg
    {P : Params} {T : ℝ} {n : ℕ}
    (hL : 0 < P.L T)
    (hn : n ∈ primeRange (P.X T)) :
    InTwoBandDifferenceSet (Real.log n / P.L T) ↔
      InTwoBandLowSource P T n ∨ InTwoBandHighSource P T n := by
  have hnlog : 0 ≤ Real.log n := log_nonneg_of_mem_primeRange hn
  have hz : 0 ≤ Real.log n / P.L T := div_nonneg hnlog hL.le
  unfold InTwoBandDifferenceSet InTwoBandLowSource InTwoBandHighSource
  constructor
  · intro h
    rcases h with hlow | hhigh | hnegative
    · exact Or.inl hlow
    · exact Or.inr hhigh
    · exact (not_mem_negative_twoBandShell_of_nonneg hz hnegative).elim
  · intro h
    rcases h with hlow | hhigh
    · exact Or.inl hlow
    · exact Or.inr (Or.inl hhigh)

/-- The actual Zeta23 diagonal source sum for the two-band family is
exactly the sum of its low and positive-high shell contributions.  This is
an equality of the real source object, not a support heuristic. -/
theorem sumA2g_atTwoBand_eq_low_add_high
    {P : Params} {T : ℝ}
    (hw : P.w ≠ 0) (hL : 0 < P.L T) :
    sumA2g (P.X T) ((P.atV (amplitudeSq twoBandAmplitude) T).g T) =
      twoBandLowA2g P T (P.X T) + twoBandHighA2g P T (P.X T) := by
  unfold sumA2g twoBandLowA2g twoBandHighA2g
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hlow : InTwoBandLowSource P T n
  · have hnotHigh := twoBandLowSource_disjoint_highSource hL hn hlow
    simp [hlow, hnotHigh]
  · by_cases hhigh : InTwoBandHighSource P T n
    · simp [hlow, hhigh]
    · have hnotDiff :
          ¬ InTwoBandDifferenceSet (Real.log n / P.L T) := by
        rw [inTwoBandDifferenceSet_iff_low_or_high_of_nonneg hL hn]
        simp [hlow, hhigh]
      have hg :
          (P.atV (amplitudeSq twoBandAmplitude) T).g T (Real.log n) = 0 :=
        atTwoBand_g_eq_zero_of_not_mem_differenceSet hw hL.ne' hnotDiff
      simp [hlow, hhigh, hg]

/-- Exact low/high shell decomposition for the full coefficient sequence
appearing in the `xi'` explicit formula.  In particular this theorem does
not replace `xiCoeff` by the von Mangoldt function. -/
theorem sumW2g_atTwoBand_eq_low_add_high
    {P : Params} {T : ℝ} (c : ℕ → ℂ)
    (hw : P.w ≠ 0) (hL : 0 < P.L T) :
    Zeta23.XiPrime.sumW2g c (P.X T)
        ((P.atV (amplitudeSq twoBandAmplitude) T).g T) =
      twoBandLowW2g c P T (P.X T) +
        twoBandHighW2g c P T (P.X T) := by
  unfold Zeta23.XiPrime.sumW2g twoBandLowW2g twoBandHighW2g
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hlow : InTwoBandLowSource P T n
  · have hnotHigh := twoBandLowSource_disjoint_highSource hL hn hlow
    simp [hlow, hnotHigh]
  · by_cases hhigh : InTwoBandHighSource P T n
    · simp [hlow, hhigh]
    · have hnotDiff :
          ¬ InTwoBandDifferenceSet (Real.log n / P.L T) := by
        rw [inTwoBandDifferenceSet_iff_low_or_high_of_nonneg hL hn]
        simp [hlow, hhigh]
      have hg :
          (P.atV (amplitudeSq twoBandAmplitude) T).g T (Real.log n) = 0 :=
        atTwoBand_g_eq_zero_of_not_mem_differenceSet hw hL.ne' hnotDiff
      simp [hlow, hhigh, hg]

end

end PrimeShell
