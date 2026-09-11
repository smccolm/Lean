import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Real

/-!
# Source-facing asymptotic predicates

Tao's statements use several logically different forms of `o(1)`. This file
gives them separate quantified interfaces over natural cutoffs. Values at
finitely many small cutoffs are intentionally irrelevant.
-/

open Filter Asymptotics

namespace Tao2026

/-- `f(n) ≪ n^(a+o(1))`: every positive epsilon permits its own eventual
big-O constant. -/
def PowerUpperBound (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    f =O[atTop] fun n : ℕ => (n : ℝ) ^ (a + ε)

/-- Products add power exponents.  The epsilon loss is split evenly between
the two factors. -/
theorem PowerUpperBound.mul {f g : ℕ → ℝ} {a b : ℝ}
    (hf : PowerUpperBound f a) (hg : PowerUpperBound g b) :
    PowerUpperBound (fun n => f n * g n) (a + b) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hproduct := (hf (ε / 2) hhalf).mul (hg (ε / 2) hhalf)
  have hpowers :
      (fun n : ℕ =>
        (n : ℝ) ^ (a + ε / 2) * (n : ℝ) ^ (b + ε / 2)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ ((a + b) + ε)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have heq :
        (n : ℝ) ^ (a + ε / 2) * (n : ℝ) ^ (b + ε / 2) =
          (n : ℝ) ^ ((a + b) + ε) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    rw [Real.norm_of_nonneg
        (mul_nonneg (Real.rpow_nonneg hnpos.le _)
          (Real.rpow_nonneg hnpos.le _)),
      Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _), one_mul, heq]
  exact hproduct.trans hpowers

/-- Sums of two functions with the same power exponent retain that exponent. -/
theorem PowerUpperBound.add {f g : ℕ → ℝ} {a : ℝ}
    (hf : PowerUpperBound f a) (hg : PowerUpperBound g a) :
    PowerUpperBound (fun n => f n + g n) a := by
  intro ε hε
  obtain ⟨C, hC⟩ := (hf ε hε).bound
  obtain ⟨D, hD⟩ := (hg ε hε).bound
  refine IsBigO.of_bound (C + D) ?_
  filter_upwards [hC, hD] with n hfn hgn
  calc
    ‖f n + g n‖ ≤ ‖f n‖ + ‖g n‖ := norm_add_le _ _
    _ ≤ C * ‖(n : ℝ) ^ (a + ε)‖ +
        D * ‖(n : ℝ) ^ (a + ε)‖ := add_le_add hfn hgn
    _ = (C + D) * ‖(n : ℝ) ^ (a + ε)‖ := by ring

/-- Enlarging the main power exponent preserves a power upper bound. -/
theorem PowerUpperBound.mono_exponent {f : ℕ → ℝ} {a b : ℝ}
    (hf : PowerUpperBound f a) (hab : a ≤ b) :
    PowerUpperBound f b := by
  intro ε hε
  have hpowers : (fun n : ℕ => (n : ℝ) ^ (a + ε)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (b + ε)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
  exact (hf ε hε).trans hpowers

/-- A natural-valued subpolynomial function is eventually below the simple
linear cutoff `2n`.  This normalization is useful when applying uniform
finite counting estimates. -/
theorem eventually_nat_le_two_mul_self_of_powerUpperBound_zero
    (g : ℕ → ℕ) (hg : PowerUpperBound (fun n => (g n : ℝ)) 0) :
    ∀ᶠ n : ℕ in atTop, g n ≤ 2 * n := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨C, hC⟩ := (hg (1 / 2) hhalf).bound
  have hrootTop : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop
  have hCroot : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
    hrootTop.eventually (eventually_ge_atTop C)
  filter_upwards [hC, hCroot, eventually_ge_atTop (1 : ℕ)] with n hn hCn hnOne
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnOne
  have hrootNonneg : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg hnpos.le _
  have hsquare :
      (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = n := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hreal : (g n : ℝ) ≤ 2 * n := by
    calc
      (g n : ℝ) = ‖(g n : ℝ)‖ := by
        rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      _ ≤ C * ‖(n : ℝ) ^ ((0 : ℝ) + 1 / 2)‖ := hn
      _ = C * (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [zero_add, Real.norm_of_nonneg hrootNonneg]
      _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hCn hrootNonneg
      _ = n := hsquare
      _ ≤ 2 * n := by linarith
  exact_mod_cast hreal

/-- `f(n) = n^(a+o(1))`, expressed as matching epsilon-power upper and lower
bounds. The reverse big-O is meaningful for the nonnegative counting
functions used by the project. -/
def PowerScale (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (f =O[atTop] fun n : ℕ => (n : ℝ) ^ (a + ε)) ∧
    ((fun n : ℕ => (n : ℝ) ^ (a - ε)) =O[atTop] f)

/-- `f ≪ g / log(n)^(1-o(1))`. Each epsilon has its own eventual big-O
constant, while `f` and `g` themselves remain fixed. -/
def LogPowerSavingRelative (f g : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    f =O[atTop] fun n : ℕ => g n / (Real.log n) ^ (1 - ε)

/-- `f = numerator / scale^(a+o(1))`. This direct eventual sandwich avoids
silently reversing the epsilon losses in a denominator. -/
def QuotientPowerScale
    (f numerator scale : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      numerator n / (scale n) ^ (a + ε) ≤ f n ∧
      f n ≤ numerator n / (scale n) ^ (a - ε)

/-- Ordinary asymptotic equivalence of real-valued sequences. -/
def SequenceEquivalent (f g : ℕ → ℝ) : Prop := f ~[atTop] g

end Tao2026
