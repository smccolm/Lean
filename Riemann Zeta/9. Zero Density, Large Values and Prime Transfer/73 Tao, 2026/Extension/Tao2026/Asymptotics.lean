import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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
