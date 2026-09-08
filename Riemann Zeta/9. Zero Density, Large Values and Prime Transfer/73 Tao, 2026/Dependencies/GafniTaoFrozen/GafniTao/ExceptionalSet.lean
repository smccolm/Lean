import GafniTao.Asymptotics
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The Gafni--Tao exceptional set

The public set in this module is a Lebesgue-measurable subset of the real
interval `[X,2X]`; it is not a sampled finite proxy.
-/

open Filter MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt BigOperators ENNReal

namespace GafniTao

/-- The literal half-open Mangoldt sum over natural numbers `x < n ≤ x+y` in
the positive range, represented by the corresponding floor interval. -/
noncomputable def mangoldtIntervalSum (x y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, Λ n

/-- On nonnegative source intervals, membership in the floor interval is
exactly the paper's half-open real-endpoint convention `x < n ≤ x+y`. -/
theorem mem_mangoldtInterval {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (n : ℕ) :
    n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊ ↔
      x < (n : ℝ) ∧ (n : ℝ) ≤ x + y := by
  rw [Finset.mem_Ioc, Nat.floor_lt hx,
    Nat.le_floor_iff (add_nonneg hx hy)]

/-- Splitting the Chebyshev sum at a real endpoint gives the exact interval
sum. -/
theorem mangoldtIntervalSum_eq_psi_sub (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    mangoldtIntervalSum x y = Chebyshev.psi (x + y) - Chebyshev.psi x := by
  have hxy : x ≤ x + y := by linarith
  have hfloor : ⌊x⌋₊ ≤ ⌊x + y⌋₊ := Nat.floor_mono hxy
  have hdisjoint :
      Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hunion :
      Finset.Ioc 0 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊ =
        Finset.Ioc 0 ⌊x + y⌋₊ :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hfloor
  have hsum := Finset.sum_union hdisjoint (f := fun n : ℕ => Λ n)
  rw [hunion] at hsum
  rw [mangoldtIntervalSum, Chebyshev.psi, Chebyshev.psi]
  linarith

/-- The exact short-interval Mangoldt sum in Definition 1.1. -/
noncomputable def mangoldtShortSum (x theta : ℝ) : ℝ :=
  mangoldtIntervalSum x (x ^ theta)

theorem mangoldtShortSum_eq_psi_sub {x theta : ℝ} (hx : 0 ≤ x) :
    mangoldtShortSum x theta =
      Chebyshev.psi (x + x ^ theta) - Chebyshev.psi x := by
  exact mangoldtIntervalSum_eq_psi_sub x (Real.rpow_nonneg hx theta)

/-- `psi` is Borel measurable as a function of its real endpoint. -/
theorem measurable_chebyshevPsi : Measurable Chebyshev.psi := by
  unfold Chebyshev.psi
  exact (measurable_of_countable
    (fun N : ℕ => ∑ n ∈ Finset.Ioc 0 N, Λ n)).comp measurable_id.nat_floor

theorem measurable_mangoldtShortSum {theta : ℝ} (htheta : 0 ≤ theta) :
    Measurable (fun x => mangoldtShortSum x theta) := by
  have hpow : Measurable (fun x : ℝ => x ^ theta) :=
    (Real.continuous_rpow_const htheta).measurable
  let intervalSum : ℕ × ℕ → ℝ := fun p =>
    ∑ n ∈ Finset.Ioc p.1 p.2, Λ n
  have hIntervalSum : Measurable intervalSum := measurable_of_countable intervalSum
  exact hIntervalSum.comp
    (measurable_id.nat_floor.prodMk (measurable_id.add hpow).nat_floor)

/-- The short-interval discrepancy from Definition 1.1. -/
noncomputable def shortIntervalDiscrepancy (x theta : ℝ) : ℝ :=
  mangoldtShortSum x theta - x ^ theta

/-- The exact Lebesgue exceptional set `E_delta(X,theta)`. -/
noncomputable def shortIntervalExceptionalSet
    (delta X theta : ℝ) : Set ℝ :=
  {x | x ∈ Icc X (2 * X) ∧
    delta * x ^ theta ≤ |shortIntervalDiscrepancy x theta|}

theorem measurable_shortIntervalDiscrepancy {theta : ℝ}
    (htheta : 0 ≤ theta) :
    Measurable (fun x => shortIntervalDiscrepancy x theta) := by
  exact (measurable_mangoldtShortSum htheta).sub
    (Real.continuous_rpow_const htheta).measurable

theorem measurableSet_shortIntervalExceptionalSet
    (delta X : ℝ) {theta : ℝ} (htheta : 0 ≤ theta) :
    MeasurableSet (shortIntervalExceptionalSet delta X theta) := by
  have hpow : Measurable (fun x : ℝ => x ^ theta) :=
    (Real.continuous_rpow_const htheta).measurable
  have hleft : Measurable (fun x : ℝ => delta * x ^ theta) :=
    measurable_const.mul hpow
  have hright : Measurable (fun x : ℝ => |shortIntervalDiscrepancy x theta|) :=
    (measurable_shortIntervalDiscrepancy htheta).abs
  exact measurableSet_Icc.inter (measurableSet_le hleft hright)

theorem shortIntervalExceptionalSet_subset_Icc (delta X theta : ℝ) :
    shortIntervalExceptionalSet delta X theta ⊆ Icc X (2 * X) := by
  intro x hx
  exact hx.1

/-- Increasing the discrepancy threshold shrinks the actual exceptional set.
The nonnegative lower endpoint is the source regime used as `X → ∞`. -/
theorem shortIntervalExceptionalSet_anti_delta
    {delta₁ delta₂ X theta : ℝ} (hX : 0 ≤ X) (hdelta : delta₁ ≤ delta₂) :
    shortIntervalExceptionalSet delta₂ X theta ⊆
      shortIntervalExceptionalSet delta₁ X theta := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hxnonneg : 0 ≤ x := hX.trans hx.1.1
  have hxpow : 0 ≤ x ^ theta := Real.rpow_nonneg hxnonneg theta
  exact (mul_le_mul_of_nonneg_right hdelta hxpow).trans hx.2

theorem measure_shortIntervalExceptionalSet_lt_top
    (delta X theta : ℝ) :
    volume (shortIntervalExceptionalSet delta X theta) < ∞ := by
  calc
    volume (shortIntervalExceptionalSet delta X theta) ≤ volume (Icc X (2 * X)) :=
      measure_mono (shortIntervalExceptionalSet_subset_Icc delta X theta)
    _ = ENNReal.ofReal (2 * X - X) := Real.volume_Icc
    _ < ∞ := ENNReal.ofReal_lt_top

/-- The real-valued Lebesgue measure used in fixed-power estimates. -/
noncomputable def exceptionalMeasure (delta X theta : ℝ) : ℝ :=
  (volume (shortIntervalExceptionalSet delta X theta)).toReal

/-- The paper's `mu_delta(theta)`, with no epsilon loss in its definition. -/
noncomputable def exceptionalExponentDelta (delta theta : ℝ) : EReal :=
  leastFixedPowerExponent (fun X => exceptionalMeasure delta X theta)

/-- The paper's `mu(theta)`, the supremum over every positive `delta`. -/
noncomputable def exceptionalExponent (theta : ℝ) : EReal :=
  sSup {a | ∃ delta : ℝ, 0 < delta ∧ a = exceptionalExponentDelta delta theta}

/-- The countable family of thresholds used in the paper's diagonalization. -/
noncomputable def countableExceptionalExponent (theta : ℝ) : EReal :=
  ⨆ n : ℕ, exceptionalExponentDelta (1 / (n + 1 : ℝ)) theta

/-- Fixed-power bounds are antitone in the positive discrepancy threshold. -/
theorem fixedPowerBound_exceptionalMeasure_anti_delta
    {delta₁ delta₂ theta xi : ℝ} (hdelta : delta₁ ≤ delta₂)
    (h : FixedPowerBound (fun X => exceptionalMeasure delta₁ X theta) xi) :
    FixedPowerBound (fun X => exceptionalMeasure delta₂ X theta) xi := by
  rcases h with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with X hboundX hX
  have hmeasure :
      volume (shortIntervalExceptionalSet delta₂ X theta) ≤
        volume (shortIntervalExceptionalSet delta₁ X theta) :=
    measure_mono (shortIntervalExceptionalSet_anti_delta hX hdelta)
  have hmeasureReal :
      exceptionalMeasure delta₂ X theta ≤
        exceptionalMeasure delta₁ X theta := by
    exact ENNReal.toReal_mono
      (measure_shortIntervalExceptionalSet_lt_top delta₁ X theta).ne hmeasure
  calc
    |exceptionalMeasure delta₂ X theta| = exceptionalMeasure delta₂ X theta :=
      abs_of_nonneg ENNReal.toReal_nonneg
    _ ≤ exceptionalMeasure delta₁ X theta := hmeasureReal
    _ ≤ |exceptionalMeasure delta₁ X theta| := le_abs_self _
    _ ≤ C * X ^ xi := hboundX

/-- The least exceptional exponent is antitone in the positive discrepancy
threshold, with the direction forced by inclusion of the literal sets. -/
theorem exceptionalExponentDelta_anti {delta₁ delta₂ theta : ℝ}
    (hdelta : delta₁ ≤ delta₂) :
    exceptionalExponentDelta delta₂ theta ≤
      exceptionalExponentDelta delta₁ theta := by
  unfold exceptionalExponentDelta leastFixedPowerExponent fixedPowerExponentSet
  apply sInf_le_sInf
  rintro x ⟨xi, hxi, rfl⟩
  exact ⟨xi, fixedPowerBound_exceptionalMeasure_anti_delta hdelta hxi, rfl⟩

theorem exceptionalExponentDelta_le {delta theta xi : ℝ}
    (h : FixedPowerBound (fun X => exceptionalMeasure delta X theta) xi) :
    exceptionalExponentDelta delta theta ≤ (xi : EReal) := by
  exact leastFixedPowerExponent_le h

theorem exceptionalExponentDelta_eq_bot_of_eventually_empty
    {delta theta : ℝ}
    (h : ∀ᶠ X in atTop, shortIntervalExceptionalSet delta X theta = ∅) :
    exceptionalExponentDelta delta theta = ⊥ := by
  apply leastFixedPowerExponent_eq_bot_of_eventually_zero
  filter_upwards [h] with X hX
  simp [exceptionalMeasure, hX]

theorem exceptionalExponentDelta_le_exceptionalExponent
    {delta theta : ℝ} (hdelta : 0 < delta) :
    exceptionalExponentDelta delta theta ≤ exceptionalExponent theta := by
  apply le_sSup
  exact ⟨delta, hdelta, rfl⟩

theorem exceptionalExponent_le {theta : ℝ} {a : EReal}
    (h : ∀ delta : ℝ, 0 < delta → exceptionalExponentDelta delta theta ≤ a) :
    exceptionalExponent theta ≤ a := by
  apply sSup_le
  rintro x ⟨delta, hdelta, rfl⟩
  exact h delta hdelta

theorem exceptionalExponent_le_coe_iff {theta xi : ℝ} :
    exceptionalExponent theta ≤ (xi : EReal) ↔
      ∀ delta : ℝ, 0 < delta →
        exceptionalExponentDelta delta theta ≤ (xi : EReal) := by
  constructor
  · intro h delta hdelta
    exact (exceptionalExponentDelta_le_exceptionalExponent hdelta).trans h
  · exact exceptionalExponent_le

/-- The uncountable positive-threshold supremum is exactly the paper's
countable diagonal family `delta = 1, 1/2, 1/3, ...`. -/
theorem exceptionalExponent_eq_countable (theta : ℝ) :
    exceptionalExponent theta = countableExceptionalExponent theta := by
  apply le_antisymm
  · apply exceptionalExponent_le
    intro delta hdelta
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdelta
    exact (exceptionalExponentDelta_anti hn.le).trans
      (le_iSup (fun k : ℕ =>
        exceptionalExponentDelta (1 / (k + 1 : ℝ)) theta) n)
  · apply iSup_le
    intro n
    apply exceptionalExponentDelta_le_exceptionalExponent
    positivity

end GafniTao
