import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Counterexample data for the printed hypotheses of Theorem 8 Part I

The digamma series is reused directly from the pinned PNT+ dependency, as in
node 77. No author numerical program is involved in these inequalities.
-/

namespace DhimanKadiriQuesadaHerrera2026.PoissonCounterexample

open scoped BigOperators
open Filter MeasureTheory

/-- A positive polynomial weight with zero derivative at the left endpoint. -/
noncomputable def weight (x : ℝ) : ℝ := 101 / 100 - (x - 1 / 2) ^ 3

/-- A phase with positive strictly decreasing derivative on the source interval. -/
noncomputable def phase (x : ℝ) : ℝ :=
  (1 / 10000) * ((x - 1 / 2) - (x - 1 / 2) ^ 2 / 4)

/-- The exact (3.2) coefficient for this example, with its empty finite boundary sum. -/
noncomputable def printedBound : ℝ :=
  (101 / 100) / Real.pi *
    (Real.log (1 + 1 / 10000) + Real.eulerMascheroniConstant -
      (Complex.digamma (9999 / 10000)).re - 1 / 2 - 1 / (2 * (1 + 1 / 10000)))

/-- Rational comparison of each digamma-series term with a telescoping majorant. -/
theorem digamma_term_le (n : ℕ) :
    1 / ((n : ℝ) + 9999 / 10000) - 1 / ((n : ℝ) + 1) ≤
      (2 / 9999) * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : 0 < (n : ℝ) + 1 := by positivity
  have h2 : 0 < (n : ℝ) + 2 := by positivity
  have hq : 0 < (n : ℝ) + 9999 / 10000 := by positivity
  field_simp
  nlinarith

/-- An exact real digamma bound from the pinned convergent series. -/
theorem neg_re_digamma_le :
    -(Complex.digamma (9999 / 10000)).re ≤ Real.eulerMascheroniConstant + 2 / 9999 := by
  have hpoles : ∀ n : ℕ, (9999 / 10000 : ℂ) ≠ -n := by
    intro n h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hs := (Complex.hasSum_re (Complex.hasSum_digamma hpoles)).neg
  have hs' : HasSum (fun n : ℕ =>
      1 / ((n : ℝ) + 9999 / 10000) - 1 / ((n : ℝ) + 1))
      (-(Complex.digamma (9999 / 10000)).re - Real.eulerMascheroniConstant) := by
    convert hs using 1
    · funext n
      have hcast : (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 9999 / 10000)) =
          ((1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 9999 / 10000) : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hcast, Complex.ofReal_re]
      ring
    · simp
      ring
  have hfinite (N : ℕ) :
      ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 9999 / 10000) - 1 / ((n : ℝ) + 1)) ≤
        (2 / 9999) * (1 - 1 / ((N : ℝ) + 1)) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hterm := digamma_term_le N
      push_cast
      rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
      linarith
  have hlim : -(Complex.digamma (9999 / 10000)).re - Real.eulerMascheroniConstant ≤
      2 / 9999 := by
    apply le_of_tendsto hs'.tendsto_sum_nat
    apply Eventually.of_forall
    intro N
    refine (hfinite N).trans ?_
    have hpos : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
    nlinarith
  linarith

/-- The printed upper bound is strictly less than three twenty-fifths. -/
theorem printedBound_lt : printedBound < 3 / 25 := by
  have hlog : Real.log (1 + 1 / 10000) < (1 / 10000 : ℝ) := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 10000)
      (by norm_num : (1 + 1 / 10000 : ℝ) ≠ 1)
    linarith
  have hgamma := Real.eulerMascheroniConstant_lt_two_thirds
  have hpsi := neg_re_digamma_le
  have hbracket : Real.log (1 + 1 / 10000) + Real.eulerMascheroniConstant -
      (Complex.digamma (9999 / 10000)).re - 1 / 2 - 1 / (2 * (1 + 1 / 10000)) <
      (17 / 50 : ℝ) := by linarith
  unfold printedBound
  have hfactor : (101 / 100 : ℝ) / Real.pi > 0 := by positivity
  calc
    _ < ((101 / 100 : ℝ) / Real.pi) * (17 / 50) :=
      mul_lt_mul_of_pos_left hbracket hfactor
    _ < ((101 / 100 : ℝ) / 3) * (17 / 50) := by
      apply mul_lt_mul_of_pos_right _ (by norm_num)
      exact div_lt_div_of_pos_left (by norm_num) (by norm_num) Real.pi_gt_three
    _ < 3 / 25 := by norm_num

/-- Exact derivative of the polynomial weight. -/
theorem hasDerivAt_weight (x : ℝ) :
    HasDerivAt weight (-3 * (x - 1 / 2) ^ 2) x := by
  convert (hasDerivAt_const x (101 / 100 : ℝ)).sub
    (((hasDerivAt_id x).sub_const (1 / 2)).pow 3) using 1
  simp

/-- Exact derivative of the phase. -/
theorem hasDerivAt_phase (x : ℝ) :
    HasDerivAt phase ((1 / 10000) * (1 - (x - 1 / 2) / 2)) x := by
  convert (((hasDerivAt_id x).sub_const (1 / 2)).sub
    ((((hasDerivAt_id x).sub_const (1 / 2)).pow 2).div_const 4)).const_mul
      (1 / 10000) using 1
  simp
  ring

/-- The weight satisfies strict positivity on the entire closed source interval. -/
theorem weight_bounds {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
    0 < weight x ∧ weight x ≤ 101 / 100 := by
  have h0 : 0 ≤ x - 1 / 2 := by linarith [hx.1]
  have h1 : x - 1 / 2 ≤ 1 := by linarith [hx.2]
  have hp0 : 0 ≤ (x - 1 / 2) ^ 3 := pow_nonneg h0 _
  have hp1 : (x - 1 / 2) ^ 3 ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) ^ 3 := pow_le_pow_left₀ h0 h1 _
      _ = 1 := by norm_num
  constructor <;> dsimp [weight] <;> linarith

/-- Uniform smallness and positivity of the real phase. -/
theorem phase_bounds {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
    0 ≤ phase x ∧ phase x ≤ 1 / 10000 := by
  have h0 : 0 ≤ x - 1 / 2 := by linarith [hx.1]
  have h1 : x - 1 / 2 ≤ 1 := by linarith [hx.2]
  have hp : (x - 1 / 2) ^ 2 ≤ x - 1 / 2 := by nlinarith
  constructor <;> dsimp [phase] <;> nlinarith [sq_nonneg (x - 1 / 2)]

/-- The printed positivity, smoothness and strict monotonicity hypotheses hold. -/
theorem printed_hypotheses :
    ContDiff ℝ 2 weight ∧ ContDiff ℝ 2 phase ∧
      StrictAntiOn weight (Set.Icc (1 / 2 : ℝ) (3 / 2)) ∧
      StrictAntiOn (deriv phase) (Set.Icc (1 / 2 : ℝ) (3 / 2)) ∧
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2), 0 < weight x ∧ 0 < deriv phase x) ∧
      deriv weight (1 / 2) = 0 ∧ deriv phase (1 / 2) = 1 / 10000 := by
  refine ⟨by unfold weight; fun_prop, by unfold phase; fun_prop, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _ y _ hxy
    have hpow := (Odd.strictMono_pow (by decide : Odd (3 : ℕ)))
      (sub_lt_sub_right hxy (1 / 2))
    dsimp [weight]
    linarith
  · intro x _ y _ hxy
    rw [(hasDerivAt_phase x).deriv, (hasDerivAt_phase y).deriv]
    linarith
  · intro x hx
    refine ⟨(weight_bounds hx).1, ?_⟩
    rw [(hasDerivAt_phase x).deriv]
    linarith [hx.2]
  · rw [(hasDerivAt_weight _).deriv]
    norm_num
  · rw [(hasDerivAt_phase _).deriv]
    norm_num

/-- The actual weighted exponential integrand. -/
noncomputable def oscillation (x : ℝ) : ℂ :=
  (weight x : ℂ) * Complex.exp (Complex.I * (2 * Real.pi * phase x : ℝ))

/-- The actual one-term finite sum minus its sole retained Fourier integral. -/
noncomputable def remainder : ℂ :=
  oscillation 1 - ∫ x in (1 / 2 : ℝ)..(3 / 2), oscillation x

/-- Exact zero-phase integral, used to keep the counterexample quantitative. -/
theorem integral_weight : (∫ x in (1 / 2 : ℝ)..(3 / 2), weight x) = 19 / 25 := by
  unfold weight
  have hpoly : IntervalIntegrable (fun x : ℝ => (x - 1 / 2) ^ 3)
      volume (1 / 2) (3 / 2) := (by fun_prop :
        Continuous (fun x : ℝ => (x - 1 / 2) ^ 3)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (intervalIntegrable_const) hpoly]
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ 3) (1 / 2), integral_pow]
  norm_num

/-- A rational uniform bound for the perturbation from the zero phase. -/
theorem norm_oscillation_sub_weight_le {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
    ‖oscillation x - (weight x : ℂ)‖ ≤ 101 / 125000 := by
  obtain ⟨hw0, hw1⟩ := weight_bounds hx
  obtain ⟨hf0, hf1⟩ := phase_bounds hx
  have he : ‖Complex.exp (Complex.I * (2 * Real.pi * phase x : ℝ)) - 1‖ ≤
      2 * Real.pi / 10000 := by
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [Real.pi_pos]
  have hid : oscillation x - (weight x : ℂ) =
      (weight x : ℂ) * (Complex.exp (Complex.I * (2 * Real.pi * phase x : ℝ)) - 1) := by
    unfold oscillation
    ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
  calc
    _ ≤ (101 / 100) * (2 * Real.pi / 10000) := mul_le_mul hw1 he (norm_nonneg _) (by norm_num)
    _ ≤ 101 / 125000 := by nlinarith [Real.pi_lt_four]

/-- The genuine complex remainder remains close to the nonzero polynomial discrepancy. -/
theorem norm_remainder_sub_eighth_le : ‖remainder - (1 / 8 : ℂ)‖ ≤ 101 / 62500 := by
  have ho : Continuous oscillation := by unfold oscillation phase weight; fun_prop
  have hw : Continuous (fun x : ℝ => (weight x : ℂ)) := by unfold weight; fun_prop
  have hi : (∫ x in (1 / 2 : ℝ)..(3 / 2), (weight x : ℂ)) = (19 / 25 : ℂ) := by
    rw [intervalIntegral.integral_ofReal, integral_weight]
    norm_num
  have herr : ‖∫ x in (1 / 2 : ℝ)..(3 / 2), (oscillation x - (weight x : ℂ))‖ ≤
      101 / 125000 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 / 2 : ℝ)) (b := (3 / 2 : ℝ)) (C := (101 / 125000 : ℝ))
      (f := fun x => oscillation x - (weight x : ℂ)) (by
        intro x hx
        apply norm_oscillation_sub_weight_le
        rw [Set.uIoc_of_le (by norm_num)] at hx
        exact ⟨hx.1.le, hx.2⟩)
    norm_num at h
    exact h
  have hid : remainder - (1 / 8 : ℂ) =
      (oscillation 1 - (weight 1 : ℂ)) -
        ∫ x in (1 / 2 : ℝ)..(3 / 2), (oscillation x - (weight x : ℂ)) := by
    rw [intervalIntegral.integral_sub (ho.intervalIntegrable _ _) (hw.intervalIntegrable _ _), hi]
    unfold remainder
    norm_num [weight]
    ring
  rw [hid]
  have hpoint := norm_oscillation_sub_weight_le (x := 1) (by constructor <;> norm_num)
  exact (norm_sub_le _ _).trans (by linarith)

/-- The actual oscillatory remainder is larger than the advertised upper bound. -/
theorem printed_partI_bound_fails : printedBound < ‖remainder‖ := by
  have htriangle := norm_sub_le remainder (remainder - (1 / 8 : ℂ))
  have hid : remainder - (remainder - (1 / 8 : ℂ)) = (1 / 8 : ℂ) := by ring
  rw [hid] at htriangle
  norm_num at htriangle
  have herror := norm_remainder_sub_eighth_le
  have hlower : (3 / 25 : ℝ) < ‖remainder‖ := by linarith
  exact printedBound_lt.trans hlower

/-- The actual integer-indexed sum in (3.1) for the polynomial witness. -/
noncomputable def sourceSum : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊(1 / 2 : ℝ)⌋ ⌊(3 / 2 : ℝ)⌋, oscillation (n : ℝ)

/-- The actual retained Fourier integrals in (3.2), with `N=0`. -/
noncomputable def sourceMain : ℂ :=
  ∑ v ∈ Finset.Icc (0 : ℤ) ⌊deriv phase (1 / 2)⌋,
    ∫ x in (1 / 2 : ℝ)..(3 / 2),
      (weight x : ℂ) * Complex.exp (Complex.I * (2 * Real.pi * (phase x - v * x) : ℝ))

/-- The literal endpoint expression named `G(a,b)` in the source. -/
noncomputable def sourceBoundary : ℝ :=
  ‖((⌊(3 / 2 : ℝ)⌋ : ℝ) - 3 / 2 + 1 / 2 : ℝ) * oscillation (3 / 2) -
    ((⌊(1 / 2 : ℝ)⌋ : ℝ) - 1 / 2 + 1 / 2 : ℝ) * oscillation (1 / 2)‖

/-- Lemma 2's displayed boundary majorant at a nonintegral endpoint. -/
noncomputable def sourceS1Bound (x y : ℝ) : ℝ :=
  if y < 1 then 0 else (1 / |Real.sin (Real.pi * x)|) * (1 / y + 1)

/-- The complete printed (3.2) expression specialized only by inserting the witness. -/
noncomputable def sourceError : ℝ :=
  let y := deriv phase (1 / 2)
  let d := 1 - (y - (⌊y⌋ : ℝ))
  (|deriv weight (1 / 2)| + 2 * Real.pi * weight (1 / 2) * y) /
      (2 * Real.pi ^ 2 * y) *
      (Real.log (1 + y) + Real.eulerMascheroniConstant + Real.log (1 + (⌊y⌋ : ℝ)) -
        (Complex.digamma d).re - 1 / (2 * (1 + (⌊y⌋ : ℝ))) - 1 / (2 * (1 + y))) +
    (weight (3 / 2) * |sourceS1Bound (3 / 2) y| +
      weight (1 / 2) * |sourceS1Bound (1 / 2) y|) / (2 * Real.pi) + sourceBoundary

/-- The integer and frequency indices reduce to the actual one-term remainder. -/
theorem source_remainder_eq : sourceSum - sourceMain = remainder := by
  have hsum : Finset.Ioc (0 : ℤ) 1 = {1} := by decide
  unfold sourceSum sourceMain
  rw [(hasDerivAt_phase _).deriv]
  norm_num [hsum, remainder, oscillation]

/-- Every endpoint and finite-boundary term of (3.2) is evaluated explicitly. -/
theorem source_error_eq : sourceError = printedBound := by
  unfold sourceError
  rw [(hasDerivAt_phase _).deriv, (hasDerivAt_weight _).deriv]
  norm_num [sourceBoundary, sourceS1Bound, weight, printedBound]
  field_simp [Real.pi_ne_zero]
  ring_nf
  simp

/-- The literal weighted-Poisson inequality fails for this admissible smooth witness. -/
theorem not_source_partI_inequality : ¬ ‖sourceSum - sourceMain‖ ≤ sourceError := by
  rw [source_remainder_eq, source_error_eq]
  exact not_le_of_gt printed_partI_bound_fails

end DhimanKadiriQuesadaHerrera2026.PoissonCounterexample
