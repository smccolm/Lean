import Tao2026.FourierApproximation
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Summability of Tao's two-dimensional Fourier decay

The proof of Proposition 1.12(ii) in the pinned source obtains
`|c_(n,m)| ≪ ‖W‖_{C³} (1 + |n| + |m|)⁻³` by integration by parts.  This
module proves the exact summability and finite-box tail consequences of that
decay.  Deriving the coefficient estimate from the derivatives of the
periodic weight remains a separate analytic step.
-/

open Complex Finset Filter
open scoped BigOperators Topology

namespace Tao2026

noncomputable section

/-- The source's radial `ℤ²` Fourier-coefficient decay envelope. -/
def fourierDecayWeight (q : ℤ × ℤ) : ℝ :=
  (1 + |(q.1 : ℝ)| + |(q.2 : ℝ)|) ^ (-(3 : ℝ))

/-- A separable one-dimensional majorant at exponent `3/2`. -/
def intFourierDecayWeight (n : ℤ) : ℝ :=
  (1 + |(n : ℝ)|) ^ (-(3 / 2 : ℝ))

theorem intFourierDecayWeight_nonneg (n : ℤ) :
    0 ≤ intFourierDecayWeight n := by
  exact Real.rpow_nonneg (by positivity) _

theorem summable_intFourierDecayWeight :
    Summable intFourierDecayWeight := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · have h := (Real.summable_one_div_nat_add_rpow 1 (3 / 2 : ℝ)).2 (by norm_num)
    convert h using 1
    funext n
    rw [intFourierDecayWeight, Int.cast_natCast,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)),
      Real.rpow_neg, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
    ring_nf
    all_goals positivity
  · have h := (Real.summable_one_div_nat_add_rpow 1 (3 / 2 : ℝ)).2 (by norm_num)
    convert h using 1
    funext n
    rw [intFourierDecayWeight, Int.cast_neg, abs_neg, Int.cast_natCast,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)), Real.rpow_neg,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
    ring_nf
    all_goals positivity

/-- Tao's radial decay is bounded by a product of summable `3/2`-power
weights. -/
theorem fourierDecayWeight_le_mul (q : ℤ × ℤ) :
    fourierDecayWeight q ≤
      intFourierDecayWeight q.1 * intFourierDecayWeight q.2 := by
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
    (by norm_num : -(3 / 2 : ℝ) ≤ 0)
  change z ^ (-(3 : ℝ)) ≤ x ^ (-(3 / 2 : ℝ)) * y ^ (-(3 / 2 : ℝ))
  rw [← Real.mul_rpow hx.le hy.le]
  calc
    z ^ (-(3 : ℝ)) = (z ^ 2) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
      norm_num
    _ ≤ (x * y) ^ (-(3 / 2 : ℝ)) := hpow

theorem fourierDecayWeight_nonneg (q : ℤ × ℤ) :
    0 ≤ fourierDecayWeight q := by
  exact Real.rpow_nonneg (by positivity) _

/-- The source's two-dimensional cubic coefficient envelope is summable. -/
theorem summable_fourierDecayWeight :
    Summable fourierDecayWeight := by
  have hproduct : Summable
      (fun q : ℤ × ℤ => intFourierDecayWeight q.1 * intFourierDecayWeight q.2) :=
    summable_intFourierDecayWeight.mul_of_nonneg
      summable_intFourierDecayWeight intFourierDecayWeight_nonneg
      intFourierDecayWeight_nonneg
  exact hproduct.of_nonneg_of_le fourierDecayWeight_nonneg fourierDecayWeight_le_mul

/-- Any coefficient family satisfying Tao's cubic envelope is absolutely
summable. -/
theorem summable_norm_of_fourierDecay
    (c : ℤ × ℤ → ℂ) {C : ℝ}
    (hc : ∀ q, ‖c q‖ ≤ C * fourierDecayWeight q) :
    Summable (fun q => ‖c q‖) := by
  exact (summable_fourierDecayWeight.mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _) hc

/-- Consequently the complex coefficient family itself is summable. -/
theorem summable_of_fourierDecay
    (c : ℤ × ℤ → ℂ) {C : ℝ}
    (hc : ∀ q, ‖c q‖ ≤ C * fourierDecayWeight q) :
    Summable c :=
  (summable_norm_of_fourierDecay c hc).of_norm

/-- The square frequency boxes exhaust `ℤ²` in the directed finite-set
filter. -/
theorem tendsto_fourierFrequencyBox_atTop :
    Tendsto fourierFrequencyBox atTop atTop := by
  rw [tendsto_atTop]
  intro s
  let R₀ : ℕ := ∑ q ∈ s, (q.1.natAbs + q.2.natAbs)
  filter_upwards [eventually_ge_atTop R₀] with R hR
  intro q hqs
  rw [mem_fourierFrequencyBox]
  have hterm : q.1.natAbs + q.2.natAbs ≤ R₀ := by
    dsimp [R₀]
    exact Finset.single_le_sum
      (s := s) (f := fun q : ℤ × ℤ => q.1.natAbs + q.2.natAbs)
      (fun _ _ => Nat.zero_le _) hqs
  have hfirst : q.1.natAbs ≤ R := by omega
  have hsecond : q.2.natAbs ≤ R := by omega
  constructor
  · rw [Int.abs_eq_natAbs]
    exact_mod_cast hfirst
  · rw [Int.abs_eq_natAbs]
    exact_mod_cast hsecond

/-- The `ℓ¹` mass outside the retained square frequency box tends to zero. -/
theorem tendsto_fourierCoefficientTail_zero (c : ℤ × ℤ → ℂ) :
    Tendsto (fun R : ℕ => ∑' q : {q // q ∉ fourierFrequencyBox R}, ‖c q‖)
      atTop (𝓝 0) :=
  (tendsto_tsum_compl_atTop_zero (fun q => ‖c q‖)).comp
    tendsto_fourierFrequencyBox_atTop

/-- For an absolutely summable coefficient family, the retained mass plus
the outer-box tail is exactly the full `ℓ¹` mass. -/
theorem sum_fourierFrequencyBox_add_tail
    (c : ℤ × ℤ → ℂ) (hc : Summable (fun q => ‖c q‖)) (R : ℕ) :
    (∑ q ∈ fourierFrequencyBox R, ‖c q‖) +
        (∑' q : {q // q ∉ fourierFrequencyBox R}, ‖c q‖) =
      ∑' q, ‖c q‖ :=
  hc.sum_add_tsum_subtype_compl (fourierFrequencyBox R)

/-- Absolute summability gives uniform convergence of Tao's finite square
Fourier polynomials to the corresponding infinite Fourier series. -/
theorem tendstoUniformly_finiteFourierPolynomial
    (c : ℤ × ℤ → ℂ) (hc : Summable (fun q => ‖c q‖)) :
    TendstoUniformly
      (fun R : ℕ => finiteFourierPolynomial (fourierFrequencyBox R) c)
      (fun x => ∑' q, c q * fourierMode2D q x) atTop := by
  have hUniform := tendstoUniformly_tsum hc
    (f := fun q x => c q * fourierMode2D q x)
    (fun q x => by rw [norm_mul, norm_fourierMode2D, mul_one])
  intro u hu
  simpa only [finiteFourierPolynomial] using
    tendsto_fourierFrequencyBox_atTop.eventually (hUniform u hu)

end

end Tao2026
