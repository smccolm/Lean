import DongWangWangZhang2026

/-! Exact consumer checks for the implemented objects and both frozen main theorems. -/

namespace DongWangWangZhang2026.SemanticRegression

theorem negativeCutoff (t : ℝ) : zetaSum (-1) t = 0 :=
  zetaSum_eq_zero_of_lt_one (by norm_num) t

theorem unitCutoff (t : ℝ) : zetaSum 1 t = 1 := by
  simp [zetaSum]

theorem zeroIndexExcluded (t : ℝ) : zetaTerm t 0 = 0 := zetaTerm_zero t

theorem bothHeightSigns (x t : ℝ) : ‖zetaSum x (-t)‖ = ‖zetaSum x t‖ :=
  norm_zetaSum_neg x t

theorem spectralShift (t : ℝ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => zetaTerm t n / (n : ℂ) ^ s) ∧
      (∑' n : ℕ, zetaTerm t n / (n : ℂ) ^ s) =
        riemannZeta (s - (t : ℂ) * Complex.I) :=
  ⟨summable_zetaTerm_div_cpow t hs, tsum_zetaTerm_div_cpow t hs⟩

theorem actualMaximizer (x t : ℝ) (hx : 1 < x) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧ ∀ u : ℝ, |u| ≤ Real.log x →
      ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) +
        ((u - t : ℝ) : ℂ) * Complex.I)‖ ≤
      ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) +
        ((t₀ - t : ℝ) : ℂ) * Complex.I)‖ :=
  exists_maximizingTwist hx t

theorem actualMobiusConvolution (x τ α : ℝ) :
    zetaSum x (τ + α) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
        ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) * phaseArithmetic τ) d *
          zetaTerm α d * zetaSum (x / d) α :=
  zetaSum_eq_mobius_twisted_sum x τ α

theorem primePowerCoefficient (τ : ℝ) (p k : ℕ) (hp : p.Prime) :
    ‖phaseMobiusCoeff τ (p ^ (k + 1))‖ = ‖zetaTerm τ p - 1‖ ∧
      ‖phaseMobiusCoeff τ (p ^ (k + 1))‖ ≤ 2 :=
  ⟨norm_phaseMobiusCoeff_prime_pow τ hp k, norm_phaseMobiusCoeff_prime_pow_le τ hp k⟩

theorem actualPrimeDistance (x t t₀ : ℝ) :
    primePhaseDistance x (t - t₀) =
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        (1 - (zetaTerm t p * star (zetaTerm t₀ p)).re) / p :=
  primePhaseDistance_eq_twisted x t t₀

theorem powerSumError (α x : ℝ) (hx : 1 ≤ x) :
    ‖zetaSum x α - (x : ℂ) ^ ((α : ℂ) * Complex.I + 1) / ((α : ℂ) * Complex.I + 1)‖ ≤
      min (4 * (1 + α ^ 2)) (2 * x) :=
  norm_zetaSum_sub_powerMain_le_min α hx

theorem twistedMeanReduction (x τ α : ℝ) (hx : 0 < x) :
    ‖zetaSum x (τ + α) -
      ((x : ℂ) ^ ((α : ℂ) * Complex.I) / ((α : ℂ) * Complex.I + 1)) * zetaSum x τ‖ ≤
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
        ‖phaseMobiusCoeff τ d‖ * min (5 * (1 + α ^ 2)) (2 * (x / d)) :=
  norm_mean_comparison_le_mobius_error hx τ α

theorem actualCoefficientMean (τ x : ℝ) (hx : 1 < x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖phaseMobiusCoeff τ n‖) ≤
      (2 * (Real.log 4 + 4) + 1) * x / Real.log x *
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖phaseMobiusCoeff τ n‖ / n :=
  sum_phaseMobiusAbs_le hx τ

theorem actualCoefficientTail (τ a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ‖phaseMobiusCoeff τ n‖ / n) ≤
      (2 * (Real.log 4 + 4) + 1) / Real.log a *
        (∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖phaseMobiusCoeff τ n‖ / n) * (1 + Real.log (b / a)) :=
  sum_phaseMobiusWeight_tail_le τ ha hab

theorem sourceMeanComparison (t t₀ x : ℝ) (hx : 1 < x) :
    ‖zetaSum x t / (x : ℂ) -
      ((x : ℂ) ^ ((t₀ : ℂ) * Complex.I) / ((t₀ : ℂ) * Complex.I + 1)) *
        (zetaSum x (t - t₀) / (x : ℂ))‖ ≤
      (42 * (2 * (Real.log 4 + 4) + 1) * Real.exp 8) *
        Real.log (Real.exp 1 + |t₀|) / Real.log x *
          Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ‖1 - zetaTerm (t - t₀) p‖ / p) :=
  norm_normalized_mean_comparison_le t t₀ hx

open MeasureTheory in
theorem actualLaplaceTransform (t : ℝ) (s : ℂ) (hs : 1 < s.re) :
    Integrable (fun u : ℝ => zetaSum (Real.exp u) t * Complex.exp (-s * u)) ∧
      (∫ u : ℝ, zetaSum (Real.exp u) t * Complex.exp (-s * u)) =
        riemannZeta (s - (t : ℂ) * Complex.I) / s :=
  ⟨integrable_zetaSum_exp t hs, integral_zetaSum_exp_univ t hs⟩

open scoped FourierTransform in
theorem actualFourierTransform (t ξ σ : ℝ) (hσ : 1 < σ) :
    𝓕 (fun u : ℝ => (Real.exp (-σ * u) : ℂ) * zetaSum (Real.exp u) t) ξ =
      riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * Complex.I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) :=
  fourier_dampedZetaSum t ξ hσ

open MeasureTheory in
theorem actualParseval (t σ : ℝ) (hσ : 1 < σ) :
    Integrable (fun ξ : ℝ => ‖riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * Complex.I) /
      ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)‖ ^ 2) ∧
    (∫ ξ : ℝ, ‖riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * Complex.I) /
      ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)‖ ^ 2) =
        ∫ u : ℝ, Real.exp (-2 * σ * u) * ‖zetaSum (Real.exp u) t‖ ^ 2 :=
  ⟨integrable_zeta_quotient_sq t hσ, integral_zeta_quotient_sq_eq_sum_sq t hσ⟩

open MeasureTheory in
theorem weightedLaplaceTransform (t : ℝ) (s : ℂ) (hs : 1 < s.re) :
    Integrable (fun u : ℝ => logZetaSum (Real.exp u) t * Complex.exp (-s * u)) ∧
      (∫ u : ℝ, logZetaSum (Real.exp u) t * Complex.exp (-s * u)) =
        -deriv riemannZeta (s - (t : ℂ) * Complex.I) / s :=
  ⟨integrable_logZetaSum_exp t hs, integral_logZetaSum_exp_univ t hs⟩

open scoped FourierTransform in
theorem weightedFourierTransform (t ξ σ : ℝ) (hσ : 1 < σ) :
    𝓕 (fun u : ℝ => (Real.exp (-σ * u) : ℂ) *
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, (Real.log n : ℂ) * zetaTerm t n) ξ =
        -deriv riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * Complex.I) /
          ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) :=
  fourier_dampedLogZetaSum t ξ hσ

open MeasureTheory in
theorem weightedParseval (t σ : ℝ) (hσ : 1 < σ) :
    Integrable (fun ξ : ℝ => ‖deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * Complex.I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)‖ ^ 2) ∧
    (∫ ξ : ℝ, ‖deriv riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * Complex.I) /
      ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)‖ ^ 2) =
        ∫ u : ℝ, Real.exp (-2 * σ * u) * ‖logZetaSum (Real.exp u) t‖ ^ 2 :=
  ⟨integrable_zeta_deriv_quotient_sq t hσ, integral_zeta_deriv_quotient_sq_eq_logSum_sq t hσ⟩

open MeasureTheory in
theorem logarithmicDerivativeMeanSquare (t σ : ℝ) (hσ : 1 < σ) :
    Integrable (fun ξ : ℝ => ‖(-deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * Complex.I)) /
          ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)‖ ^ 2) ∧
    (∫ ξ : ℝ, ‖(-deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * Complex.I)) /
          ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)‖ ^ 2) ≤
            (Real.log 4 + 4) ^ 2 / (2 * (σ - 1)) :=
  zeta_logDeriv_quotient_mean_square_le t hσ

open MeasureTheory in
theorem actualMaximizerNearMeanSquare (t x : ℝ) (hx : 1 < x) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      (∫ ξ in Set.Icc (-(Real.log x / (2 * Real.pi))) (Real.log x / (2 * Real.pi)),
        ‖deriv riemannZeta (twistZetaPoint x t (2 * Real.pi * ξ)) /
          ((((1 + 1 / Real.log x : ℝ) : ℂ)) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)‖ ^ 2) ≤
            ‖riemannZeta (twistZetaPoint x t t₀)‖ ^ 2 * (Real.log 4 + 4) ^ 2 * Real.log x / 2 :=
  exists_maximizingTwist_near_mean_square hx t

theorem actualDerivativeBlock (N : ℕ) (σ t y : ℝ) :
    zetaLogBlock N σ t y = ∑ n ∈ Finset.Ioc N (2 * N),
      LSeries.term (fun m => (Real.log m : ℂ) * zetaTerm t m) ((σ : ℂ) + (y : ℂ) * Complex.I) n :=
  zetaLogBlock_eq_LSeries_terms N σ t y

theorem blockConjugation (N : ℕ) (σ t y : ℝ) :
    zetaLogBlock N σ t (-y) = star (zetaLogBlock N σ (-t) y) :=
  zetaLogBlock_neg_frequency N σ t y

open MeasureTheory in
theorem shiftedBlockMeanSquare (N : ℕ) (σ t a b : ℝ) (hN : 0 < N) (hab : a ≤ b) :
    (∫ y : ℝ in a..b, ‖zetaLogBlock N σ t y‖ ^ 2) ≤
      (b - a + 2 * (5 * Real.pi + 1) * (N : ℝ)) *
        ∑ n ∈ Finset.Ioc N (2 * N), (Real.log n * (n : ℝ) ^ (-σ)) ^ 2 :=
  integral_norm_sq_zetaLogBlock_le N σ t a b hN hab

open MeasureTheory in
theorem actualBlockFarTail (N : ℕ) (σ t T : ℝ) (hN : 0 < N) (hσ : 0 < σ) (hT : 0 < T) :
    IntegrableOn (fun y : ℝ => ‖zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)
      {y : ℝ | T < |y|} ∧
    (∫ y in {y : ℝ | T < |y|}, ‖zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) ≤
      4 * (T + 2 * (5 * Real.pi + 1) * (N : ℝ)) *
        (∑ n ∈ Finset.Ioc N (2 * N), (Real.log n * (n : ℝ) ^ (-σ)) ^ 2) / T ^ 2 :=
  zetaLogBlock_far_tail N σ t T hN hσ hT

open MeasureTheory in
theorem exactGaussianGram (M : ℕ) (a : ℕ → ℂ) (T : ℝ) :
    ((∫ u : ℝ, Real.exp (-u ^ 2) *
      ‖∑ n ∈ Finset.Icc 1 M, a n * zetaTerm (-(T * u)) n‖ ^ 2 : ℝ) : ℂ) =
      (Real.sqrt Real.pi : ℂ) * ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        (a m * star (a n)) *
          ((Real.exp (-((T / 2) * (Real.log m - Real.log n)) ^ 2) : ℝ) : ℂ) :=
  integral_gaussian_logFrequencySum M a T

theorem actualDerivativeSeries (σ t y : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖zetaLogCoeff σ t n‖) ∧
    (∑' n : ℕ, zetaLogCoeff σ t n * zetaTerm (-y) n) =
      -deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * Complex.I) :=
  ⟨summable_norm_zetaLogCoeff σ t hσ, tsum_zetaLogCoeff_phase σ t y hσ⟩

theorem sharpDerivativeCoefficientSums (σ t : ℝ) (hσ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ((∑' n : ℕ, ‖zetaLogCoeff σ t n‖ ^ 2) ≤ 48) ∧
    ((∑' n : ℕ, (n : ℝ) * ‖zetaLogCoeff σ t n‖ ^ 2) ≤ 8 / (σ - 1) ^ 3) :=
  ⟨tsum_norm_zetaLogCoeff_sq_le σ t hσ, tsum_index_norm_zetaLogCoeff_sq_le σ t hσ hσ₂⟩

open MeasureTheory in
theorem actualFullDerivativeMeanSquare (σ t a b : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hab : 4 ≤ b - a) :
    (∫ y : ℝ in a..b, ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * Complex.I)‖ ^ 2) ≤
      48 * Real.sqrt Real.pi * Real.exp (5 / 4) * ((b - a) + 1 / (σ - 1) ^ 3) :=
  integral_zeta_deriv_sq_shift_le σ t a b hσ hσ₂ hab

open MeasureTheory in
theorem actualFullDerivativeFarTail (σ t T : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hT : 4 ≤ T) :
    IntegrableOn (fun y : ℝ => ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * Complex.I) /
      ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) {y : ℝ | T < |y|} ∧
    (∫ y in {y : ℝ | T < |y|},
      ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * Complex.I) /
        ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) ≤
      192 * Real.sqrt Real.pi * Real.exp (5 / 4) * (1 / T + 1 / ((σ - 1) ^ 3 * T ^ 2)) :=
  zeta_deriv_far_tail σ t T hσ hσ₂ hT

open MeasureTheory in
theorem poissonFrequencyNormalization (α v : ℝ) (hα : 0 < α) :
    Integrable (fun u : ℝ => (poissonLineKernel α u : ℂ) *
      Complex.exp (((v * u : ℝ) : ℂ) * Complex.I)) ∧
    (∫ u : ℝ, (poissonLineKernel α u : ℂ) *
      Complex.exp (((v * u : ℝ) : ℂ) * Complex.I)) = (Real.exp (-α * |v|) : ℂ) :=
  ⟨integrable_poissonLineKernel_phase hα v, integral_poissonLineKernel_phase hα v⟩

open MeasureTheory in
theorem actualZetaPoisson (σ t α y : ℝ) (hσ : 1 < σ) (hα : 0 < α) :
    Integrable (fun u : ℝ => (poissonLineKernel α u : ℂ) *
      riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * Complex.I)) ∧
    (∫ u : ℝ, (poissonLineKernel α u : ℂ) *
      riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * Complex.I)) =
        riemannZeta (((σ + α : ℝ) : ℂ) + ((y - t : ℝ) : ℂ) * Complex.I) :=
  poissonLine_zeta σ t α y hσ hα

theorem actualMaximizerRightward (x t : ℝ) (hx : 1 < x) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      ∀ α : ℝ, 0 < α → ∀ y : ℝ, |y| ≤ Real.log x / 2 →
        ‖riemannZeta ((((1 + 1 / Real.log x + α : ℝ) : ℂ)) +
          ((y - t : ℝ) : ℂ) * Complex.I)‖ ≤
            ‖riemannZeta (twistZetaPoint x t t₀)‖ +
              (1 + Real.log x) * (4 * α / (Real.pi * Real.log x)) :=
  exists_maximizingTwist_rightward_bound hx t

open MeasureTheory in
theorem actualMaximizerWeightedMeanSquare (x t : ℝ) (hx : 1 < x) (hxlog : 8 ≤ Real.log x) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      ∀ α : ℝ, 0 < α → 1 / Real.log x + α ≤ 1 →
        (∫ u : ℝ, Real.exp (-2 * (1 + 1 / Real.log x + α) * u) *
          ‖∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, (Real.log n : ℂ) * zetaTerm t n‖ ^ 2) ≤
          (‖riemannZeta (twistZetaPoint x t t₀)‖ +
            (1 + Real.log x) * (4 * α / (Real.pi * Real.log x))) ^ 2 *
              (Real.log 4 + 4) ^ 2 / (2 * (1 / Real.log x + α)) +
            (2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4) *
              (2 / Real.log x + 4 / ((1 / Real.log x + α) ^ 3 * (Real.log x) ^ 2))) :=
  exists_maximizingTwist_weighted_mean_square hx hxlog t

open MeasureTheory in
theorem actualDilationLaplace (t b : ℝ) (s : ℂ) (hs : 1 < s.re) :
    Integrable (fun u : ℝ => (zetaSum (Real.exp u) t -
      (Real.exp b : ℂ) * zetaSum (Real.exp (u - b)) t) * Complex.exp (-s * u)) ∧
    (∫ u : ℝ, (zetaSum (Real.exp u) t -
      (Real.exp b : ℂ) * zetaSum (Real.exp (u - b)) t) * Complex.exp (-s * u)) =
        (riemannZeta (s - (t : ℂ) * Complex.I) / s) * (1 - Complex.exp ((1 - s) * b)) :=
  laplace_zetaSum_dilation t b hs

open MeasureTheory in
theorem weightedDilationLaplace (t b : ℝ) (s : ℂ) (hs : 1 < s.re) :
    Integrable (fun u : ℝ => (logZetaSum (Real.exp u) t -
      (Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) t) * Complex.exp (-s * u)) ∧
    (∫ u : ℝ, (logZetaSum (Real.exp u) t -
      (Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) t) * Complex.exp (-s * u)) =
        (-deriv riemannZeta (s - (t : ℂ) * Complex.I) / s) *
          (1 - Complex.exp ((1 - s) * b)) :=
  laplace_logZetaSum_dilation t b hs

open MeasureTheory in
theorem actualDilationPoisson (σ t α y b : ℝ) (hσ : 1 < σ) (hα : 0 < α) (hb : 0 ≤ b) :
    Integrable (fun u : ℝ => (poissonLineKernel α u : ℂ) *
      (riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * Complex.I) *
        (1 - Complex.exp (((-(σ - 1) * b : ℝ) : ℂ) +
          (((-b * (y + u) : ℝ) : ℂ) * Complex.I))))) ∧
    (∫ u : ℝ, (poissonLineKernel α u : ℂ) *
      (riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * Complex.I) *
        (1 - Complex.exp (((-(σ - 1) * b : ℝ) : ℂ) +
          (((-b * (y + u) : ℝ) : ℂ) * Complex.I))))) =
      riemannZeta (((σ + α : ℝ) : ℂ) + ((y - t : ℝ) : ℂ) * Complex.I) *
        (1 - Complex.exp (((-(σ + α - 1) * b : ℝ) : ℂ) +
          (((-b * y : ℝ) : ℂ) * Complex.I))) :=
  poissonLine_zeta_dilation_difference σ t α y b hσ hα hb

theorem differenceMaximumTransport (σ t α T M y b : ℝ) (c : ℂ)
    (hσ : 1 < σ) (hα : 0 < α) (hT : 0 < T) (hb : 0 ≤ b) (hc : ‖c‖ ≤ 1)
    (hlocal : ∀ u : ℝ, |u| ≤ 2 * T →
      ‖riemannZeta ((σ : ℂ) + ((u - t : ℝ) : ℂ) * Complex.I) *
        (1 - c * Complex.exp (((-b * u : ℝ) : ℂ) * Complex.I))‖ ≤ M) (hy : |y| ≤ T) :
    ‖riemannZeta (((σ + α : ℝ) : ℂ) + ((y - t : ℝ) : ℂ) * Complex.I) *
      (1 - c * Complex.exp (((-α * b : ℝ) : ℂ) + (((-b * y : ℝ) : ℂ) * Complex.I)))‖ ≤
        M + (1 + 1 / (σ - 1)) * (4 * α / (Real.pi * T)) :=
  norm_shifted_zeta_difference_rightward_le σ t α T M y b c hσ hα hT hb hc hlocal hy

theorem exactConvergentEulerDistance (s : ℂ) (hs : 1 < s.re) :
    (∑' p : Nat.Primes, ((p : ℝ) ^ (-s.re) - ((p : ℂ) ^ (-s)).re)) ≤
      Real.log ‖riemannZeta (s.re : ℂ)‖ - Real.log ‖riemannZeta s‖ :=
  dampedPrimeDistance_le_log_norm_sub hs

theorem actualSourcePrimeDistanceBound (x t u : ℝ) (hx : 1 < x)
    (hxlog : 1 ≤ Real.log x) :
    ‖riemannZeta (twistZetaPoint x t u)‖ ≤
      (1 + Real.log x) * Real.exp (4 * (Real.log 4 + 4) -
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 - (zetaTerm (t - u) p).re) / p) :=
  norm_twistZeta_le_primePhaseDistance x t u hx hxlog

theorem reciprocalPrimeBound (x : ℝ) (hx : 1 < x) (hxlog : 1 ≤ Real.log x) :
    (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p) ≤
      Real.log (1 + Real.log x) + 2 * (Real.log 4 + 4) :=
  sum_prime_reciprocal_le hx hxlog

theorem sourceMeanComparisonDistance (t t₀ x : ℝ) (hx : 1 < x)
    (hxlog : 1 ≤ Real.log x) :
    ‖zetaSum x t / (x : ℂ) -
      ((x : ℂ) ^ ((t₀ : ℂ) * Complex.I) / ((t₀ : ℂ) * Complex.I + 1)) *
        (zetaSum x (t - t₀) / (x : ℂ))‖ ≤
      (42 * (2 * (Real.log 4 + 4) + 1) * Real.exp 8) *
        Real.log (Real.exp 1 + |t₀|) / Real.log x *
          Real.exp (Real.sqrt (2 * primePhaseDistance x (t - t₀) *
            (Real.log (1 + Real.log x) + 2 * (Real.log 4 + 4)))) :=
  norm_normalized_mean_comparison_le_distance t t₀ x hx hxlog

theorem actualQuarticMangoldtMass (k : ℕ) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.Ioc (k ^ 4) ((k + 1) ^ 4), ArithmeticFunction.vonMangoldt n) ≤
      2048 * (k : ℝ) ^ 3 :=
  sum_mangoldt_quarticCell_le_uniform k hk

theorem actualCutoffVariation (t a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖zetaSum b t - zetaSum a t‖ ≤ b - a + 1 :=
  norm_zetaSum_sub_le t ha hab

theorem actualMangoldtConvolution (x t : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Real.log n : ℂ) * zetaTerm t n) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt d : ℂ) * zetaTerm t d * zetaSum (x / d) t :=
  logZetaSum_eq_mangoldt_convolution x t

open MeasureTheory in
theorem actualPointwiseSmoothing (t x : ℝ) (hx : 1 < x) :
    ‖zetaSum x t‖ / x ≤
      2048 / Real.log x *
        (∫ v : ℝ in 0..Real.log x, Real.exp (-v) * ‖zetaSum (Real.exp v) t‖) +
          952321 / Real.log x :=
  norm_normalized_zetaSum_le_log_average t hx

open MeasureTheory in
theorem dampingReconstruction (L u : ℝ) (hu : 0 < u) :
    (∫ α : ℝ in 0..(1 / 2 : ℝ), Real.exp (-2 * (1 / L + α) * u)) =
      Real.exp (-2 * u / L) * (1 - Real.exp (-u)) / (2 * u) :=
  integral_damping_parameter L hu

open MeasureTheory in
theorem actualWeightedCauchy (t δ L : ℝ) (hδ : 0 < δ) (hL : 1 ≤ L) :
    (∫ u : ℝ in 1..L, Real.exp (-(1 + 2 * δ) * u) * ‖logZetaSum (Real.exp u) t‖) ≤
      Real.sqrt (1 / (2 * δ)) * Real.sqrt
        (∫ u : ℝ, Real.exp (-2 * (1 + δ) * u) * ‖logZetaSum (Real.exp u) t‖ ^ 2) :=
  integral_damped_logSum_le_sqrt t hδ hL

open MeasureTheory in
theorem parameterMinimumEvaluation (a b R : ℝ) (ha : 0 < a) (hR : 0 < R)
    (hac : a ≤ 2 / R) (hcb : 2 / R ≤ b) :
    (∫ u : ℝ in a..b, min R (2 / u) / u) ≤ R * (1 + Real.log (2 / (a * R))) :=
  integral_min_reciprocal_le ha hR hac hcb

theorem actualMaximizerMeanValue (x t : ℝ) (hx : 1 < x) (hxlog : 8 ≤ Real.log x) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      ‖zetaSum x t‖ / x ≤ 2048 / Real.log x * (1 + Real.log (Real.log x) +
        36 * meanValueAssemblyConstant *
          ((‖riemannZeta (twistZetaPoint x t t₀)‖ + 4) *
            (1 + Real.log (2 * Real.log x / (‖riemannZeta (twistZetaPoint x t t₀)‖ + 4))) + 2)) +
              952321 / Real.log x :=
  exists_maximizingTwist_mean_value_bound hx hxlog t

theorem actualDistanceMeanValue (x t : ℝ) (hx : 1 < x) (hxlog : 8 ≤ Real.log x) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      ‖zetaSum x t‖ / x ≤ ordinaryHalaszConstant *
        ((primePhaseDistance x (t - t₀) + 1) * Real.exp (-primePhaseDistance x (t - t₀)) +
          (1 + Real.log (Real.log x)) / Real.log x) :=
  exists_maximizingTwist_prime_distance_mean_bound hx hxlog t

theorem crudePrimeDistance (x τ : ℝ) (hx : 1 < x) (hxlog : 8 ≤ Real.log x) :
    primePhaseDistance x τ + 1 ≤ (4 * (Real.log 4 + 4) + 5) * Real.log (Real.log x) :=
  primePhaseDistance_add_one_le_log x τ hx hxlog

theorem uniformMeanErrorThreshold :
    ∃ L₀ : ℝ, 8 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      ordinaryHalaszConstant * ((1 + Real.log L) / L) ≤ 1 / (2 * L ^ (1 / 100 : ℝ)) :=
  exists_ordinary_mean_error_threshold

theorem sourceLargeSumPrimeDistance :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ t N : ℝ, 1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) →
        ‖zetaSum x t‖ = x / N →
        ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
          (∀ u : ℝ, |u| ≤ Real.log x →
            ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
          primePhaseDistance x (t - t₀) ≤
            (1 / 100 : ℝ) * Real.log (Real.log x) + Real.log (Real.log (Real.log x)) + C :=
  exists_large_sum_prime_distance_bound

theorem exactInverseTwistFactor (x a : ℝ) (hx : 0 < x) :
    (((a : ℂ) * Complex.I + 1) * (x : ℂ) ^ (-((a : ℂ) * Complex.I))) *
      comparisonFactor x a = 1 :=
  inverse_comparisonFactor_mul hx a

theorem sameTwistQuantitativeBounds :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ t N : ℝ, 1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) →
        ‖zetaSum x t‖ = x / N →
        ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
          (∀ u : ℝ, |u| ≤ Real.log x →
            ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
          |t₀| ≤ 4 * N ∧
          primePhaseDistance x (t - t₀) ≤
            (1 / 100 : ℝ) * Real.log (Real.log x) + Real.log (Real.log (Real.log x)) + C ∧
          ‖zetaSum x (t - t₀) -
            (((t₀ : ℂ) * Complex.I + 1) * (x : ℂ) ^ (-((t₀ : ℂ) * Complex.I))) *
              zetaSum x t‖ ≤ 4 * x / (Real.log x) ^ (3 / 4 : ℝ) :=
  exists_large_sum_twist_bounds

theorem actualThetaLogarithmicError (A : ℕ) :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      |Chebyshev.theta x - x| ≤ x / (Real.log x) ^ A :=
  exists_theta_logarithmic_error A

theorem actualPrimeCosine (A : ℕ) (hA : 1 ≤ A) :
    ∃ X : ℝ, 3 ≤ X ∧ 1 ≤ Real.log X ∧ ∀ a b β : ℝ, X ≤ a → a ≤ b →
      1 ≤ |β| * Real.log a → |β| ≤ Real.log a ^ A →
      (∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
        |Real.cos (β * Real.log p / 2)| / p) ≤
          (75 / 113 : ℝ) * (Real.log (Real.log b) - Real.log (Real.log a)) + 8 :=
  exists_prime_absolute_cosine_bound A hA

theorem actualTwoPointZeta (A : ℕ) (hA : 1 ≤ A) :
    ∃ X : ℝ, 3 ≤ X ∧ 1 ≤ Real.log X ∧ ∀ a x τ υ : ℝ, X ≤ a → a ≤ x →
      1 ≤ |τ - υ| * Real.log a → |τ - υ| ≤ Real.log a ^ A →
      ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) - (τ : ℂ) * Complex.I)‖ *
        ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) - (υ : ℂ) * Complex.I)‖ ≤
          (1 + Real.log x) ^ 2 * Real.exp
            (8 * (Real.log 4 + 4) + 24 -
              (76 / 113 : ℝ) * (Real.log (Real.log x) - Real.log (Real.log a))) :=
  exists_two_point_zeta_bound A hA

theorem sameMaximizerFrequencyBound (A : ℕ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ y : ℝ, 1 < x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 1 / Real.log x ≤ |y| → |y| ≤ Real.log x / 2 →
      ‖riemannZeta (twistZetaPoint x t (t₀ + y))‖ ≤
        (1 + Real.log x) * Real.exp
          (4 * (Real.log 4 + 4) + 12 - (38 / 113 : ℝ) *
            (Real.log (Real.log x) -
              Real.log (max B (max (1 / |y|) ((Real.log x) ^ ((A : ℝ)⁻¹)))))) :=
  exists_maximizingTwist_uniform_frequency_bound A hA

theorem actualMaximizerDilationFactor (A : ℕ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ b y : ℝ, 1 < x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 0 ≤ b → |y| ≤ Real.log x / 2 →
      ‖riemannZeta (twistZetaPoint x t (t₀ + y)) *
        (1 - Complex.exp (-((b / Real.log x : ℝ) : ℂ) + ((-b * y : ℝ) : ℂ) * Complex.I))‖ ≤
          4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + Real.log x) *
            (max B (max b ((Real.log x) ^ ((A : ℝ)⁻¹))) / Real.log x) ^ (38 / 113 : ℝ) :=
  exists_maximizingTwist_dilation_factor_bound A hA

theorem actualDilationRightwardBound (A : ℕ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ b α y : ℝ, 1 < x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 0 ≤ b → 0 < α → |y| ≤ Real.log x / 4 →
      ‖riemannZeta (((1 + 1 / Real.log x + α : ℝ) : ℂ) +
          ((y - (t - t₀) : ℝ) : ℂ) * Complex.I) *
        (1 - Complex.exp (-(((1 / Real.log x + α) * b : ℝ) : ℂ) +
          ((-b * y : ℝ) : ℂ) * Complex.I))‖ ≤
          4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + Real.log x) *
            (max B (max b ((Real.log x) ^ ((A : ℝ)⁻¹))) / Real.log x) ^ (38 / 113 : ℝ) +
              (1 + Real.log x) * (16 * α / (Real.pi * Real.log x)) :=
  exists_maximizingTwist_dilation_rightward_bound A hA

open MeasureTheory in
theorem weightedDilationParseval (t b σ : ℝ) (hσ : 1 < σ) :
    (∫ ξ : ℝ, ‖(deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * Complex.I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) *
          (1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) +
            ((-b * (2 * Real.pi * ξ) : ℝ) : ℂ) * Complex.I))‖ ^ 2) =
      ∫ u : ℝ, Real.exp (-2 * σ * u) *
        ‖logZetaSum (Real.exp u) t -
          (Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) t‖ ^ 2 :=
  integral_zeta_deriv_dilation_sq_eq_logDifference_sq t b hσ

open MeasureTheory in
theorem actualWeightedDilationMeanSquare (A : ℕ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ b α : ℝ, 1 < x → 16 ≤ Real.log x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 0 ≤ b → 0 < α → 1 / Real.log x + α ≤ 1 →
      (∫ u : ℝ, Real.exp (-2 * (1 + 1 / Real.log x + α) * u) *
        ‖logZetaSum (Real.exp u) (t - t₀) -
          (Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) (t - t₀)‖ ^ 2) ≤
        (4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + Real.log x) *
          (max B (max b ((Real.log x) ^ ((A : ℝ)⁻¹))) / Real.log x) ^ (38 / 113 : ℝ) +
            (1 + Real.log x) * (16 * α / (Real.pi * Real.log x))) ^ 2 *
              (Real.log 4 + 4) ^ 2 / (2 * (1 / Real.log x + α)) +
          4 * ((2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4) *
            (4 / Real.log x + 16 / ((1 / Real.log x + α) ^ 3 * (Real.log x) ^ 2)))) :=
  exists_maximizingTwist_weighted_dilation_mean_square A hA

open MeasureTheory in
theorem cappedWeightedDilationMeanSquare (A : ℕ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ b α : ℝ, 1 < x → 16 ≤ Real.log x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 0 ≤ b → 0 < α → 1 / Real.log x + α ≤ 1 →
      (∫ u : ℝ, Real.exp (-2 * (1 + 1 / Real.log x + α) * u) *
        ‖logZetaSum (Real.exp u) (t - t₀) -
          (Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) (t - t₀)‖ ^ 2) ≤
        (min (4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + Real.log x) *
          (max B (max b ((Real.log x) ^ ((A : ℝ)⁻¹))) / Real.log x) ^ (38 / 113 : ℝ) + 16)
            (4 / (1 / Real.log x + α))) ^ 2 *
              (Real.log 4 + 4) ^ 2 / (2 * (1 / Real.log x + α)) +
          4 * ((2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4) *
            (4 / Real.log x + 16 / ((1 / Real.log x + α) ^ 3 * (Real.log x) ^ 2)))) :=
  exists_maximizingTwist_weighted_dilation_mean_square_min A hA

theorem actualDilationConvolution (t : ℝ) {w x : ℝ} (hw : 1 ≤ w) (hx : 0 ≤ x) :
    logZetaSum x t - (w : ℂ) * logZetaSum (x / w) t =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt d : ℂ) * zetaTerm t d *
        (zetaSum (x / d) t - (w : ℂ) * zetaSum ((x / d) / w) t) :=
  logZetaSumDilation_eq_mangoldt_convolution t hw hx

theorem activeDilationFloorCost (x w : ℝ) (K : ℕ) (hx : 0 ≤ x) (hw : 1 ≤ w) :
    (∑ k ∈ Finset.Icc 1 K, if (k : ℝ) ^ 4 ≤ x / w then
      w * ((((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
        ((x / w) / (k : ℝ) ^ 4 - (x / w) / ((k : ℝ) + 1) ^ 4 + 1)) else 0) ≤ 465 * x :=
  sum_active_quarticCell_variation_cost_le x w K hx hw

open MeasureTheory in
theorem actualDilationPointwiseSmoothing (t : ℝ) {b Y : ℝ} (hb : 0 ≤ b) (hY : 0 < Y) :
    Real.exp (-Y) * ‖zetaSum (Real.exp Y) t -
      (Real.exp b : ℂ) * zetaSum (Real.exp (Y - b)) t‖ ≤
      2048 / Y * (∫ u : ℝ in 0..Y, Real.exp (-u) *
        ‖zetaSum (Real.exp u) t - (Real.exp b : ℂ) * zetaSum (Real.exp (u - b)) t‖) +
          (1904642 + b) / Y :=
  norm_exp_dilation_le_log_average t hb hY

open MeasureTheory in
theorem translationScaleLogRemoval (t : ℝ) {b Y : ℝ}
    (hb : 0 ≤ b) (hY : b + 1 ≤ Y) :
    (∫ u : ℝ in 0..Y, Real.exp (-u) * ‖zetaSumDilation t (Real.exp b) (Real.exp u)‖) ≤
      2 * (b + 1) + (2 + b) * Real.log (Y / (b + 1)) +
        ∫ u : ℝ in 1..Y, Real.exp (-u) *
          ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ / u :=
  integral_normalized_zetaDilation_le_logDilation t hb hY

open MeasureTheory in
theorem fixedSourceLineReconstruction {L u : ℝ}
    (hL : 0 < L) (hu : 1 ≤ u) (huL : u ≤ 2 * L) :
    1 / u ≤ 324 * ∫ α : ℝ in 0..(1 / 2 : ℝ), Real.exp (-2 * (1 / L + α) * u) :=
  reciprocal_le_damping_parameter_double hL hu huL

open MeasureTheory in
theorem uniformSizeParameterEvaluation {L R q : ℝ} (hL : 8 ≤ L)
    (hR : 0 ≤ R) (hq : 0 < q) (hq₁ : q < 1) :
    (∫ α : ℝ in 0..(1 / 2 : ℝ), dilationDampingBound L R α) ≤
      4 * meanValueAssemblyConstant *
        ((R + 4) ^ q * (2 : ℝ) ^ (1 - q) * L ^ (1 - q) / (1 - q) + 2) :=
  integral_dilationDampingBound_le_rpow hL hR hq hq₁

open MeasureTheory in
theorem actualMaximizerDilationPowerBound (A : ℕ) (hA : 1 ≤ A)
    {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ b Y : ℝ, 1 < x → 16 ≤ Real.log x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 0 ≤ b → b + 1 ≤ Y → Y ≤ 2 * Real.log x →
      let R := 4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + Real.log x) *
        (max B (max b ((Real.log x) ^ ((A : ℝ)⁻¹))) / Real.log x) ^ (38 / 113 : ℝ) + 16
      Real.exp (-Y) * ‖zetaSum (Real.exp Y) (t - t₀) -
        (Real.exp b : ℂ) * zetaSum (Real.exp (Y - b)) (t - t₀)‖ ≤
          2048 / Y * (2 * (b + 1) + (2 + b) * Real.log (Y / (b + 1)) +
            1296 * meanValueAssemblyConstant *
              ((R + 4) ^ q * (2 : ℝ) ^ (1 - q) *
                (Real.log x) ^ (1 - q) / (1 - q) + 2)) + (1904642 + b) / Y :=
  exists_maximizingTwist_dilation_power_bound A hA hq hq₁

theorem exactThirdExponentAbsorption {L b : ℝ} (hL : 1 ≤ L)
    (hb : 0 ≤ b) (hbL : b + 1 ≤ L) :
    (max b (L ^ (1 / 1000 : ℝ)) / L) ^ (3781 / 11300 : ℝ) ≤
      ((b + 1) / L) ^ (1 / 3 : ℝ) :=
  optimized_dilation_scale_le_third hL hb hbL

theorem exactNormalizedDilation (t b Y : ℝ) :
    ‖zetaSum (Real.exp Y) t / (Real.exp Y : ℂ) -
      zetaSum (Real.exp (Y - b)) t / (Real.exp (Y - b) : ℂ)‖ =
        Real.exp (-Y) * ‖zetaSum (Real.exp Y) t -
          (Real.exp b : ℂ) * zetaSum (Real.exp (Y - b)) t‖ :=
  norm_normalized_dilation_eq t b Y

theorem actualAllRealLipschitz :
    ∃ L₀ : ℝ, 16 ≤ L₀ ∧ ∀ x t t₀ : ℝ, 1 < x → L₀ ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → ∀ y : ℝ,
      ‖zetaSum (Real.exp y) (t - t₀) / (Real.exp y : ℂ) -
        zetaSum (Real.exp (Real.log x)) (t - t₀) / (Real.exp (Real.log x) : ℂ)‖ ≤
          dilationLipschitzConstant *
            ((1 + |y - Real.log x|) / Real.log x) ^ (1 / 3 : ℝ) :=
  exists_maximizingTwist_uniform_lipschitz

theorem fullSourceMaximizingTwist :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ t N : ℝ, 1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) →
        ‖zetaSum x t‖ = x / N →
        ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
          (∀ u : ℝ, |u| ≤ Real.log x →
            ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
          |t₀| ≤ C * N ∧
          primePhaseDistance x (t - t₀) ≤
            (1 / 100 : ℝ) * Real.log (Real.log x) + Real.log (Real.log (Real.log x)) + C ∧
          (∀ y : ℝ, ‖zetaSum (Real.exp y) (t - t₀) / (Real.exp y : ℂ) -
            zetaSum (Real.exp (Real.log x)) (t - t₀) / (Real.exp (Real.log x) : ℂ)‖ ≤
              C * ((1 + |y - Real.log x|) / Real.log x) ^ (1 / 3 : ℝ)) ∧
          ‖zetaSum x (t - t₀) -
            (((t₀ : ℂ) * Complex.I + 1) * (x : ℂ) ^ (-((t₀ : ℂ) * Complex.I))) *
              zetaSum x t‖ ≤ C * x / (Real.log x) ^ (3 / 4 : ℝ) :=
  exists_large_sum_maximizing_twist

theorem uniformLeftStripZeta (a v : ℝ) (ha : 0 < a) (ha2 : a ≤ 1 / 2) :
    ‖riemannZeta (1 - (a : ℂ) + v * Complex.I)‖ ≤ 8 * (2 + |v|) ^ a / a := by
  simpa only [Complex.ofReal_sub, Complex.ofReal_one] using norm_zeta_left_strip_le a v ha ha2

theorem zeroHeightLeftStrip (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 1 / 2) :
    ‖riemannZeta ((1 - a : ℝ) : ℂ)‖ ≤ 8 * (2 : ℝ) ^ a / a := by
  simpa using norm_zeta_left_strip_le a 0 ha ha2

theorem closedHalfEndpoint (v : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + v * Complex.I)‖ ≤ 16 * (2 + |v|) ^ (1 / 2 : ℝ) := by
  have h := norm_zeta_left_strip_le (1 / 2) v (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith only [h]

theorem explicitZetaPoleTruncation {N : ℕ} (hN : 1 ≤ N) {σ v : ℝ}
    (hσ : 0 < σ) (hs : (σ : ℂ) + v * Complex.I ≠ 1) :
    ‖riemannZeta ((σ : ℂ) + v * Complex.I) -
      ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ((σ : ℂ) + v * Complex.I)) +
        (-(N : ℂ) ^ (1 - ((σ : ℂ) + v * Complex.I))) /
          (1 - ((σ : ℂ) + v * Complex.I)))‖ ≤
      (N : ℝ) ^ (-σ) / 2 + (σ + |v|) * (N : ℝ) ^ (-σ) / σ :=
  norm_zeta_sub_sum_pole_le hN hσ hs

theorem continuedActualMellin (t : ℝ) {s : ℂ} (hs : 0 < s.re)
    (hp : s ≠ (t : ℂ) * Complex.I + 1) :
    zetaRemainderMellin t s = riemannZeta (s - (t : ℂ) * Complex.I) / s -
      1 / (((t : ℂ) * Complex.I + 1) * (s - ((t : ℂ) * Complex.I + 1))) :=
  zetaRemainderMellin_eq t hs hp

theorem actualStripTransform (t : ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MeasureTheory.Integrable (fun u : ℝ => zetaExpRemainder t u * Complex.exp (-s * u)) ∧
      (∫ u : ℝ, zetaExpRemainder t u * Complex.exp (-s * u)) =
        riemannZeta (s - (t : ℂ) * Complex.I) / s :=
  ⟨integrable_zetaExpRemainder t hs0 hs1, integral_zetaExpRemainder t hs0 hs1⟩

theorem gaussianPoleAtZeroTwist (a V : ℝ) (hV : 0 < V) :
    (Real.sqrt (2 * Real.pi * V) : ℂ) *
      (∫ u : ℝ, Complex.exp ((a : ℂ) * u - (V : ℂ) * u ^ 2 / 2)) =
        (2 * Real.pi : ℂ) * Complex.exp ((a : ℂ) ^ 2 / (2 * (V : ℂ))) := by
  simpa using integral_source_gaussian_pole a 0 V hV

theorem bothSourceGaussianIntegrals (a t V : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hV : 0 < V) :
    MeasureTheory.Integrable (fun u : ℝ => zetaSum (Real.exp u) t *
      (Real.exp ((a - 1) * u - V * u ^ 2 / 2) : ℂ)) ∧
    MeasureTheory.Integrable (fun ξ : ℝ =>
      (riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * Complex.I) /
        (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * Complex.I)) *
          (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ)) :=
  ⟨integrable_source_gaussian_sum a t V ha (by linarith) hV,
    integrable_source_gaussian_zeta a t V ha (by linarith) hV⟩

theorem exactResidueBearingGaussian (a t V : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hV : 0 < V) :
    (Real.sqrt (2 * Real.pi * V) : ℂ) *
      (∫ u : ℝ, zetaSum (Real.exp u) t *
        (Real.exp ((a - 1) * u - V * u ^ 2 / 2) : ℂ)) =
      (∫ ξ : ℝ, (riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * Complex.I) /
        (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * Complex.I)) *
          (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ)) +
        (2 * Real.pi : ℂ) / (1 + (t : ℂ) * Complex.I) *
          Complex.exp (((a : ℂ) + (t : ℂ) * Complex.I) ^ 2 / (2 * (V : ℂ))) :=
  source_gaussian_identity a t V ha ha2 hV

theorem xiActualZeros (p : XiZero) :
    riemannZeta (xiZeroPoint p) = 0 ∧
      0 < (xiZeroPoint p).re ∧ (xiZeroPoint p).re < 1 :=
  ⟨xiZeroPoint_zeta_zero p, xiZeroPoint_re p⟩

theorem xiMultiplicityFiber (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := Complex.riemannXi) s).card =
      analyticOrderNatAt riemannZeta s :=
  xi_zero_fiber_card hs hs1

theorem xiReflectionLabels (p : XiZero) :
    xiZeroReflect (xiZeroReflect p) = p ∧
      xiZeroPoint (xiZeroReflect p) = 1 - xiZeroPoint p :=
  ⟨xiZeroReflect_involutive p, xiZeroPoint_reflect p⟩

theorem xiGenusOneConvergence :
    Summable (fun p : XiZero => ‖xiZeroPoint p‖⁻¹ ^ (2 : ℕ)) ∧
      Summable (fun p : XiZero => (1 / xiZeroPoint p).re) :=
  ⟨summable_xiZero_norm_inv_sq, summable_xiZero_re_inv⟩

theorem xiRealLogDerivative (s : ℂ) (hs : 1 ≤ s.re) :
    Summable (fun p : XiZero => (1 / (s - xiZeroPoint p)).re) ∧
      (logDeriv Complex.riemannXi s).re =
        ∑' p : XiZero, (1 / (s - xiZeroPoint p)).re :=
  re_xi_logDeriv_eq_tsum_of_one_le_re hs

theorem xiZetaGammaDecomposition (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : XiZero => (1 / (s - xiZeroPoint p)).re) ∧
      (∑' p : XiZero, (1 / (s - xiZeroPoint p)).re) =
        (1 / s + 1 / (s - 1) - Complex.log (Real.pi : ℂ) / 2 +
          logDeriv Complex.Gamma (s / 2) / 2 + logDeriv riemannZeta s).re :=
  tsum_xiZero_re_eq_zeta_gamma hs

theorem xiRepulsionKernelConvergence (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : XiZero => 1 / ‖s - xiZeroPoint p‖ ^ 2) :=
  summable_xiZero_inverse_square hs

theorem coefficientOneDigamma (z : ℂ) (hz : 1 / 4 ≤ z.re) :
    |(Complex.digamma z).re - Real.log (‖z‖ + 2)| ≤
      14 + |Real.eulerMascheroniConstant| :=
  abs_re_digamma_sub_log_norm_le hz

theorem uniformZetaLogDerivativePole :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 < s.re →
      ‖logDeriv riemannZeta s‖ ≤ 1 / (s.re - 1) + C :=
  exists_norm_logDeriv_zeta_le_pole

theorem exactSourceZeroSumUpper :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a v : ℝ, 0 < a → 2 ≤ |v| →
      Summable (fun p : XiZero =>
        (1 / ((((1 + a : ℝ) : ℂ) + (v : ℂ) * Complex.I) - xiZeroPoint p)).re) ∧
      (∑' p : XiZero,
        (1 / ((((1 + a : ℝ) : ℂ) + (v : ℂ) * Complex.I) - xiZeroPoint p)).re) ≤
        (1 / 2) * Real.log (2 + a + |v|) + 1 / a + C :=
  exists_source_zero_sum_upper

theorem zeroSumBothClosedHeightEndpoints :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → ∀ v : ℝ, v = 2 ∨ v = -2 →
      Summable (fun p : XiZero =>
        (1 / ((((1 + a : ℝ) : ℂ) + (v : ℂ) * Complex.I) - xiZeroPoint p)).re) ∧
      (∑' p : XiZero,
        (1 / ((((1 + a : ℝ) : ℂ) + (v : ℂ) * Complex.I) - xiZeroPoint p)).re) ≤
        (1 / 2) * Real.log (4 + a) + 1 / a + C := by
  obtain ⟨C, hC, hb⟩ := exists_source_zero_sum_upper
  refine ⟨C, hC, ?_⟩
  intro a ha v hv
  have hab : |v| = 2 := by rcases hv with rfl | rfl <;> norm_num
  simpa only [hab, show 2 + a + 2 = 4 + a by ring] using
    hb a v ha (by rw [hab])

theorem digammaClosedQuarterBoundary (v : ℝ) :
    |(Complex.digamma ((1 / 4 : ℂ) + (v : ℂ) * Complex.I)).re -
      Real.log (‖(1 / 4 : ℂ) + (v : ℂ) * Complex.I‖ + 2)| ≤
        14 + |Real.eulerMascheroniConstant| :=
  abs_re_digamma_sub_log_norm_le (by simp)

theorem actualXiQuadraticShift (s : ℂ) (hs : 1 < s.re) (r : ℝ) :
    ‖Complex.riemannXi (s - (r : ℂ))‖ ≤ ‖Complex.riemannXi s‖ *
      Real.exp (-r * (logDeriv Complex.riemannXi s).re +
        (r ^ 2 / 2) * ∑' p : XiZero, 1 / ‖s - xiZeroPoint p‖ ^ 2) :=
  norm_xi_sub_real_le hs r

theorem actualGammaSourceRatio (a u : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hu : 2 ≤ |u|) :
    ‖Complex.Gammaℝ (((1 + a : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ ≤
      ‖Complex.Gammaℝ (((1 - a : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ *
        Real.exp (a * (Real.log (2 + |u|) + (14 + |Real.eulerMascheroniConstant|))) :=
  norm_GammaReal_source_ratio_le ha ha2 hu

theorem uniformXiLowerLogarithm :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → ∀ u : ℝ,
      (1 / 2) * Real.log (2 + |u|) - 1 / a - C ≤
        (logDeriv Complex.riemannXi (((1 + a : ℝ) : ℂ) + (u : ℂ) * Complex.I)).re :=
  exists_re_xi_logDeriv_source_lower

theorem exactSourceZeroRepulsion :
    ∃ C : ℝ, 0 < C ∧ ∀ a u : ℝ, 0 < a → a ≤ 1 / 2 →
      Summable (fun p : XiZero =>
        2 * a ^ 2 / ‖(((1 + a : ℝ) : ℂ) + (u : ℂ) * Complex.I) - xiZeroPoint p‖ ^ 2) ∧
      ‖riemannZeta (((1 - a : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ ≤
        (C / a) * Real.exp (∑' p : XiZero,
          2 * a ^ 2 / ‖(((1 + a : ℝ) : ℂ) + (u : ℂ) * Complex.I) - xiZeroPoint p‖ ^ 2) :=
  exists_source_zero_repulsion

theorem zeroRepulsionZeroHeight :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 / 2 →
      ‖riemannZeta ((1 - a : ℝ) : ℂ)‖ ≤
        (C / a) * Real.exp (∑' p : XiZero,
          2 * a ^ 2 / ‖((1 + a : ℝ) : ℂ) - xiZeroPoint p‖ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_source_zero_repulsion
  exact ⟨C, hC, fun a ha ha2 => by simpa using (hb a 0 ha ha2).2⟩

theorem zeroRepulsionClosedHalf :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
      ‖riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * Complex.I)‖ ≤
        (2 * C) * Real.exp (∑' p : XiZero,
          (1 / 2 : ℝ) / ‖(3 / 2 : ℂ) + (u : ℂ) * Complex.I - xiZeroPoint p‖ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_source_zero_repulsion
  refine ⟨C, hC, fun u => ?_⟩
  have h := (hb (1 / 2) u (by norm_num) (by norm_num)).2
  norm_num at h ⊢
  rw [show C / (1 / 2 : ℝ) = 2 * C by ring] at h
  exact h

theorem zeroConjugationLabels (p : XiZero) :
    xiZeroConj (xiZeroConj p) = p ∧ xiZeroPoint (xiZeroConj p) = star (xiZeroPoint p) :=
  ⟨xiZeroConj_involutive p, xiZeroPoint_conj p⟩

theorem finiteSourceZeroCounts (u r δ : ℝ) :
    {p : XiZero | xiZeroPoint p ∈ sourceZeroDisk u r}.Finite ∧
      {p : XiZero | xiZeroPoint p ∈ sourceZeroWindow u δ}.Finite :=
  ⟨finite_xiZero_sourceDisk u r, finite_xiZero_sourceWindow u δ⟩

theorem exactClosedWindowMultiplicity {δ : ℝ} (hδ : δ < 1) (u : ℝ) :
    zeroCountIn (sourceZeroWindow u δ) =
      RiemannZeta.GuthMaynard.zeroCountRect (1 - δ) 1 (u - δ) (u + δ) :=
  zeroCountIn_sourceWindow_eq hδ u

theorem sourceZeroCountsBothSigns (u r δ : ℝ) :
    zeroCountIn (sourceZeroDisk (-u) r) = zeroCountIn (sourceZeroDisk u r) ∧
      zeroCountIn (sourceZeroWindow (-u) δ) = zeroCountIn (sourceZeroWindow u δ) :=
  ⟨zeroCountIn_sourceDisk_neg u r, zeroCountIn_sourceWindow_neg u δ⟩

theorem openDiskBoundaryExcluded (z : ℂ) (u r : ℝ)
    (h : ‖z - (1 + (u : ℂ) * Complex.I)‖ = r) : z ∉ sourceZeroDisk u r := by
  change ¬ ‖z - (1 + (u : ℂ) * Complex.I)‖ < r
  rw [h]
  exact lt_irrefl _

theorem closedWindowCornerIncluded (u : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((1 - δ : ℝ) : ℂ) + ((u + δ : ℝ) : ℂ) * Complex.I ∈ sourceZeroWindow u δ := by
  simp [sourceZeroWindow, abs_of_nonneg hδ]

theorem sourceDiskWindowCountTransfer (u δ : ℝ) :
    zeroCountIn (sourceZeroDisk u δ) ≤ zeroCountIn (sourceZeroWindow u δ) :=
  zeroCountIn_disk_le_window u le_rfl

theorem convergentKernelBothSigns {a : ℝ} (ha : 0 < a) (v : ℝ) :
    Summable (fun p : XiZero =>
      a / ‖(((1 + a : ℝ) : ℂ) + (v : ℂ) * Complex.I) - xiZeroPoint p‖ ^ 2) ∧
    (∑' p : XiZero,
      a / ‖(((1 + a : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * Complex.I) - xiZeroPoint p‖ ^ 2) =
    ∑' p : XiZero,
      a / ‖(((1 + a : ℝ) : ℂ) + (v : ℂ) * Complex.I) - xiZeroPoint p‖ ^ 2 :=
  source_zero_kernel_neg_height ha v


theorem gaussianFixedMoment :
    MeasureTheory.Integrable gaussianMomentMajorant ∧ 0 ≤ gaussianMomentConstant :=
  ⟨integrable_gaussianMomentMajorant, gaussianMomentConstant_nonneg⟩

theorem gaussianLinkedOneSixth {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    (Real.sqrt (a / L) * L) ^ (1 / 3 : ℝ) = (a * L) ^ (1 / 6 : ℝ) :=
  source_gaussian_width_third ha hL

theorem gaussianActualErrorIntegrable {L r : ℝ} (hr : 0 < r) (t : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ =>
      (zetaSum (Real.exp y) t / (Real.exp y : ℂ) -
        zetaSum (Real.exp L) t / (Real.exp L : ℂ)) *
        (Real.exp (-(r * (y - L)) ^ 2 / 2) : ℂ)) :=
  integrable_normalized_zetaSum_gaussian_difference hr t

theorem sourceNormalizedGaussianError :
    ∃ L₀ : ℝ, 16 ≤ L₀ ∧ ∀ x t t₀ : ℝ, 1 < x → L₀ ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → ∀ a : ℝ, 0 < a → a ≤ 1 / 2 →
      ‖(Real.sqrt (2 * Real.pi * (a / Real.log x)) : ℂ) *
        (∫ y : ℝ, zetaSum (Real.exp y) (t - t₀) *
          (Real.exp ((a - 1) * y - (a / Real.log x) * y ^ 2 / 2) : ℂ)) -
        (2 * Real.pi : ℂ) * (Real.exp (a * Real.log x / 2) : ℂ) *
          (zetaSum (Real.exp (Real.log x)) (t - t₀) / (Real.exp (Real.log x) : ℂ))‖ ≤
      (Real.sqrt (2 * Real.pi) * dilationLipschitzConstant * gaussianMomentConstant) *
        Real.exp (a * Real.log x / 2) / (a * Real.log x) ^ (1 / 6 : ℝ) :=
  exists_maximizingTwist_source_gaussian_error


theorem inverseComparisonCannotShrink {x : ℝ} (hx : 0 < x) (a : ℝ) :
    1 ≤ ‖((a : ℂ) * Complex.I + 1) * (x : ℂ) ^ (-((a : ℂ) * Complex.I))‖ :=
  one_le_norm_inverse_comparisonFactor hx a

theorem actualLargeSumGaussianLower :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ t N : ℝ, 1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) →
        ‖zetaSum x t‖ = x / N →
        ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
          (∀ u : ℝ, |u| ≤ Real.log x →
            ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
          |t₀| ≤ c * N ∧ ∀ a : ℝ, c * N ^ (6 : ℕ) / Real.log x ≤ a → a ≤ 1 / 2 →
          (Real.pi / N) * Real.exp (a * Real.log x / 2) ≤
            ‖(Real.sqrt (2 * Real.pi * (a / Real.log x)) : ℂ) *
              (∫ y : ℝ, zetaSum (Real.exp y) (t - t₀) *
                (Real.exp ((a - 1) * y - (a / Real.log x) * y ^ 2 / 2) : ℂ))‖ :=
  exists_large_sum_gaussian_lower

theorem actualWeightedZeroForcing :
    ∃ c T₀ : ℝ, 0 < c ∧ 3 ≤ T₀ ∧
      ∀ T t x N : ℝ, T₀ ≤ T → T ≤ |t| → |t| ≤ 2 * T →
        Real.exp (Real.sqrt (Real.log T)) ≤ x → x ≤ Real.sqrt T →
        1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) → ‖zetaSum x t‖ = x / N →
        ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
          (∀ u : ℝ, |u| ≤ Real.log x →
            ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
          |t₀| ≤ c * N ∧ ∀ a : ℝ, c * N ^ (6 : ℕ) / Real.log x ≤ a → a ≤ 1 / 2 →
          ∃ η : ℝ, |η| ≤ 2 * a * Real.sqrt (Real.log T / Real.log x) ∧
            Summable (fun p : XiZero => a /
              ‖(((1 + a : ℝ) : ℂ) + ((t - t₀ + η : ℝ) : ℂ) * Complex.I) - xiZeroPoint p‖ ^ 2) ∧
            Real.log x / 4 ≤ ∑' p : XiZero, a /
              ‖(((1 + a : ℝ) : ℂ) + ((t - t₀ + η : ℝ) : ℂ) * Complex.I) - xiZeroPoint p‖ ^ 2 :=
  exists_large_sum_weighted_zero_forcing

theorem actualFrequencyIntegralLower :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ t N : ℝ, x ≤ |t| →
        1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) → ‖zetaSum x t‖ = x / N →
        ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
          (∀ u : ℝ, |u| ≤ Real.log x →
            ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
          |t₀| ≤ c * N ∧ ∀ a : ℝ, c * N ^ (6 : ℕ) / Real.log x ≤ a → a ≤ 1 / 2 →
          MeasureTheory.Integrable (fun ξ : ℝ =>
            (riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - (t - t₀) : ℝ) : ℂ) * Complex.I) /
              (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * Complex.I)) *
                (Real.exp (-ξ ^ 2 / (2 * (a / Real.log x))) : ℂ)) ∧
          (Real.pi / (2 * N)) * Real.exp (a * Real.log x / 2) ≤
            ‖∫ ξ : ℝ, (riemannZeta (((1 - a : ℝ) : ℂ) +
              ((ξ - (t - t₀) : ℝ) : ℂ) * Complex.I) /
                (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * Complex.I)) *
                  (Real.exp (-ξ ^ 2 / (2 * (a / Real.log x))) : ℂ)‖ :=
  exists_large_sum_gaussian_frequency_lower

theorem sourceFrequencyTailUniform {a L T : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hL : 0 < L) (hT : 1 ≤ T)
    {t ξ : ℝ} (ht : |t| ≤ 3 * T)
    (hξ : 2 * a * Real.sqrt (Real.log T / L) ≤ |ξ|) :
    ‖riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * Complex.I) /
      (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * Complex.I)‖ *
        Real.exp (-ξ ^ 2 / (4 * (a / L))) ≤ 120 / a :=
  source_gaussian_weighted_zeta_tail ha ha2 hL hT ht hξ

theorem sourceResidueHalfBound {a L N t : ℝ}
    (ha : 0 < a) (hL : 0 < L) (hN : 0 < N) (ht : 4 * N ≤ |t|) :
    ‖(2 * Real.pi : ℂ) / (1 + (t : ℂ) * Complex.I) *
      Complex.exp (((a : ℂ) + (t : ℂ) * Complex.I) ^ 2 / (2 * ((a / L : ℝ) : ℂ)))‖ ≤
      (Real.pi / (2 * N)) * Real.exp (a * L / 2) :=
  norm_source_gaussian_residue_half ha hL hN ht


theorem farDiskBoundaryIncluded {a l η φ : ℝ} (hl : 0 < l) (hla : l ≤ a)
    (hη : |η| ≤ a / 10) (p : XiZero)
    (hboundary : ‖(1 + (φ : ℂ) * Complex.I) - xiZeroPoint p‖ = 2 * a) :
    l / ‖(((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * Complex.I) - xiZeroPoint p‖ ^ 2 ≤
      (5 * l / a) *
        (1 / ((((1 + a : ℝ) : ℂ) + (φ : ℂ) * Complex.I) - xiZeroPoint p)).re :=
  source_far_kernel_le_real_resolvent hl hla hη p hboundary.ge

theorem linkedDiskMultiplicityTransfer {l Y Q η φ : ℝ}
    (hl : 0 < l) (hY : 0 < Y) (hYQ : Y ≤ Q / 2)
    (hη : |η| ≤ 2 * l * Real.sqrt (Q / Y))
    (hforce : Y / 4 ≤ ∑' p : XiZero,
      l / ‖(((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * Complex.I) - xiZeroPoint p‖ ^ 2)
    (hupper : (∑' p : XiZero,
      (1 / ((((1 + 20 * l * Q / Y : ℝ) : ℂ) + (φ : ℂ) * Complex.I) - xiZeroPoint p)).re) ≤
        5 * Q / 9) :
    l * Y / 9 ≤ (zeroCountIn (sourceZeroDisk φ (40 * l * Q / Y)) : ℝ) :=
  source_disk_count_of_weighted_forcing hl hY hYQ hη hforce hupper

theorem reciprocalOuterScale {l Y Q : ℝ} (hl : 0 < l) (hY : 0 < Y)
    (hYQ : Y ≤ Q / 2) (hlY : 1 ≤ l * Y) :
    1 / (20 * l * Q / Y) ≤ Q / 80 :=
  source_outer_shift_reciprocal hl hY hYQ hlY

theorem emptyScaleIntervalAllowed {c N Y : ℝ} (hempty : Y / 2 < c * N ^ (6 : ℕ)) :
    ¬ ∃ L : ℝ, c * N ^ (6 : ℕ) ≤ L ∧ L ≤ Y / 2 := by
  rintro ⟨L, hlo, hhi⟩
  linarith

theorem exactTheoremOneSourceContract :
    ∃ c T₀ : ℝ, 0 < c ∧ 3 ≤ T₀ ∧
      ∀ T t x N : ℝ, T₀ ≤ T → T ≤ |t| → |t| ≤ 2 * T →
        Real.exp (Real.sqrt (Real.log T)) ≤ x → x ≤ Real.sqrt T →
        1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) → ‖zetaSum x t‖ = x / N →
        ∃ φ : ℝ, |φ - t| ≤ c * N ∧
          ∀ L : ℝ, c * N ^ (6 : ℕ) ≤ L → L ≤ Real.log x / 2 →
            L / 360 ≤ (zeroCountIn
              (sourceZeroDisk φ (L * Real.log T / (Real.log x) ^ (2 : ℕ))) : ℝ) :=
  large_zeta_sum_forces_zero_disk

theorem deltaOnlyScaleThreshold (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
      c * Q ^ (3 / 50 : ℝ) ≤ δ * Q ^ (1 / 3 : ℝ) :=
  exists_local_window_scale_threshold c hδ

theorem smallRangeLocalWindowContract :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
      ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ T t ε : ℝ,
        T₀ ≤ T → T ≤ |t| → |t| ≤ 2 * T →
        (Real.log T) ^ (-1 / 3 : ℝ) < ε →
        (∀ u : ℝ, |u - t| ≤ C * (Real.log T) ^ (1 / 100 : ℝ) →
          (zeroCountIn (sourceZeroWindow u δ) : ℝ) ≤ δ * ε ^ 2 * Real.log T / 400) →
        ∀ x : ℝ, T ^ ε ≤ x → x ≤ Real.sqrt T →
          ‖zetaSum x t‖ ≤ x / (Real.log x) ^ (1 / 100 : ℝ) :=
  exists_small_range_local_zero_cancellation


theorem exactLargeCutoffSourceContract :
    ∃ K T₀ : ℝ, 0 < K ∧ 3 ≤ T₀ ∧ ∀ T t x : ℝ,
      T₀ ≤ T → T ≤ |t| → |t| ≤ 2 * T → Real.sqrt T ≤ x →
      ‖zetaSum x t‖ ≤ K * x * T ^ (-1 / 13 : ℝ) :=
  exists_large_x_zeta_sum_bound

theorem largeCutoffClosedJunction {T t : ℝ} (hT : 4096 ≤ T)
    (hlo : T ≤ |t|) (hhi : |t| ≤ 2 * T) :
    ‖zetaSum (Real.sqrt T) t‖ ≤ 3000 * Real.sqrt T * T ^ (-1 / 13 : ℝ) :=
  large_x_zeta_sum_bound hT hlo hhi le_rfl

theorem largeCutoffNegativeHeight {T t x : ℝ} (hT : 4096 ≤ T)
    (hlo : T ≤ |t|) (hhi : |t| ≤ 2 * T) (hx : Real.sqrt T ≤ x) :
    ‖zetaSum x (-t)‖ ≤ 3000 * x * T ^ (-1 / 13 : ℝ) := by
  rw [norm_zetaSum_neg]
  exact large_x_zeta_sum_bound hT hlo hhi hx

theorem actualTerminalPrefixBound {Z : ℝ} (hZ : 2 ≤ Z)
    (A N : ℕ) (hA : 0 < A) (hNA : N ≤ A) :
    ‖zetaSum ((A + N : ℕ) : ℝ) (-(Z ^ (12 : ℕ))) -
      zetaSum (A : ℝ) (-(Z ^ (12 : ℕ)))‖ ≤
        120 * (Z ^ (2 : ℕ) * Real.sqrt A + (A : ℝ) / Z) := by
  rw [zetaSum_nat_increment_logarithmic]
  exact source_logarithmic_prefix_uniform hZ A N hA hNA

theorem exactTheoremTwoSourceContract :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A →
      ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ T t ε : ℝ,
          T₀ ≤ T → T ≤ |t| → |t| ≤ 2 * T →
          (Real.log T) ^ (-1 / 3 : ℝ) < ε →
          (∀ u : ℝ, |u - t| ≤ C * (Real.log T) ^ (1 / 100 : ℝ) →
            (zeroCountIn (sourceZeroWindow u δ) : ℝ) ≤ δ * ε ^ 2 * Real.log T / 400) →
          ∀ x : ℝ, T ^ ε ≤ x → x ≤ T ^ A →
            ‖zetaSum x t‖ ≤ K * x / (Real.log x) ^ (1 / 100 : ℝ) :=
  local_zero_windows_force_zeta_sum_cancellation

theorem theoremTwoClosedQuarter :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A →
      ∃ K T₀ : ℝ, 0 < K ∧ 3 ≤ T₀ ∧ ∀ T t ε : ℝ,
        T₀ ≤ T → T ≤ |t| → |t| ≤ 2 * T →
        (Real.log T) ^ (-1 / 3 : ℝ) < ε →
        (∀ u : ℝ, |u - t| ≤ C * (Real.log T) ^ (1 / 100 : ℝ) →
          (zeroCountIn (sourceZeroWindow u (1 / 4)) : ℝ) ≤
            (1 / 4 : ℝ) * ε ^ 2 * Real.log T / 400) →
        ∀ x : ℝ, T ^ ε ≤ x → x ≤ T ^ A →
          ‖zetaSum x t‖ ≤ K * x / (Real.log x) ^ (1 / 100 : ℝ) := by
  obtain ⟨C, hC, h⟩ := local_zero_windows_force_zeta_sum_cancellation
  refine ⟨C, hC, ?_⟩
  intro A hA
  obtain ⟨K, hK, hδ⟩ := h A hA
  obtain ⟨T₀, hT₀, hresult⟩ := hδ (1 / 4) (by norm_num) le_rfl
  exact ⟨K, T₀, hK, hT₀, hresult⟩


end DongWangWangZhang2026.SemanticRegression
