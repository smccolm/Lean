import DhimanKadiriQuesadaHerrera2026

/-! Exact unfolded source contracts and retained diagnostics for the implemented scope. -/

namespace DhimanKadiriQuesadaHerrera2026.SemanticRegression

open scoped BigOperators

/-- Preserve the actual positive-integer interval and the omitted unit term. -/
theorem actual_sum_index_discrepancy (s : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-s)) =
      1 + ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, (n : ℂ) ^ (-s) :=
  sharpZetaSum_eq_one_add_printed s hx

/-- Preserve both actual zeta residuals and the quantitative obstruction. -/
theorem actual_residual_discrepancy (s : ℂ) {x a b : ℝ} (hx : 1 ≤ x)
    (ha : ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-s)‖ ≤ a)
    (hb : ‖riemannZeta s - ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, (n : ℂ) ^ (-s)‖ ≤ b) :
    1 ≤ a + b :=
  one_le_sum_of_afe1_residual_bounds s hx ha hb

/-- The false orientation fails for the precise chi formula of equation (2.16). -/
theorem literal_functional_equation_counterexample :
    riemannZeta (1 - (-2 : ℂ)) ≠
      ((2 : ℂ) ^ (-2 : ℂ) * (Real.pi : ℂ) ^ ((-2 : ℂ) - 1) *
        Complex.Gamma (1 - (-2 : ℂ)) * Complex.sin ((Real.pi : ℂ) * (-2) / 2)) *
        riemannZeta (-2) :=
  printed_functional_equation_fails_at_neg_two

/-- The counterexample uses smooth positive decreasing weights and a decreasing positive slope. -/
theorem poisson_counterexample_hypotheses :
    ContDiff ℝ 2 PoissonCounterexample.weight ∧ ContDiff ℝ 2 PoissonCounterexample.phase ∧
      StrictAntiOn PoissonCounterexample.weight (Set.Icc (1 / 2 : ℝ) (3 / 2)) ∧
      StrictAntiOn (deriv PoissonCounterexample.phase) (Set.Icc (1 / 2 : ℝ) (3 / 2)) ∧
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2),
        0 < PoissonCounterexample.weight x ∧ 0 < deriv PoissonCounterexample.phase x) ∧
      deriv PoissonCounterexample.weight (1 / 2) = 0 ∧
      deriv PoissonCounterexample.phase (1 / 2) = 1 / 10000 :=
  PoissonCounterexample.printed_hypotheses

/-- The precise retained integer sum and Fourier integral violate the printed error expression. -/
theorem poisson_counterexample_source_inequality :
    ¬ ‖PoissonCounterexample.sourceSum - PoissonCounterexample.sourceMain‖ ≤
      PoissonCounterexample.sourceError :=
  PoissonCounterexample.not_source_partI_inequality

/-- The added monotonicity assumptions are derived for the actual power and logarithmic functions. -/
theorem actual_afe_repair_hypotheses {sigma c : ℝ} (hsigma : 0 ≤ sigma) (hc : 0 ≤ c) :
    AntitoneOn (fun x => |deriv (fun u : ℝ => u ^ (-sigma)) x|) (Set.Ioi 0) ∧
      AntitoneOn (fun x => |deriv (fun u : ℝ => u ^ (-sigma)) x| /
        (1 + deriv (fun u : ℝ => c * Real.log u) x)) (Set.Ioi 0) :=
  afe_weights_satisfy_accepted_partI_hypotheses hsigma hc

/-- Lemma 1's two-sided first estimate with the literal natural-number tail. -/
theorem lemma_one_first_tail {N : ℕ} {y : ℝ} (hy : 0 < y) (hNy : y < (N : ℝ) + 1) :
    let S := ∑' ν : ℕ, if N < ν then 1 / ((ν : ℝ) * ((ν : ℝ) - y) ^ 1) else 0;
    -1 / (y * ((N : ℝ) + 1)) - (Complex.digamma ((N : ℝ) + 1 - y : ℝ)).re / y ≤
        S - Real.log ((N : ℝ) + 1) / y ∧
      S - Real.log ((N : ℝ) + 1) / y ≤ -1 / (2 * y * ((N : ℝ) + 1)) -
        (Complex.digamma ((N : ℝ) + 1 - y : ℝ)).re / y := by
  dsimp only
  rw [source_harmonic_tail_power_eq hy hNy (Or.inl rfl)]
  simpa only [pow_one] using harmonic_tail_bounds hy hNy

/-- Lemma 1's second negative-shift estimate, including its exact delta. -/
theorem lemma_one_second_tail {N : ℕ} {y : ℝ} (hy : 0 < y) (hNy : y < (N : ℝ) + 1) :
    let δ : ℝ := (N : ℝ) + 1 - y
    (∑' ν : ℕ, if N < ν then 1 / ((ν : ℝ) * ((ν : ℝ) - y) ^ 2) else 0) ≤
      (1 / δ ^ 2 + 1 / (δ + 1) ^ 2 + 1 / (δ + 1)) / y -
        (Real.log ((N : ℝ) + 1) - 1 / ((N : ℝ) + 1) -
          (Complex.digamma (δ : ℂ)).re) / y ^ 2 := by
  dsimp only
  rw [source_harmonic_tail_power_eq hy hNy (Or.inr (Or.inl rfl))]
  exact harmonic_tail_square_bound hy hNy

/-- Lemma 1's third negative-shift estimate with all three correction terms. -/
theorem lemma_one_third_tail {N : ℕ} {y : ℝ} (hy : 0 < y) (hNy : y < (N : ℝ) + 1) :
    let δ : ℝ := (N : ℝ) + 1 - y
    (∑' ν : ℕ, if N < ν then 1 / ((ν : ℝ) * ((ν : ℝ) - y) ^ 3) else 0) ≤
      (1 / δ ^ 3 + 1 / (δ + 1) ^ 3 + 1 / (2 * (δ + 1) ^ 2)) / y -
        (1 / δ ^ 2 + 1 / (δ + 1)) / y ^ 2 +
        (Real.log ((N : ℝ) + 1) - 1 / (2 * ((N : ℝ) + 1)) -
          (Complex.digamma (δ : ℂ)).re) / y ^ 3 := by
  dsimp only
  rw [source_harmonic_tail_power_eq hy hNy (Or.inr (Or.inr rfl))]
  exact harmonic_tail_cube_bound hy hNy

/-- The first positive-shift estimate uses the actual positive-index series. -/
theorem lemma_one_first_plus {y : ℝ} (hy : 0 < y) :
    (∑' ν : ℕ, if 0 < ν then 1 / ((ν : ℝ) * ((ν : ℝ) + y) ^ 1) else 0) ≤
      (Real.log (y + 1) + Real.eulerMascheroniConstant) / y -
        1 / (2 * y * (y + 1)) := by
  rw [source_harmonic_plus_power_eq hy (Or.inl rfl)]
  simpa only [pow_one] using harmonic_plus_bound hy

/-- The second positive-shift estimate preserves the source polynomial q₂. -/
theorem lemma_one_second_plus {y : ℝ} (hy : 0 < y) :
    (∑' ν : ℕ, if 0 < ν then 1 / ((ν : ℝ) * ((ν : ℝ) + y) ^ 2) else 0) ≤
      (Real.log (y + 1) + Real.eulerMascheroniConstant) / y ^ 2 -
        (1 + 2 * y) / (2 * y ^ 2 * (y + 1)) := by
  rw [source_harmonic_plus_power_eq hy (Or.inr (Or.inl rfl))]
  exact harmonic_plus_square_bound hy

/-- The third positive-shift estimate preserves the source polynomial q₃. -/
theorem lemma_one_third_plus {y : ℝ} (hy : 0 < y) :
    (∑' ν : ℕ, if 0 < ν then 1 / ((ν : ℝ) * ((ν : ℝ) + y) ^ 3) else 0) ≤
      (Real.log (y + 1) + Real.eulerMascheroniConstant) / y ^ 3 -
        (1 + 3 * y + 3 * y ^ 2) / (2 * y ^ 3 * (y + 1) ^ 2) := by
  rw [source_harmonic_plus_power_eq hy (Or.inr (Or.inr rfl))]
  exact harmonic_plus_cube_bound hy

/-- Appendix Lemma 11's negative-shift bound with its literal sign and tail. -/
theorem lemma_eleven_negative {N : ℕ} {y : ℝ} (hy : 0 < y) (hNy : y < (N : ℝ) + 1) :
    let δ : ℝ := (N : ℝ) + 1 - y
    |∑' ν : ℕ, if N < ν then (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) - y)) else 0| ≤
      |(Complex.digamma (δ : ℂ)).re -
        (Complex.digamma ((δ + 1) / 2 : ℝ)).re - Real.log 2| / y +
        1 / (y * ((N : ℝ) + 1)) :=
  source_alternating_harmonic_tail_bound hy hNy

/-- Appendix Lemma 11's positive-shift bound with the printed coefficient three halves. -/
theorem lemma_eleven_positive {y : ℝ} (hy : 0 < y) :
    |∑' ν : ℕ, if 0 < ν then (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) + y)) else 0| ≤
      Real.log 2 / y + 3 / (2 * y * (y + 1)) :=
  source_alternating_harmonic_plus_bound hy

/-- The corrected intermediate identity retains the omitted logarithmic term. -/
theorem corrected_alternating_identity {y : ℝ} (hy : 0 < y) :
    (∑' ν : ℕ, if 0 < ν then (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) + y)) else 0) =
      ((Complex.digamma (y + 1 : ℝ)).re -
        (Complex.digamma ((y + 1) / 2 : ℝ)).re - 2 * Real.log 2) / y :=
  source_alternating_harmonic_plus_identity hy

/-- The digamma convention is the actual real Gamma logarithmic derivative. -/
theorem actual_real_gamma_log_derivative {x : ℝ} (hx : 0 < x) :
    (Complex.digamma (x : ℂ)).re = deriv Real.Gamma x / Real.Gamma x :=
  real_digamma_eq_deriv_Gamma_div hx

/-- Lemma 2 uses the actual negative Fourier modes and the integer floor. -/
theorem lemma_two_geometric_identity {x y : ℝ}
    (hx : ∀ k : ℤ, x ≠ (k : ℝ)) (hy : 0 < y) :
    ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      Complex.exp (Complex.I * ((-2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ))‖ =
        |Real.sin (Real.pi * x * (⌊y⌋ : ℤ))| / |Real.sin (Real.pi * x)| :=
  norm_finiteS0_source_floor hx hy

/-- Lemma 2's geometric bound retains both real-cutoff branches. -/
theorem lemma_two_geometric_bound {x y : ℝ} (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      Complex.exp (Complex.I * ((-2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ))‖ ≤
        if 1 ≤ y then 1 / |Real.sin (Real.pi * x)| else 0 :=
  norm_finiteS0_le_source hx

/-- The complete tilde-S₁ majorant bounds the actual divided Fourier sum. -/
theorem lemma_two_harmonic_bound {x y : ℝ} (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      Complex.exp (Complex.I * ((-2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ)) / (n : ℂ)‖ ≤
        if 1 ≤ y then (1 / |Real.sin (Real.pi * x)|) * (1 / y + 1) else 0 :=
  norm_finiteS1_le_tildeS1 hx

/-- The half-integer O-star claim is checked as a two-sided norm error. -/
theorem lemma_two_half_integer_error (k : ℤ) {y : ℝ} (hy : 1 ≤ y) :
    |‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      Complex.exp (Complex.I * ((-2 * Real.pi * (n : ℝ) * ((k : ℝ) + 1 / 2) : ℝ) : ℂ)) /
        (n : ℂ)‖ - Real.log 2| ≤ 1 / y :=
  finiteS1_half_integer_error k hy

/-- The deterministic upper endpoint of the half-integer O-star bound. -/
theorem lemma_two_half_integer_bound (k : ℤ) {y : ℝ} (hy : 1 ≤ y) :
    ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      Complex.exp (Complex.I * ((-2 * Real.pi * (n : ℝ) * ((k : ℝ) + 1 / 2) : ℝ) : ℂ)) /
        (n : ℂ)‖ ≤ Real.log 2 + 1 / y :=
  norm_finiteS1_half_integer_le k hy

/-- Integer frequencies are handled by the actual finite count and harmonic number. -/
theorem lemma_two_integer_cases (k : ℤ) (y : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      Complex.exp (Complex.I * ((-2 * Real.pi * (n : ℝ) * (k : ℝ) : ℝ) : ℂ))) =
        (⌊y⌋₊ : ℂ) ∧
    (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      Complex.exp (Complex.I * ((-2 * Real.pi * (n : ℝ) * (k : ℝ) : ℝ) : ℂ)) / (n : ℂ)) =
        (harmonic ⌊y⌋₊ : ℂ) :=
  ⟨finiteS0_integer k y, finiteS1_integer k y⟩

/-- Lemma 3's literal negative-tail sum and complete generic Z₀ expression. -/
theorem lemma_three_negative {N : ℕ} {x y : ℝ} (hy : 1 ≤ y)
    (hNy : y < (N : ℝ) + 1) (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    ‖∑' ν : ℕ, if N < ν then
      Complex.exp (Complex.I * ((-2 * Real.pi * (ν : ℝ) * x : ℝ) : ℂ)) /
        (((ν : ℝ) * ((ν : ℝ) - y) : ℝ) : ℂ) else 0‖ ≤
      (1 / (y * |Real.sin (Real.pi * x)|)) *
        (1 / ((N : ℝ) + 1 - y) + 1 / ((N : ℝ) + 1)) :=
  norm_negativeTail_le_source (by linarith) hNy hx

/-- Lemma 3's literal positive-tail sum and complete generic Z₁ expression. -/
theorem lemma_three_positive {x y : ℝ} (hy : 1 ≤ y) (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    ‖∑' ν : ℕ, if 0 < ν then
      Complex.exp (Complex.I * ((-2 * Real.pi * (ν : ℝ) * x : ℝ) : ℂ)) /
        (((ν : ℝ) * ((ν : ℝ) + y) : ℝ) : ℂ) else 0‖ ≤
      (1 / (y * |Real.sin (Real.pi * x)|)) * (1 + 1 / (1 + y)) :=
  norm_positiveTail_le_source (by linarith) hx

/-- Lemma 3's refined negative half-integer tail with its source delta. -/
theorem lemma_three_half_integer_negative {N : ℕ} (k : ℤ) {y : ℝ} (hy : 1 ≤ y)
    (hδ : 1 / 2 ≤ (N : ℝ) + 1 - y) :
    let δ : ℝ := (N : ℝ) + 1 - y
    ‖∑' ν : ℕ, if N < ν then
      Complex.exp (Complex.I * ((-2 * Real.pi * (ν : ℝ) * ((k : ℝ) + 1 / 2) : ℝ) : ℂ)) /
        (((ν : ℝ) * ((ν : ℝ) - y) : ℝ) : ℂ) else 0‖ ≤
      |(Complex.digamma (δ : ℂ)).re -
        (Complex.digamma ((δ + 1) / 2 : ℝ)).re - Real.log 2| / y + 1 / (y * ((N : ℝ) + 1)) :=
  norm_negativeTail_half_integer_le k (by linarith) (by linarith)

/-- The second inequality between the source's half-integer majorants. -/
theorem lemma_three_half_integer_majorant {N : ℕ} {y : ℝ} (hy : 1 ≤ y)
    (hδ : 1 / 2 ≤ (N : ℝ) + 1 - y) :
    let δ : ℝ := (N : ℝ) + 1 - y
    |(Complex.digamma (δ : ℂ)).re -
        (Complex.digamma ((δ + 1) / 2 : ℝ)).re - Real.log 2| / y + 1 / (y * ((N : ℝ) + 1)) ≤
      (1 / y) * (Real.pi / 2 + 1 / ((N : ℝ) + 1)) := by
  have h := add_le_add_left
    (div_le_div_of_nonneg_right (digamma_half_integer_tail_bound hδ) (by linarith : 0 ≤ y))
    (1 / (y * ((N : ℝ) + 1)))
  convert h using 1
  have hy' : 0 < y := by linarith
  field_simp

/-- Lemma 3's refined positive half-integer bound has the unchanged coefficient three halves. -/
theorem lemma_three_half_integer_positive (k : ℤ) {y : ℝ} (hy : 1 ≤ y) :
    ‖∑' ν : ℕ, if 0 < ν then
      Complex.exp (Complex.I * ((-2 * Real.pi * (ν : ℝ) * ((k : ℝ) + 1 / 2) : ℝ) : ℂ)) /
        (((ν : ℝ) * ((ν : ℝ) + y) : ℝ) : ℂ) else 0‖ ≤
      Real.log 2 / y + 3 / (2 * y * (y + 1)) :=
  norm_positiveTail_half_integer_le k (by linarith)

/-- The negative-tail source sum is absolutely convergent on the declared domain. -/
theorem lemma_three_negative_convergence {N : ℕ} {y : ℝ} (hy : 1 ≤ y)
    (hNy : y < (N : ℝ) + 1) (x : ℝ) :
    Summable (fun ν : ℕ => if N < ν then
      Complex.exp (Complex.I * ((-2 * Real.pi * (ν : ℝ) * x : ℝ) : ℂ)) /
        (((ν : ℝ) * ((ν : ℝ) - y) : ℝ) : ℂ) else 0) :=
  summable_negativeTail (by linarith) hNy x

/-- The positive-tail source sum is absolutely convergent. -/
theorem lemma_three_positive_convergence {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    Summable (fun ν : ℕ => if 0 < ν then
      Complex.exp (Complex.I * ((-2 * Real.pi * (ν : ℝ) * x : ℝ) : ℂ)) /
        (((ν : ℝ) * ((ν : ℝ) + y) : ℝ) : ℂ) else 0) :=
  summable_positiveTail (by linarith) x

/-- The Poisson amplitude really is the derivative of the actual weighted exponential. -/
theorem actual_weighted_wave_derivative {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun u => (g u : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f u : ℂ))) x =
      (((deriv g x : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (g x : ℂ) * ((deriv f x : ℝ) : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (f x : ℂ)) :=
  (weighted_wave_hasDerivAt hf hg).deriv

/-- The first complete derivative-amplitude tail bound uses the accepted absolute monotonicity. -/
theorem partI_negative_frequency_integral {a b ν : ℝ} (hab : a < b) (f g : ℝ → ℝ)
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hfp : ∀ x ∈ Set.Icc a b, 0 ≤ deriv f x)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hgc : ContinuousOn g (Set.Icc a b)) (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ x ∈ Set.Icc a b, 0 ≤ g x) (hga : AntitoneOn g (Set.Icc a b))
    (hgda : AntitoneOn (fun x => |deriv g x|) (Set.Icc a b)) (hν : deriv f a < ν) :
    ‖∫ x in a..b, (((deriv g x : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((g x * deriv f x : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((f x - ν * x : ℝ) : ℂ))‖ ≤
        (|deriv g a| + 2 * Real.pi * g a * deriv f a) / (Real.pi * (ν - deriv f a)) :=
  negative_derivative_amplitude_integral_bound hab f g hfd hfc hfp hfa hgc hgdc hgp hga hgda hν

/-- The second complete derivative-amplitude tail bound uses the accepted quotient monotonicity. -/
theorem partI_positive_frequency_integral {a b ν : ℝ} (hab : a < b) (f g : ℝ → ℝ)
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hfp : ∀ x ∈ Set.Icc a b, 0 ≤ deriv f x)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hgc : ContinuousOn g (Set.Icc a b)) (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ x ∈ Set.Icc a b, 0 ≤ g x) (hga : AntitoneOn g (Set.Icc a b))
    (hgdq : AntitoneOn (fun x => |deriv g x| / (1 + deriv f x)) (Set.Icc a b)) (hν : 1 ≤ ν) :
    ‖∫ x in a..b, (((deriv g x : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((g x * deriv f x : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((f x + ν * x : ℝ) : ℂ))‖ ≤
        (|deriv g a| + 2 * Real.pi * g a * deriv f a) / (Real.pi * (ν + deriv f a)) :=
  positive_derivative_amplitude_integral_bound hab f g hfd hfc hfp hfa hgc hgdc hgp hga hgdq hν


/-- Exact source-object consumer for the repaired N = 0 theorem with general endpoints. -/
theorem partI_zero_source {f g : ℝ → ℝ} {a b : ℝ} (h : PartIRegularity f g a b) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
        (g (n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊,
        ∫ x in a..b, (g x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      ((|deriv g a| + 2 * Real.pi * g a * deriv f a) / (2 * Real.pi ^ 2) / deriv f a) *
        (Real.log (1 + deriv f a) + Real.eulerMascheroniConstant +
          Real.log ((⌊deriv f a⌋₊ : ℝ) + 1) -
          (Complex.digamma ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a : ℝ)).re -
          1 / (2 * ((⌊deriv f a⌋₊ : ℝ) + 1)) - 1 / (2 * (1 + deriv f a))) +
      (g b * poissonEndpointMajorant b (deriv f a) +
        g a * poissonEndpointMajorant a (deriv f a)) / (2 * Real.pi) +
      ‖(g a : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f a : ℂ)) *
        ((Int.fract a - 1 / 2 : ℝ) : ℂ) -
        (g b : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f b : ℂ)) *
          ((Int.fract b - 1 / 2 : ℝ) : ℂ)‖ := by
  simpa only [poissonMain_eq_source, weightedWave, partIZeroError, partIAnalyticError,
    partICoefficient, poissonBoundary] using corrected_poisson_partI_zero h

/-- Exact source-object consumer for the half-integer N = 0 constant and vanishing G term. -/
theorem partI_zero_half_integer_source {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b)
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
        (g (n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊,
        ∫ x in a..b, (g x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      ((|deriv g a| + 2 * Real.pi * g a * deriv f a) / (2 * Real.pi ^ 2) / deriv f a) *
        (Real.log (1 + deriv f a) + Real.eulerMascheroniConstant +
          Real.log ((⌊deriv f a⌋₊ : ℝ) + 1) -
          (Complex.digamma ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a : ℝ)).re -
          1 / (2 * ((⌊deriv f a⌋₊ : ℝ) + 1)) - 1 / (2 * (1 + deriv f a))) +
      (g a + g b) / (2 * Real.pi) * (Real.log 2 + 1 / deriv f a) := by
  simpa only [poissonMain_eq_source, weightedWave, partIAnalyticError, partICoefficient] using
    corrected_poisson_partI_zero_half_integer h ha hb


/-- General-N source sum, exact frequency range and every fully shifted error term. -/
theorem partI_general_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
        (g (n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ x in a..b, (g x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      (|deriv g a| + 2 * Real.pi * g a * (deriv f a - N)) /
        (2 * Real.pi ^ 2 * (deriv f a - N)) *
        (Real.log (1 + (deriv f a - N)) + Real.eulerMascheroniConstant +
          Real.log (((⌊deriv f a⌋₊ - N : ℕ) : ℝ) + 1) -
          (Complex.digamma ((1 - Int.fract (deriv f a) : ℝ) : ℂ)).re -
          1 / (2 * (((⌊deriv f a⌋₊ - N : ℕ) : ℝ) + 1)) - 1 / (2 * (1 + (deriv f a - N)))) +
      (g b * poissonEndpointMajorant b (deriv f a - N) +
        g a * poissonEndpointMajorant a (deriv f a - N)) / (2 * Real.pi) +
      ‖(g a : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((f a - N * a : ℝ) : ℂ)) *
        ((Int.fract a - 1 / 2 : ℝ) : ℂ) -
        (g b : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((f b - N * b : ℝ) : ℂ)) *
          ((Int.fract b - 1 / 2 : ℝ) : ℂ)‖ := by
  simpa only [weightedWave, partIError, partIShiftAnalyticError, poissonBoundary, phaseShift] using
    corrected_poisson_partI h

/-- General-N half-integer source specialization with invariant δ and exact log(2) coefficient. -/
theorem partI_general_half_integer_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N)
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
        (g (n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ x in a..b, (g x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      (|deriv g a| + 2 * Real.pi * g a * (deriv f a - N)) /
        (2 * Real.pi ^ 2 * (deriv f a - N)) *
        (Real.log (1 + (deriv f a - N)) + Real.eulerMascheroniConstant +
          Real.log (((⌊deriv f a⌋₊ - N : ℕ) : ℝ) + 1) -
          (Complex.digamma ((1 - Int.fract (deriv f a) : ℝ) : ℂ)).re -
          1 / (2 * (((⌊deriv f a⌋₊ - N : ℕ) : ℝ) + 1)) - 1 / (2 * (1 + (deriv f a - N)))) +
      (g a + g b) / (2 * Real.pi) * (Real.log 2 + 1 / (deriv f a - N)) := by
  simpa only [weightedWave, partIShiftAnalyticError] using corrected_poisson_partI_half_integer h ha hb

/-- The actual unweighted first Corollary-0.1 bound, with every displayed correction. -/
theorem corollary_zero_one_partI_source {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hfp : ∀ x ∈ Set.Icc a b, 0 < deriv f x) (hfa : StrictAntiOn (deriv f) (Set.Icc a b))
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊,
        ∫ x in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      (1 / Real.pi) * (Real.log (1 + deriv f a) + Real.log (1 + (⌊deriv f a⌋₊ : ℝ)) +
        Real.eulerMascheroniConstant - 1 / (2 * (1 + (⌊deriv f a⌋₊ : ℝ))) -
        1 / (2 * (1 + deriv f a)) - (Complex.digamma ((1 - Int.fract (deriv f a) : ℝ) : ℂ)).re +
        Real.log 2 + 1 / deriv f a) :=
  corollary_poisson_partI hab hfd hfc hfp hfa ha hb

/-- Theorem 9's exact corrected source statement, with the real Gamma derivative and unit term. -/
theorem theorem_nine_source {sigma t t₀ c : ℝ} (hsigma : sigma ∈ Set.Ioc 0 1)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hc : 1 / (2 * Real.pi) < c)
    (hhalf : ∃ k : ℤ, c * t = (k : ℝ) + 1 / 2) :
    ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) -
      ∑ n ∈ Finset.Icc 1 ⌊c * t⌋₊, (n : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      (c + (1 / Real.pi) * (1 / t₀ + 1) *
        (Real.log (1 + 1 / (2 * Real.pi * c)) + Real.eulerMascheroniConstant -
          deriv Real.Gamma (1 - 1 / (2 * Real.pi * c)) /
            Real.Gamma (1 - 1 / (2 * Real.pi * c)) -
          1 / (2 * (1 + 1 / (2 * Real.pi * c))) - 1 / 2)) * (c * t) ^ (-sigma) := by
  have h := afe_first_kind hsigma ht₀ ht hc hhalf
  rw [afeFirstConstant_eq_source hc] at h
  simpa only [sharpZetaSum, zetaTerm] using h

/-- The permitted cutoff ct=1/2 retains exactly the same m(c), with an empty sharp sum. -/
theorem theorem_nine_small_cutoff_source {sigma t t₀ c : ℝ} (hsigma : sigma ∈ Set.Ioc 0 1)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hc : 1 / (2 * Real.pi) < c) (hcut : c * t = 1 / 2) :
    ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (c + (1 / Real.pi) * (1 / t₀ + 1) *
        (Real.log (1 + 1 / (2 * Real.pi * c)) + Real.eulerMascheroniConstant -
          deriv Real.Gamma (1 - 1 / (2 * Real.pi * c)) /
            Real.Gamma (1 - 1 / (2 * Real.pi * c)) -
          1 / (2 * (1 + 1 / (2 * Real.pi * c))) - 1 / 2)) * (1 / 2 : ℝ) ^ (-sigma) := by
  have h := afe_first_kind_small_cutoff hsigma ht₀ ht hc hcut
  rwa [afeFirstConstant_eq_source hc] at h

/-- The actual real-cutoff corollary with source integer floor and exact Gamma-based c₀.
The two advertised decimal instances are verified by the following separate consumers. -/
theorem corollary_zero_three_source {sigma t t₀ : ℝ} (hsigma : sigma ∈ Set.Ioc 0 1)
    (ht₀ : 14 ≤ t₀) (ht : t₀ ≤ t) :
    let N : ℝ := (⌊t₀⌋ : ℤ)
    let m : ℝ → ℝ := fun c => c + (1 / Real.pi) * (1 / t₀ + 1) *
      (Real.log (1 + 1 / (2 * Real.pi * c)) + Real.eulerMascheroniConstant -
        deriv Real.Gamma (1 - 1 / (2 * Real.pi * c)) /
          Real.Gamma (1 - 1 / (2 * Real.pi * c)) -
        1 / (2 * (1 + 1 / (2 * Real.pi * c))) - 1 / 2)
    ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) -
      ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (n : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      max (max (m ((N + 1 / 2) / t₀)) (m ((N + 3 / 2) / (N + 1))))
        (m (1 - 1 / (2 * (N + 1))) / (1 - 1 / (2 * (N + 1)))) * t ^ (-sigma) := by
  have h := afe_first_kind_real_cutoff hsigma ht₀ ht
  rw [afeFirstRealConstant_eq_source ht₀] at h
  simpa only [sharpZetaSum, zetaTerm, natCast_floor_eq_intCast_floor (by linarith : 0 ≤ t₀)] using h

/-- The smaller advertised first threshold 14.13472, with the exact decimal constant and real cutoff. -/
theorem corollary_zero_three_small_decimal {sigma t : ℝ} (hsigma : sigma ∈ Set.Ioc 0 1)
    (ht : 14.13472 ≤ t) :
    ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) -
      ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (n : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      1.2552 * t ^ (-sigma) := by
  simpa only [sharpZetaSum, zetaTerm] using afe_first_kind_small_decimal hsigma ht

/-- The 3·10¹² threshold is a numerical parameter; no assertion about zeros is assumed. -/
theorem corollary_zero_three_large_decimal {sigma t : ℝ} (hsigma : sigma ∈ Set.Ioc 0 1)
    (ht : 3 * 10 ^ 12 ≤ t) :
    ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) -
      ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (n : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      1.2127 * t ^ (-sigma) := by
  norm_num at ht
  simpa only [sharpZetaSum, zetaTerm] using afe_first_kind_large_decimal hsigma ht


/-- The valid orientation uses precisely the frozen source chi product. -/
theorem corrected_functional_equation_source {s : ℂ} (hs : s.im ≠ 0) :
    riemannZeta s = ((2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
      Complex.sin ((Real.pi : ℂ) * s / 2)) * riemannZeta (1 - s) :=
  zeta_eq_chi_mul_zeta_one_sub hs

/-- Reflection consumes the actual two polynomials, with exchanged physical cutoffs. -/
theorem actual_remainder_reflection {s : ℂ} (hs : s.im ≠ 0) (x y : ℝ) :
    let X : ℂ → ℂ := fun z => (2 : ℂ) ^ z * (Real.pi : ℂ) ^ (z - 1) *
      Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z / 2)
    (riemannZeta s - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-s)) -
      X s * (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (n : ℂ) ^ (-(1 - s)))) =
    X s * (riemannZeta (1 - s) -
      (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (n : ℂ) ^ (-(1 - s))) -
      X (1 - s) * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-s))) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, chi, sub_sub_cancel] using
    afeRemainder_reflection hs x y

/-- Both height signs preserve the norm of the actual AFE remainder. -/
theorem actual_remainder_conjugation {σ t : ℝ} (ht : t ≠ 0) (x y : ℝ) :
    let E : ℂ → ℂ := fun s => riemannZeta s -
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-s)) -
      ((2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
        Complex.sin ((Real.pi : ℂ) * s / 2)) *
      (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (n : ℂ) ^ (-(1 - s)))
    ‖E ((σ : ℂ) - (t : ℂ) * Complex.I)‖ =
      ‖E ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
  norm_afeRemainder_neg_height ht x y

/-- The literal Lemma-7 signed exponential is valid on its full printed domain.
The proof establishes the stronger result for every real part. -/
theorem lemma_seven_source {σ t t₀ : ℝ} (_hσ : σ ∈ Set.Icc 0 1)
    (ht₀ : 1 / Real.pi ≤ t₀) (ht : t₀ ≤ |t|) :
    let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    ∃ ε : ℂ, Complex.Gamma (1 - s) * (2 * (Real.pi : ℂ) / Complex.I) ^ (s - 1) =
      ((2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
        Complex.sin ((Real.pi : ℂ) * s / 2)) * (1 + ε) ∧
      ‖ε‖ ≤ Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀)) := by
  have hp : 0 < t₀ := lt_of_lt_of_le (by positivity) ht₀
  have hi : (((σ : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
  simpa only [chi, hi] using gamma_factor_lemma_seven (s :=
    (σ : ℂ) + (t : ℂ) * Complex.I) hp (by simpa only [hi] using ht)

/-- The conjugate negative-height factor has a decaying error with the required opposite branch. -/
theorem lemma_seven_negative_height {σ t t₀ : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ -t) :
    let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    ∃ ε : ℂ, Complex.Gamma (1 - s) * (2 * (Real.pi : ℂ) / (-Complex.I)) ^ (s - 1) =
      ((2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
        Complex.sin ((Real.pi : ℂ) * s / 2)) * (1 + ε) ∧
      ‖ε‖ ≤ Real.exp (-Real.pi * |t|) / (1 - Real.exp (-Real.pi * t₀)) := by
  have hi : (((σ : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
  simpa only [chi, hi] using gamma_factor_conjugate_branch (s :=
    (σ : ℂ) + (t : ℂ) * Complex.I) ht₀ (by simpa only [hi] using ht)

/-- Lemma 6 with the actual chi product and every printed constant unfolded.
Both height signs and both sigma endpoints remain in the public contract. -/
theorem lemma_six_source {σ t t₀ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (ht₀ : 1 / Real.pi ≤ t₀) (ht : t₀ ≤ |t|) :
    let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    let C₁ : ℝ := (1 - σ) ^ 2 * (1 / 2 + 2 / Real.pi) +
      (1 - σ) * (σ - 1 / 2) * ((Real.pi / 2) ^ 2 + (1 - σ) / (2 * t₀))
    let C₂ : ℝ := Real.exp (1 / (12 * t₀) + 1 / (90 * t₀ ^ 3))
    let C₃ : ℝ := (C₂ - 1) / Real.log C₂ * (1 / 12 + 1 / (90 * t₀ ^ 2)) +
      t₀ * Real.exp (-Real.pi * t₀) * C₂
    ‖(2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
      Complex.sin ((Real.pi : ℂ) * s / 2)‖ ≤
      (1 + 1 / t₀ * (C₁ * (1 + Real.exp (-Real.pi * t₀)) * C₂ + C₃)) *
        (2 * Real.pi / |t|) ^ (σ - 1 / 2) := by
  simpa only [chi, chiC0, chiC1, chiC2, chiC3] using norm_chi_le_chiC0 hσ ht₀ ht

/-- The full first-derivative test of Lemma 4, with the maximum over the actual source interval. -/
theorem lemma_four_source {a b : ℝ} (hab : a ≤ b) {f f' g : ℝ → ℝ}
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hn : ∀ x ∈ Set.Icc a b, f' x ≠ 0)
    (hm : MonotoneOn (fun x => |g x / f' x|) (Set.Icc a b) ∨
      AntitoneOn (fun x => |g x / f' x|) (Set.Icc a b)) :
    ‖∫ x in a..b, (g x : ℂ) * Complex.exp ((f x : ℂ) * Complex.I)‖ ≤
      2 * sSup ((fun x => |g x / f' x|) '' Set.Icc a b) := by
  simpa only [mul_comm] using first_derivative_test_sup hab hd hc hg hn hm

/-- The finite arithmetic estimate inside Lemma 5 retains the actual half-integer cutoff.
The complete first integral-sum estimate has a separate source consumer. -/
theorem lemma_five_quadratic_sum {y : ℝ} (hy : y = (⌊y⌋₊ : ℝ) + 1 / 2) :
    (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℝ) ^ 2 / (y ^ 2 * (y - m))) ≤
      Real.log y + Real.eulerMascheroniConstant + 2 * Real.log 2 - 3 / 2 + 1 / (8 * y ^ 2) := by
  have h := half_integer_quadratic_sum_le ⌊y⌋₊
  rwa [← hy] at h

/-- The actual zero-endpoint remainder integral inside Lemma 5, with its physical scale linked. -/
theorem lemma_five_lower_remainder_source {σ t x y : ℝ} (hσ : σ < 1)
    (hx : 0 < x) (m : ℕ) (hmy : (m : ℝ) < y) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖∫ u in 0..x, (u : ℂ) ^ (2 - ((σ : ℂ) + (t : ℂ) * Complex.I)) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (u : ℂ))‖ ≤
      x ^ (2 - σ) / (Real.pi * (y - m)) := by
  simpa only [weightedIntegral, neg_sub, Complex.ofReal_natCast] using
    norm_weightedIntegral_shift_two_source (by linarith : σ ≤ 2) (Nat.cast_nonneg m) hx hmy hscale


/-- Lemma 5's complete first inequality: the actual J integrals, exact printed constants,
    both height signs, and both half-integer physical cutoffs. -/
theorem lemma_five_lower_sum_source {σ t x y : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hscale : 2 * Real.pi * x * y = |t|)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) :
    ‖∑ m ∈ Finset.Icc 1 ⌊y⌋₊, ∫ u in 0..x,
      (u : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (u : ℂ))‖ ≤
      x ^ (-σ) * (Real.log y / Real.pi +
        (Real.eulerMascheroniConstant + 2 * Real.log 2 - 3 / 2) / Real.pi +
          3 / (4 * Real.pi * y) + 3 / (8 * Real.pi * y ^ 2)) := by
  simpa only [weightedIntegral, Complex.ofReal_natCast] using
    norm_sum_lower_integral_source hσ.2 hx hy hscale hxhalf hyhalf


/-- Lemma 5's complete second inequality includes existence of every actual improper integral.
The signed cutoff printed with m is required for each frequency in the finite sum. -/
theorem lemma_five_upper_sum_source {σ t N y : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (hN : 0 < N) (hy : 1 ≤ y)
    (hcut : ∀ m ∈ Finset.Icc 1 ⌊y⌋₊, t / (Real.pi * (m : ℝ)) < N) :
    ∃ J : ℕ → ℂ,
      (∀ m ∈ Finset.Icc 1 ⌊y⌋₊,
        Filter.Tendsto (fun b : ℝ => ∫ u in N..b,
          (u : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (u : ℂ)))
              Filter.atTop (nhds (J m))) ∧
      ‖∑ m ∈ Finset.Icc 1 ⌊y⌋₊, J m‖ ≤
        2 * N ^ (-σ) / Real.pi * (Real.log y + 1) := by
  refine ⟨fun m => weightedIntegralTail ((σ : ℂ) + (t : ℂ) * Complex.I) N (m : ℝ), ?_, ?_⟩
  · intro m hm
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    simpa only [weightedIntegral, Complex.ofReal_natCast] using weightedIntegral_tendsto_tail hσ hmpos N
  · apply norm_sum_weightedIntegralTail_le hσ hN hy
    intro m hm
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have h := (div_lt_iff₀ (show 0 < Real.pi * (m : ℝ) by positivity)).mp (hcut m hm)
    nlinarith


/-- The decreasing derivative selects the unique actual stationary point, with zero shifted derivative. -/
theorem stationary_point_source {f : ℝ → ℝ} {a b ν : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hc : ContinuousOn (deriv f) (Set.Icc a b))
    (hm : StrictAntiOn (deriv f) (Set.Icc a b))
    (hν : ν ∈ Set.Icc (deriv f b) (deriv f a)) :
    ∃! x : ℝ, x ∈ Set.Icc a b ∧ deriv f x = ν ∧
      HasDerivAt (fun u => f u - ν * u) 0 x := by
  obtain ⟨x, hx, hu⟩ := existsUnique_stationaryPoint hab hc hm hν
  exact ⟨x, ⟨hx.1, hx.2, stationary_shift_hasDerivAt (hf x hx.1) hx.2⟩,
    fun y hy => hu y ⟨hy.1, hy.2.1⟩⟩

/-- The literal Fresnel integral has its evaluated phase and a quantitative finite-window error. -/
theorem fresnel_window_source {c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    ‖(∫ u in (-H)..H, Complex.exp (((-2 * Real.pi * c * u ^ 2 : ℝ) : ℂ) * Complex.I)) -
      Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * Complex.I) / (Real.sqrt (2 * c) : ℂ)‖ ≤
        2 / (c * H * Real.pi) := norm_quadraticWindow_sub_fresnel_le hc hH

/-- The actual critical point and curvature give the source's quadratic main term with phase −1/8.
The separate B-process gate must still prove the nonlinear Taylor replacement error. -/
theorem stationary_quadratic_phase_source {f : ℝ → ℝ} {x ν : ℝ}
    (hd : DifferentiableAt ℝ f x) (hv : deriv f x = ν) (hκ : deriv (deriv f) x < 0) :
    HasDerivAt (fun u => f u - ν * u) 0 x ∧
    Filter.Tendsto (fun H : ℝ => ∫ v in (-H)..H,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((f x - ν * x + deriv (deriv f) x * v ^ 2 / 2 : ℝ) : ℂ))) Filter.atTop
      (nhds (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((f x - ν * x - 1 / 8 : ℝ) : ℂ)) / (Real.sqrt |deriv (deriv f) x| : ℂ))) :=
  ⟨stationary_shift_hasDerivAt hd hv, quadratic_stationary_phase_limit (f x - ν * x) hκ⟩


/-- At the valid source parameter y=δ=1, the literal E₁ value fails to majorize its two actual tails.
This diagnoses the arithmetic assembly, not the entire weighted Poisson conclusion. -/
theorem partII_printed_E1_counterexample :
    ¬ ((∑' n : ℕ, 1 / (((n : ℝ) + 2) * ((n : ℝ) + 1) ^ 2)) +
      (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2)) ≤
        3 - 2 * Real.log 2 - 2 * Real.eulerMascheroniConstant) := by
  simpa only [printedPartIIE1_one] using printedPartIIE1_not_square_tail_bound

/-- Equation (I1 1.1) evaluates the actual improper integral with the source's principal complex power. -/
theorem weighted_integral_gamma_source {σ t m : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (hm : 0 < m) :
    Filter.Tendsto (fun R : ℝ => ∫ u in 0..R,
      (u : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (u : ℂ))) Filter.atTop
      (nhds (((2 * (Real.pi : ℂ) * (m : ℂ)) / Complex.I) ^
        (((σ : ℂ) + (t : ℂ) * Complex.I) - 1) *
          Complex.Gamma (1 - ((σ : ℂ) + (t : ℂ) * Complex.I)))) := by
  have he : 2 * (Real.pi : ℂ) * (m : ℂ) / Complex.I =
      -(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) := by
    rw [div_eq_mul_inv, Complex.inv_I]
    ring
  simpa only [weightedIntegral, weightedIntegralTail_zero_eq_gamma hσ hm, he] using
    weightedIntegral_tendsto_tail (t := t) hσ hm 0

/-- Equation (new I1) consumes the actual integral evaluation and Lemma 7, including its signed error. -/
theorem weighted_integral_chi_source {σ t m t₀ : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (hm : 0 < m) (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ∃ ε : ℂ,
      Filter.Tendsto (fun R : ℝ => ∫ u in 0..R,
        (u : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (u : ℂ))) Filter.atTop
        (nhds (chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (1 + ε) *
          (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))) ∧
      ‖ε‖ ≤ Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀)) := by
  refine ⟨gammaChiError ((σ : ℂ) + (t : ℂ) * Complex.I), ?_, ?_⟩
  · simpa only [weightedIntegral, weightedIntegralTail_zero_eq_chi hσ hm ht₀ ht] using
      weightedIntegral_tendsto_tail (t := t) hσ hm 0
  · simpa using norm_gammaChiError_le (s := (σ : ℂ) + (t : ℂ) * Complex.I) ht₀
      (by simpa using ht)

/-- The integral sum in equation (4.59), with each actual interval and all three explicit errors.
The Poisson-to-zeta step and the strip endpoints remain separate AFE2 obligations. -/
theorem afe_integral_sum_source {σ t x y R t₀ : ℝ}
    (hσ : σ ∈ Set.Ioo 0 1) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|)
    (hR : 0 < R) (hcut : ∀ m ∈ Finset.Icc 1 ⌊y⌋₊, t / (Real.pi * (m : ℝ)) < R)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖(∑ m ∈ Finset.Icc 1 ⌊y⌋₊, ∫ u in x..R,
      (u : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (u : ℂ))) -
      chi ((σ : ℂ) + (t : ℂ) * Complex.I) *
        ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1)‖ ≤
      ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        (Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀))) *
        (y ^ σ * Real.log y + 1) +
      x ^ (-σ) * (Real.log y / Real.pi +
        (Real.eulerMascheroniConstant + 2 * Real.log 2 - 3 / 2) / Real.pi +
          3 / (4 * Real.pi * y) + 3 / (8 * Real.pi * y ^ 2)) +
      2 * R ^ (-σ) / Real.pi * (Real.log y + 1) := by
  have hc : ∀ m ∈ Finset.Icc 1 ⌊y⌋₊, t < Real.pi * (m : ℝ) * R := by
    intro m hm
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have h := (div_lt_iff₀ (show 0 < Real.pi * (m : ℝ) by positivity)).mp (hcut m hm)
    nlinarith
  simpa only [weightedIntegral, Complex.ofReal_natCast] using
    norm_sum_weightedIntegral_sub_chi_le hσ hx hy hxhalf hyhalf hscale hR hc ht₀ ht

/-- The source's 1.251 is an outward bound for the actual digamma value, proved from finite rational enclosures. -/
theorem stationary_digamma_decimal_source :
    -(2 / Real.pi) * (Complex.digamma (1 / 2)).re ≤ 1.251 := by
  rw [real_digamma_half]
  convert stationary_digamma_constant_le using 1
  ring

/-- The actual AFE second derivatives satisfy the source's decreasing conditions, including σ=0. -/
theorem afe_second_derivatives_source {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 ≤ t) :
    AntitoneOn (deriv (deriv (fun u : ℝ => u ^ (-σ)))) (Set.Ioi 0) ∧
    AntitoneOn (fun u => |deriv (deriv (fun v => (t / (2 * Real.pi)) * Real.log v)) u|)
      (Set.Ioi 0) ∧
    AntitoneOn (fun u => |deriv (fun v => v ^ (-σ) *
      deriv (fun w => (t / (2 * Real.pi)) * Real.log w) v) u|) (Set.Ioi 0) := by
  simpa only [afeWeight, afePhase] using
    afe_second_derivatives_antitone hσ (div_nonneg ht (by positivity : 0 ≤ 2 * Real.pi))

/-- Both actual amplitudes satisfy the disputed positive-frequency quotient conditions directly.
This is an application theorem, not an assertion that the printed general inference is valid. -/
theorem afe_positive_second_quotients_source {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 ≤ t)
    {ν : ℕ} (hν : 0 < ν) (h : ℝ → ℝ)
    (hh : h = deriv (fun u : ℝ => u ^ (-σ)) ∨
      h = fun u => u ^ (-σ) * deriv (fun v => (t / (2 * Real.pi)) * Real.log v) u) :
    AntitoneOn (fun u => |deriv h u| /
      ((ν : ℝ) + deriv (fun v => (t / (2 * Real.pi)) * Real.log v) u) ^ 2) (Set.Ioi 0) ∧
    AntitoneOn (fun u => |h u * deriv (deriv (fun v => (t / (2 * Real.pi)) * Real.log v)) u| /
      ((ν : ℝ) + deriv (fun v => (t / (2 * Real.pi)) * Real.log v) u) ^ 3) (Set.Ioi 0) := by
  have hq := afe_second_quotients_antitone hσ
    (div_nonneg ht (by positivity : 0 ≤ 2 * Real.pi)) (Nat.cast_pos.mpr hν)
  rcases hh with rfl | rfl
  · simpa only [afeWeight, afePhase] using And.intro hq.1 hq.2.1
  · simpa only [afeWeight, afePhase] using hq.2.2

/-- The actual negative-frequency integral has the source's second-order bound with the corrected complex boundary factor. -/
theorem partII_negative_second_integral {a b ν : ℝ} (hab : a < b)
    {f h : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hh : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ h u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hfddc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hhdc : ContinuousOn (deriv h) (Set.Icc a b))
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hha : AntitoneOn (fun u => |h u|) (Set.Icc a b))
    (hhda : AntitoneOn (fun u => |deriv h u|) (Set.Icc a b))
    (hfdda : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b)) (hν : deriv f a < ν) :
    ‖(∫ u in a..b, (h u : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      (((h b / (deriv f b - ν) : ℝ) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((f b - ν * b : ℝ) : ℂ)) -
        ((h a / (deriv f a - ν) : ℝ) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((f a - ν * a : ℝ) : ℂ))) /
          (2 * (Real.pi : ℂ) * Complex.I)‖ ≤
      |deriv h a| / (2 * Real.pi ^ 2 * (ν - deriv f a) ^ 2) +
        |h a * deriv (deriv f) a| / (2 * Real.pi ^ 2 * (ν - deriv f a) ^ 3) :=
  norm_negative_exp_integral_sub_boundary_le hab (fun u hu => (hf u hu).hasDerivAt)
    (fun u hu => (hfd u hu).hasDerivAt) (fun u hu => (hh u hu).hasDerivAt)
    hfc hfddc hhdc hfa hha hhda hfdda hν

/-- Both actual AFE amplitudes consume the second-integration estimate at the physical height scale.
All regularity and monotonicity conditions are derived, including the σ=0 boundary. -/
theorem afe_positive_second_integral_source {σ t ν a b : ℝ} (hσ : 0 ≤ σ) (ht : 0 ≤ t)
    (hν : 0 < ν) (ha : 0 < a) (hab : a < b) (h : ℝ → ℝ)
    (hh : h = deriv (fun u : ℝ => u ^ (-σ)) ∨
      h = fun u => u ^ (-σ) * deriv (fun v => (t / (2 * Real.pi)) * Real.log v) u) :
    ‖(∫ u in a..b, (h u : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (((t / (2 * Real.pi)) * Real.log u + ν * u : ℝ) : ℂ))) -
      (((h b / (ν + (t / (2 * Real.pi)) / b) : ℝ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((t / (2 * Real.pi)) * Real.log b + ν * b : ℝ) : ℂ)) -
       ((h a / (ν + (t / (2 * Real.pi)) / a) : ℝ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((t / (2 * Real.pi)) * Real.log a + ν * a : ℝ) : ℂ))) /
          (2 * (Real.pi : ℂ) * Complex.I)‖ ≤
      |deriv h a| / (2 * Real.pi ^ 2 * (ν + (t / (2 * Real.pi)) / a) ^ 2) +
        |h a * (-(t / (2 * Real.pi)) / a ^ 2)| /
          (2 * Real.pi ^ 2 * (ν + (t / (2 * Real.pi)) / a) ^ 3) := by
  have hc : 0 ≤ t / (2 * Real.pi) := div_nonneg ht (by positivity)
  have hb := afe_positive_second_integral_bound hσ hc hν ha hab h hh
  simpa only [(afePhase_hasDerivAt (t / (2 * Real.pi)) ha).deriv,
    (afePhase_hasDerivAt (t / (2 * Real.pi)) (ha.trans hab)).deriv,
    (afePhase_deriv_hasDerivAt (t / (2 * Real.pi)) ha).deriv, afePhase] using hb

/-- The literal cubic functions satisfy all printed decreasing conditions but refute the positive-frequency quotient inference. -/
theorem partII_quotient_inference_counterexample :
    let f : ℝ → ℝ := fun x => 2 * x - x ^ 2 / 20 + x ^ 3 / 300
    let g : ℝ → ℝ := fun x => 10 - x + x ^ 2 / 20 - x ^ 3 / 6000
    PartIRegularityAt f g 0 1 0 ∧
    ContDiff ℝ ⊤ f ∧ ContDiff ℝ ⊤ g ∧
    StrictAntiOn (deriv f) (Set.Icc 0 1) ∧
    (∀ x ∈ Set.Icc 0 1, 0 < g x ∧ 0 < deriv f x ∧
      0 < |deriv g x| ∧ 0 < |deriv (deriv f) x| ∧
      0 < deriv (deriv g) x ∧
      0 < |deriv g x * deriv f x + g x * deriv (deriv f) x|) ∧
    StrictAntiOn (fun x => |deriv g x|) (Set.Icc 0 1) ∧
    StrictAntiOn (fun x => |deriv (deriv f) x|) (Set.Icc 0 1) ∧
    StrictAntiOn (deriv (deriv g)) (Set.Icc 0 1) ∧
    StrictAntiOn (fun x => |deriv g x * deriv f x + g x * deriv (deriv f) x|)
      (Set.Icc 0 1) ∧
    ¬ AntitoneOn (fun x => |deriv (deriv g) x| / (1 + deriv f x) ^ 2) (Set.Icc 0 1) := by
  simpa only [PartIIMonotonicity.phase, PartIIMonotonicity.weight] using
    PartIIMonotonicity.source_conditions_and_failed_quotient

/-- The physical AFE phase and both literal amplitudes satisfy the complete positive-frequency series estimate. -/
theorem afe_positive_second_tail_source {σ t a b : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (ha : 0 < a) (hab : a < b) (h : ℝ → ℝ)
    (hh : h = deriv (fun u : ℝ => u ^ (-σ)) ∨
      h = fun u => u ^ (-σ) * deriv (fun v => (t / (2 * Real.pi)) * Real.log v) u) :
    let c : ℝ := t / (2 * Real.pi)
    Summable (fun n : ℕ => ((∫ u in a..b, (h u : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((c * Real.log u + ((n : ℝ) + 1) * u : ℝ) : ℂ))) /
      (2 * (Real.pi : ℂ) * ((n : ℂ) + 1)))) ∧
    ‖∑' n : ℕ, ((∫ u in a..b, (h u : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((c * Real.log u + ((n : ℝ) + 1) * u : ℝ) : ℂ))) /
      (2 * (Real.pi : ℂ) * ((n : ℂ) + 1)))‖ ≤
      |h b| / (4 * Real.pi ^ 2) * ‖positiveTail (-b) (c / b)‖ +
      |h a| / (4 * Real.pi ^ 2) * ‖positiveTail (-a) (c / a)‖ +
      (|deriv h a| / (4 * Real.pi ^ 3)) *
        ((Real.log (c / a + 1) + Real.eulerMascheroniConstant) / (c / a) ^ 2 -
          (1 + 2 * (c / a)) / (2 * (c / a) ^ 2 * (c / a + 1))) +
      (|h a * (-c / a ^ 2)| / (4 * Real.pi ^ 3)) *
        ((Real.log (c / a + 1) + Real.eulerMascheroniConstant) / (c / a) ^ 3 -
          (1 + 3 * (c / a) + 3 * (c / a) ^ 2) / (2 * (c / a) ^ 3 * (c / a + 1) ^ 2)) := by
  simpa only [secondModeTerm, afePhase, afeWeight] using
    afe_positive_second_tail_bound hσ (div_pos ht (by positivity : 0 < 2 * Real.pi)) ha hab h hh

/-- The actual AFE upper-frequency series uses the physical scale and its derived floor cutoff. -/
theorem afe_upper_second_tail_source {σ t a b : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (ha : 0 < a) (hab : a < b) (h : ℝ → ℝ)
    (hh : h = deriv (fun u : ℝ => u ^ (-σ)) ∨
      h = fun u => u ^ (-σ) * deriv (fun v => (t / (2 * Real.pi)) * Real.log v) u) :
    let c : ℝ := t / (2 * Real.pi)
    let M : ℕ := ⌊c / a⌋₊
    let δ : ℝ := (M : ℝ) + 1 - c / a
    Summable (fun n : ℕ => ((∫ u in a..b, (h u : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((c * Real.log u - ((n : ℝ) + M + 1) * u : ℝ) : ℂ))) /
      (2 * (Real.pi : ℂ) * ((n : ℂ) + M + 1)))) ∧
    ‖∑' n : ℕ, ((∫ u in a..b, (h u : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((c * Real.log u - ((n : ℝ) + M + 1) * u : ℝ) : ℂ))) /
      (2 * (Real.pi : ℂ) * ((n : ℂ) + M + 1)))‖ ≤
      |h b| / (4 * Real.pi ^ 2) * ‖negativeTail M b (c / b)‖ +
      |h a| / (4 * Real.pi ^ 2) * ‖negativeTail M a (c / a)‖ +
      (|deriv h a| / (4 * Real.pi ^ 3)) *
        ((1 / δ ^ 2 + 1 / (δ + 1) ^ 2 + 1 / (δ + 1)) / (c / a) -
          (Real.log ((M : ℝ) + 1) - 1 / ((M : ℝ) + 1) -
            (Complex.digamma (δ : ℂ)).re) / (c / a) ^ 2) +
      (|h a * (-c / a ^ 2)| / (4 * Real.pi ^ 3)) *
        ((1 / δ ^ 3 + 1 / (δ + 1) ^ 3 + 1 / (2 * (δ + 1) ^ 2)) / (c / a) -
          (1 / δ ^ 2 + 1 / (δ + 1)) / (c / a) ^ 2 +
          (Real.log ((M : ℝ) + 1) - 1 / (2 * ((M : ℝ) + 1)) -
            (Complex.digamma (δ : ℂ)).re) / (c / a) ^ 3) := by
  simpa only [upperModeTerm, afePhase, afeWeight] using
    afe_upper_second_tail_bound hσ (div_pos ht (by positivity : 0 < 2 * Real.pi)) ha hab h hh
      (Nat.lt_floor_add_one ((t / (2 * Real.pi)) / a))

/-- The actual logarithmic phase and power weight enter the complete four-series Poisson identity at the physical cutoff. -/
theorem afe_second_poisson_source {σ t a b : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (ha : 0 < a) (hab : a < b) :
    let c : ℝ := t / (2 * Real.pi)
    let f : ℝ → ℝ := fun u => c * Real.log u
    let g : ℝ → ℝ := fun u : ℝ => u ^ (-σ)
    let M : ℕ := ⌊c / a⌋₊
    (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M =
      poissonHeadBoundary f g b M - poissonHeadBoundary f g a M +
        ((∑' n : ℕ, upperModeTerm f (deriv g) a b M n) / Complex.I +
          (2 * (Real.pi : ℂ)) * ∑' n : ℕ, upperModeTerm f (fun u => g u * deriv f u) a b M n) -
        ((∑' n : ℕ, secondModeTerm f (deriv g) a b n) / Complex.I +
          (2 * (Real.pi : ℂ)) * ∑' n : ℕ, secondModeTerm f (fun u => g u * deriv f u) a b n) +
        poissonBoundary f g a b := by
  simpa only [afePhase, afeWeight] using
    afe_second_poisson_identity hσ (div_pos ht (by positivity : 0 < 2 * Real.pi)) ha hab

/-- The actual physical AFE finite sum and literal Fourier integrals satisfy the assembled second-order estimate. -/
theorem afe_second_poisson_bound_source {σ t a b : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (ha : 0 < a) (hab : a < b) :
    let c : ℝ := t / (2 * Real.pi)
    let f : ℝ → ℝ := fun u => c * Real.log u
    let g : ℝ → ℝ := fun u : ℝ => u ^ (-σ)
    let M : ℕ := ⌊c / a⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, ((g (n : ℝ) : ℝ) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((f (n : ℝ) : ℝ) : ℂ))) - (∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b, (g u : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ)))‖ ≤
      ‖poissonHeadBoundary f g b M‖ + ‖poissonHeadBoundary f g a M‖ + ‖poissonBoundary f g a b‖ +
      secondH f g b / (4 * Real.pi ^ 2) *
        (‖negativeTail M b (c / b)‖ + ‖positiveTail (-b) (c / b)‖) +
      secondH f g a / (4 * Real.pi ^ 2) *
        (‖negativeTail M a (c / a)‖ + ‖positiveTail (-a) (c / a)‖) +
      secondH1 f g a / (4 * Real.pi ^ 3) *
        (minusSquareBound M (c / a) + plusSquareBound (c / a)) +
      (secondH f g a * (c / a ^ 2) / (4 * Real.pi ^ 3)) *
        (minusCubeBound M (c / a) + plusCubeBound (c / a)) := by
  have hb := afe_finite_poisson_second_bound hσ (div_pos ht (by positivity : 0 < 2 * Real.pi)) ha hab
  dsimp only at hb
  rw [poissonMain_eq_source] at hb
  simpa only [weightedWave, afePhase, afeWeight] using hb

/-- The literal source E₂ majorizes the two actual cube-denominator tails. -/
theorem partII_cube_coefficient_source {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, 1 / (((n : ℝ) + ⌊y⌋₊ + 1) * ((n : ℝ) + ⌊y⌋₊ + 1 - y) ^ 3)) +
      (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) ^ 3)) ≤
      (  let δ : ℝ := 1 - (y - (⌊y⌋₊ : ℝ))
  1 / δ ^ 3 + 1 / (δ + 1) ^ 3 + 1 / (2 * (δ + 1) ^ 2) -
    1 / y * (1 / δ ^ 2 + 1 / (δ + 1)) +
    1 / y ^ 2 * (Real.log ((⌊y⌋₊ : ℝ) + 1) - 1 / (2 * ((⌊y⌋₊ : ℝ) + 1)) -
      (Complex.digamma (δ : ℂ)).re + Real.log (y + 1) + Real.eulerMascheroniConstant -
      (3 * y + 3 * y ^ 2 + 1) / (2 * (1 + y) ^ 2))) / y := by
  exact partII_cube_coefficient_bound hy

/-- The actual pair of endpoint tails satisfies the literal half-integer B expression. -/
theorem partII_half_endpoint_source {M : ℕ} {x y : ℝ}
    (hx : ∃ k : ℤ, x = (k : ℝ) + 1 / 2) (hy : 0 < y)
    (hδ : 1 / 2 ≤ (M : ℝ) + 1 - y) :
    ‖negativeTail M x y‖ + ‖positiveTail (-x) y‖ ≤
      (1 / y) * (Real.pi / 2 + 1 / ((M : ℝ) + 1) + Real.log 2 + 3 / (2 * (y + 1))) :=
  second_endpoint_half_integer_bound hx hy hδ

/-- The literal physical AFE sum and Fourier integrals satisfy the complete half-integer endpoint simplification. -/
theorem afe_second_poisson_half_source {σ t a b : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (ha : 0 < a) (hab : a < b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ (⌊(t / (2 * Real.pi)) / a⌋₊ : ℝ) + 1 - (t / (2 * Real.pi)) / a) :
    let c : ℝ := t / (2 * Real.pi)
    let f : ℝ → ℝ := fun u => c * Real.log u
    let g : ℝ → ℝ := fun u : ℝ => u ^ (-σ)
    let M : ℕ := ⌊c / a⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, ((g (n : ℝ) : ℝ) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((f (n : ℝ) : ℝ) : ℂ))) - (∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b, (g u : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ)))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / (c / a)) +
      secondH f g b / (4 * Real.pi ^ 2) * halfSecondEndpointBound M (c / b) +
      secondH f g a / (4 * Real.pi ^ 2) * halfSecondEndpointBound M (c / a) +
      secondH1 f g a / (4 * Real.pi ^ 3) *
        (minusSquareBound M (c / a) + plusSquareBound (c / a)) +
      (secondH f g a * (c / a ^ 2) / (4 * Real.pi ^ 3)) *
        (minusCubeBound M (c / a) + plusCubeBound (c / a)) := by
  have hb := afe_finite_poisson_second_half hσ (div_pos ht (by positivity : 0 < 2 * Real.pi)) ha hab hah hbh hδ
  dsimp only at hb
  rw [poissonMain_eq_source] at hb
  simpa only [weightedWave, afePhase, afeWeight] using hb

/-- The actual zeta function, sharp polynomial and improper integrals consume the proved second-order Poisson limit. -/
theorem afe_second_zeta_limit_source {σ t a : ℝ} (hσ : σ ∈ Set.Ioo 0 1) (ht : 0 < t)
    (ha : 0 < a) (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ (⌊(t / (2 * Real.pi)) / a⌋₊ : ℝ) + 1 - (t / (2 * Real.pi)) / a) :
    let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    let c : ℝ := t / (2 * Real.pi)
    ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s)) - (a : ℂ) ^ (1 - s) / (s - 1) -
      ∑ m ∈ Finset.Icc 1 ⌊c / a⌋₊, weightedIntegralTail s a m‖ ≤ afeSecondLeftError σ c a := by
  simpa only [sharpZetaSum, zetaTerm] using
    afe_zeta_sub_sum_pole_integrals_bound hσ ht ha hah hδ

/-- The actual two Dirichlet polynomials satisfy the assembled strict-strip error estimate. -/
theorem afe_second_strict_strip_source {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Ioo 0 1) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = t)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) -
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) -
      chi ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      afeSecondLeftError σ (t / (2 * Real.pi)) x + (x / t) * x ^ (-σ) +
      ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        (Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀))) * (y ^ σ * Real.log y + 1) +
      x ^ (-σ) * (Real.log y / Real.pi +
        (Real.eulerMascheroniConstant + 2 * Real.log 2 - 3 / 2) / Real.pi +
          3 / (4 * Real.pi * y) + 3 / (8 * Real.pi * y ^ 2)) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using
    afe_strict_strip_bound hσ hx hy hxhalf hyhalf hscale ht₀ ht

/-- The literal zeta and both polynomials satisfy the closed-strip estimate at both height signs. -/
theorem afe_second_closed_strip_source {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) -
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) -
      chi ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤ afeSecondError σ |t| x y t₀ := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using
    afe_closed_strip_abs_bound hσ hx hy hxhalf hyhalf hscale ht₀ ht

/-- The reflected quantitative estimate consumes the actual zeta remainder, including σ=1 and dual σ=0. -/
theorem afe_second_reflected_source {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) -
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) -
      chi ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * afeSecondError (1 - σ) |t| y x t₀ := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using
    afe_closed_strip_reflected_bound hσ hx hy hxhalf hyhalf hscale ht₀ ht


/-- The actual half-integer endpoint tails retain cancellation and all frequency indices. -/
theorem partII_half_endpoint_sharp_source {M : ℕ} {x y : ℝ}
    (hx : ∃ k : ℤ, x = (k : ℝ) + 1 / 2) (hy : 0 < y)
    (hδ : 1 / 2 ≤ (M : ℝ) + 1 - y) :
    ‖negativeTail M x y‖ + ‖positiveTail (-x) y‖ ≤ (Real.pi / 2 + Real.log 2) / y :=
  second_endpoint_half_integer_sharp hx hy hδ

/-- The two actual square-denominator tails satisfy the unchanged 46/9 half-integer coefficient. -/
theorem partII_half_square_source {y : ℝ} (hy : 1 ≤ y)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) :
    (∑' n : ℕ, 1 / (((n : ℝ) + ⌊y⌋₊ + 1) * ((n : ℝ) + ⌊y⌋₊ + 1 - y) ^ 2)) +
      (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) ^ 2)) ≤ (46 / 9) / y := by
  have hypos : 0 < y := by linarith
  exact (add_le_add (harmonic_tail_square_bound hypos (Nat.lt_floor_add_one y))
    (harmonic_plus_square_bound hypos)).trans (squareBounds_half_le hy hyhalf)

/-- The two actual cube-denominator tails satisfy the unchanged 230/27 half-integer coefficient. -/
theorem partII_half_cube_source {y : ℝ} (hy : 3 / 2 ≤ y)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) :
    (∑' n : ℕ, 1 / (((n : ℝ) + ⌊y⌋₊ + 1) * ((n : ℝ) + ⌊y⌋₊ + 1 - y) ^ 3)) +
      (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) ^ 3)) ≤ (230 / 27) / y := by
  have hypos : 0 < y := by linarith
  exact (add_le_add (harmonic_tail_cube_bound hypos (Nat.lt_floor_add_one y))
    (harmonic_plus_cube_bound hypos)).trans (cubeBounds_half_le hy hyhalf)

/-- The literal A and B formulas bound the actual two-polynomial remainder for both height signs. -/
theorem afe_second_AB_source {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) (hx : 3 / 2 ≤ x) (hy : 3 / 2 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    let A : ℝ → ℝ → ℝ → ℝ → ℝ := fun σ t x y =>
  1 / 4 + (Real.eulerMascheroniConstant + (7 / 2) * Real.log 2 - 3 / 2) / Real.pi +
    (115 / (54 * Real.pi ^ 3)) * (t / x ^ 2) +
    7 / (4 * Real.pi * y) + 3 / (4 * Real.pi * (y + 1)) + 7 / (8 * Real.pi * y ^ 2) +
    (23 * (σ + 1)) / (9 * Real.pi ^ 2 * x) + (115 * σ) / (54 * Real.pi ^ 3 * x ^ 2) +
    σ / (4 * t) + σ / (2 * Real.pi * y ^ 2 * t) +
    (σ * Real.log 2) / (2 * Real.pi * t) + (3 * σ) / (4 * Real.pi * (y + 1) * t) +
    (23 * σ * (σ + 1)) / (9 * Real.pi ^ 2 * x * t)
    let B : ℝ → ℝ → ℝ → ℝ → ℝ := fun σ t y t₀ =>
  (y * Real.log y + y ^ (1 - σ)) * Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀))
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) -
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) -
      chi ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      (Real.log y / Real.pi + A σ |t| x y) * x ^ (-σ) +
        ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * B σ |t| y t₀ * y ^ (σ - 1) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub, afeSourceA, afeSourceB] using
    afe_second_source_AB hσ hx hy hxhalf hyhalf hscale ht₀ ht

/-- The reflected actual remainder has log(x), exchanged cutoffs and exactly the literal dual A/B formulas. -/
theorem afe_second_AB_reflected_source {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) (hx : 3 / 2 ≤ x) (hy : 3 / 2 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    let A : ℝ → ℝ → ℝ → ℝ → ℝ := fun σ t x y =>
  1 / 4 + (Real.eulerMascheroniConstant + (7 / 2) * Real.log 2 - 3 / 2) / Real.pi +
    (115 / (54 * Real.pi ^ 3)) * (t / x ^ 2) +
    7 / (4 * Real.pi * y) + 3 / (4 * Real.pi * (y + 1)) + 7 / (8 * Real.pi * y ^ 2) +
    (23 * (σ + 1)) / (9 * Real.pi ^ 2 * x) + (115 * σ) / (54 * Real.pi ^ 3 * x ^ 2) +
    σ / (4 * t) + σ / (2 * Real.pi * y ^ 2 * t) +
    (σ * Real.log 2) / (2 * Real.pi * t) + (3 * σ) / (4 * Real.pi * (y + 1) * t) +
    (23 * σ * (σ + 1)) / (9 * Real.pi ^ 2 * x * t)
    let B : ℝ → ℝ → ℝ → ℝ → ℝ := fun σ t y t₀ =>
  (y * Real.log y + y ^ (1 - σ)) * Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀))
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) -
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) -
      chi ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        (Real.log x / Real.pi + A (1 - σ) |t| y x) * y ^ (σ - 1) +
          B (1 - σ) |t| x t₀ * x ^ (-σ) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub, afeSourceA, afeSourceB] using
    afe_second_source_AB_reflected hσ hx hy hxhalf hyhalf hscale ht₀ ht

/-- The exact proof-consistent direct branch retains all A₀/B₀ terms, actual polynomials, source domains and the diagonal. -/
theorem theorem_ten_direct_source {σ t t₀ x y h : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hh : 3 / 2 ≤ h) (hx : h ≤ x) (hy : h ≤ y) (hyx : y ≤ x)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    let A₀ : ℝ → ℝ → ℝ → ℝ := fun σ h t₀ =>
  let x₀ := max h (Real.sqrt (t₀ / (2 * Real.pi)))
  1 / 4 + (Real.eulerMascheroniConstant + (7 / 2) * Real.log 2 - 3 / 2) / Real.pi +
    115 / (27 * Real.pi ^ 2) +
    7 / (4 * Real.pi * h) + 3 / (4 * Real.pi * (h + 1)) + 7 / (8 * Real.pi * h ^ 2) +
    (23 * (σ + 1)) / (9 * Real.pi ^ 2 * x₀) + (115 * σ) / (54 * Real.pi ^ 3 * x₀ ^ 2) +
    σ / (4 * t₀) + σ / (2 * Real.pi * h ^ 2 * t₀) +
    (σ * Real.log 2) / (2 * Real.pi * t₀) + (3 * σ) / (4 * Real.pi * (h + 1) * t₀) +
    (23 * σ * (σ + 1)) / (9 * Real.pi ^ 2 * x₀ * t₀)
    let B₀ : ℝ → ℝ → ℝ := fun σ t₀ =>
  ((1 / 2) * Real.sqrt (t₀ / (2 * Real.pi)) * Real.log (t₀ / (2 * Real.pi)) +
    (t₀ / (2 * Real.pi)) ^ ((1 - σ) / 2)) * Real.exp (-Real.pi * t₀) /
      (1 - Real.exp (-Real.pi * t₀))
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) -
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) -
      chi ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      (Real.log y / Real.pi + A₀ σ h t₀ + chiC0 σ t₀ * B₀ σ t₀) *
        (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub, afeSourceA0, afeSourceB0] using
    afe_second_uniform_direct hσ ht₀ ht hh hx hy hyx hxhalf hyhalf hscale

/-- The exact proof-consistent reflected branch retains the dual exponent and full source constants, including σ=1. -/
theorem theorem_ten_reflected_source {σ t t₀ x y h : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hh : 3 / 2 ≤ h) (hx : h ≤ x) (hy : h ≤ y) (hxy : x ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    let A₀ : ℝ → ℝ → ℝ → ℝ := fun σ h t₀ =>
  let x₀ := max h (Real.sqrt (t₀ / (2 * Real.pi)))
  1 / 4 + (Real.eulerMascheroniConstant + (7 / 2) * Real.log 2 - 3 / 2) / Real.pi +
    115 / (27 * Real.pi ^ 2) +
    7 / (4 * Real.pi * h) + 3 / (4 * Real.pi * (h + 1)) + 7 / (8 * Real.pi * h ^ 2) +
    (23 * (σ + 1)) / (9 * Real.pi ^ 2 * x₀) + (115 * σ) / (54 * Real.pi ^ 3 * x₀ ^ 2) +
    σ / (4 * t₀) + σ / (2 * Real.pi * h ^ 2 * t₀) +
    (σ * Real.log 2) / (2 * Real.pi * t₀) + (3 * σ) / (4 * Real.pi * (h + 1) * t₀) +
    (23 * σ * (σ + 1)) / (9 * Real.pi ^ 2 * x₀ * t₀)
    let B₀ : ℝ → ℝ → ℝ := fun σ t₀ =>
  ((1 / 2) * Real.sqrt (t₀ / (2 * Real.pi)) * Real.log (t₀ / (2 * Real.pi)) +
    (t₀ / (2 * Real.pi)) ^ ((1 - σ) / 2)) * Real.exp (-Real.pi * t₀) /
      (1 - Real.exp (-Real.pi * t₀))
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) -
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) -
      chi ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      (chiC0 σ t₀ / Real.pi * Real.log x + A₀ (1 - σ) h t₀ * chiC0 σ t₀ +
        B₀ (1 - σ) t₀) * x ^ (-σ) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub, afeSourceA0, afeSourceB0] using
    afe_second_uniform_reflected hσ ht₀ ht hh hx hy hxy hxhalf hyhalf hscale

/-- The constant-weight source estimate retains the complete shifted range and all N-dependent terms. -/
theorem shifted_constant_poisson_source {f : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hN : (N : ℝ) < deriv f b)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ x in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      (1 / Real.pi) *
        (Real.log (1 + (deriv f a - N)) + Real.eulerMascheroniConstant +
          Real.log (((⌊deriv f a⌋₊ - N : ℕ) : ℝ) + 1) -
            (Complex.digamma ((1 - Int.fract (deriv f a) : ℝ) : ℂ)).re -
          1 / (2 * (((⌊deriv f a⌋₊ - N : ℕ) : ℝ) + 1)) -
            1 / (2 * (1 + (deriv f a - N))) + Real.log 2 + 1 / (deriv f a - N)) := by
  exact poisson_constant_partI_half_integer hab hfd hfc hN hfa ha hb

/-- The repaired general second-order analytic interface bounds the actual sum and literal Fourier integrals. -/
theorem general_second_poisson_source {f g : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f g a b) :
    let M : ℕ := ⌊deriv f a⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, (g (n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) - (∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b, (g u : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ)))‖ ≤
      ‖poissonHeadBoundary f g b M‖ + ‖poissonHeadBoundary f g a M‖ + ‖poissonBoundary f g a b‖ +
      secondH f g b / (4 * Real.pi ^ 2) *
        (‖negativeTail M b (deriv f b)‖ + ‖positiveTail (-b) (deriv f b)‖) +
      secondH f g a / (4 * Real.pi ^ 2) *
        (‖negativeTail M a (deriv f a)‖ + ‖positiveTail (-a) (deriv f a)‖) +
      secondH1 f g a / (4 * Real.pi ^ 3) *
        (minusSquareBound M (deriv f a) + plusSquareBound (deriv f a)) +
      (secondH f g a * (|deriv (deriv f) a|) / (4 * Real.pi ^ 3)) *
        (minusCubeBound M (deriv f a) + plusCubeBound (deriv f a)) := by
  simpa only [weightedWave, poissonMain_eq_source] using r.finite_poisson_bound


/-- The actual AFE functions consume the general second-order bound with every technical hypothesis proved. -/
theorem afe_general_second_poisson_source {σ c a b : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) :
    let f : ℝ → ℝ := afePhase c
    let g : ℝ → ℝ := afeWeight σ
    let M : ℕ := ⌊deriv f a⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M‖ ≤
      ‖poissonHeadBoundary f g b M‖ + ‖poissonHeadBoundary f g a M‖ + ‖poissonBoundary f g a b‖ +
      secondH f g b / (4 * Real.pi ^ 2) *
        (‖negativeTail M b (deriv f b)‖ + ‖positiveTail (-b) (deriv f b)‖) +
      secondH f g a / (4 * Real.pi ^ 2) *
        (‖negativeTail M a (deriv f a)‖ + ‖positiveTail (-a) (deriv f a)‖) +
      secondH1 f g a / (4 * Real.pi ^ 3) *
        (minusSquareBound M (deriv f a) + plusSquareBound (deriv f a)) +
      (secondH f g a * (|deriv (deriv f) a|) / (4 * Real.pi ^ 3)) *
        (minusCubeBound M (deriv f a) + plusCubeBound (deriv f a)) := by
  exact (afe_secondOrderRegularity hσ hc ha hab).finite_poisson_bound

/-- The complete source-frequency range and actual weighted sum consume the explicit repaired second-order theorem. -/
theorem general_second_poisson_shifted_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N)
    (r : SecondOrderRegularity (phaseShift f N) g a b) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, (g (n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      secondPoissonError (phaseShift f N) g a b := by
  simpa only [weightedWave] using second_poisson_shifted_bound h r


/-- The complete source-frequency range and actual weighted sum consume the explicit repaired second-order theorem. -/
theorem general_second_poisson_half_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N)
    (r : SecondOrderRegularity (phaseShift f N) g a b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ 1 - Int.fract (deriv f a)) :
    let F := phaseShift f N
    let y := deriv f a - N
    let M := ⌊deriv f a⌋₊ - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, (g (n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH F g b / (4 * Real.pi ^ 2) * halfSecondEndpointBound M (deriv f b - N) +
      secondH F g a / (4 * Real.pi ^ 2) * halfSecondEndpointBound M y +
      secondH1 F g a / (4 * Real.pi ^ 3) * (minusSquareBound M y + plusSquareBound y) +
      (secondH F g a * |deriv (deriv F) a| / (4 * Real.pi ^ 3)) *
        (minusCubeBound M y + plusCubeBound y) := by
  simpa only [weightedWave] using second_poisson_shifted_half h r hah hbh hδ

/-- The exact analytic source consumer retains the full domain and actual sums; numerical table certification is separate. -/
theorem constant_second_poisson_source {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hpos : 0 < deriv f b)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hfdd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfcc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hanti : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hq : ∀ n : ℕ, AntitoneOn (fun u => |deriv (deriv f) u| /
      (((n : ℝ) + 1) + deriv f u) ^ 2) (Set.Icc a b))
    (hr : ∀ n : ℕ, AntitoneOn (fun u => |deriv f u * deriv (deriv f) u| /
      (((n : ℝ) + 1) + deriv f u) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a) :
    let y := deriv f a
    let M := ⌊y⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / y) / Real.pi +
      (deriv f b * halfSecondEndpointBound M (deriv f b) + y * halfSecondEndpointBound M y) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) * (minusSquareBound M y + plusSquareBound y) +
      (y * |deriv (deriv f) a| / (2 * Real.pi ^ 2)) * (minusCubeBound M y + plusCubeBound y) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using constant_second_poisson_from_phase hab hfd hfc hpos hfa hfdd hfcc hanti hq hr hah hbh hδ


/-- The exact analytic source consumer retains the full domain and actual sums; numerical table certification is separate. -/
theorem afe_maxima_attained_source {h t₀ : ℝ} (ht : 0 < t₀) :
    (∃ σ ∈ afeSigmaStrip, afeDirectMaximum h t₀ = afeDirectE0 σ h t₀) ∧
    (∃ σ ∈ afeSigmaStrip, afeReflectedMaximum h t₀ = afeReflectedE0 σ h t₀) ∧
    (∃ σ ∈ afeSigmaStrip, afeDelta0 t₀ + 1 = chiC0 σ t₀) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_source_maxima_attained ht


/-- The exact analytic source consumer retains the full domain and actual sums; numerical table certification is separate. -/
theorem corollary_zero_four_direct_source {σ t t₀ x y h : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hh : 3 / 2 ≤ h) (hx : h ≤ x) (hy : h ≤ y) (hyx : y ≤ x)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      (Real.log y / Real.pi + afeDirectMaximum h t₀) *
        (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_uniform_max_direct hσ ht₀ ht hh hx hy hyx hxhalf hyhalf hscale


/-- The exact analytic source consumer retains the full domain and actual sums; numerical table certification is separate. -/
theorem corollary_zero_four_reflected_source {σ t t₀ x y h : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hh : 3 / 2 ≤ h) (hx : h ≤ x) (hy : h ≤ y) (hxy : x ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      ((1 + afeDelta0 t₀) / Real.pi * Real.log x + afeReflectedMaximum h t₀) * x ^ (-σ) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_uniform_max_reflected hσ ht₀ ht hh hx hy hxy hxhalf hyhalf hscale


/-- The exact analytic source consumer retains the full domain and actual sums; numerical table certification is separate. -/
theorem corollary_zero_five_direct_source {σ t t₀ x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hk : 1 ≤ k) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hyx : y ≤ x)
    (hband : y ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      ((k : ℝ) / Real.pi + afeDirectMaximum (afeBandLower k) t₀) *
        (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_band_direct hσ ht₀ ht hk hx hy hyx hband hxhalf hyhalf hscale


/-- The exact analytic source consumer retains the full domain and actual sums; numerical table certification is separate. -/
theorem corollary_zero_five_reflected_source {σ t t₀ x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hk : 1 ≤ k) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hxy : x ≤ y)
    (hband : x ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      ((k : ℝ) * (1 + afeDelta0 t₀) / Real.pi + afeReflectedMaximum (afeBandLower k) t₀) * x ^ (-σ) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_band_reflected hσ ht₀ ht hk hx hy hxy hband hxhalf hyhalf hscale

/-- The complete constant-six consequence has the literal source polynomials, all endpoints and both height signs. -/
theorem constant_six_direct_source {σ t x y : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (ht : 2 * Real.pi ≤ |t|) (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hymax : y ≤ 1000000)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      6 * (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_constant_six_direct hσ ht hx hy hyx hymax hxhalf hyhalf hscale


/-- The complete constant-six consequence has the literal source polynomials, all endpoints and both height signs. -/
theorem constant_six_reflected_source {σ t x y : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (ht : 2 * Real.pi ≤ |t|) (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x ≤ y)
    (hxmax : x ≤ 1000000)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤ 6 * x ^ (-σ) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_constant_six_reflected hσ ht hx hy hxy hxmax hxhalf hyhalf hscale

/-- The unchanged large-k decimal is certified on the entire stated integer range and consumed by actual source objects. -/
theorem large_k_constants_source {k : ℕ} (hk : 11 ≤ k) (hkmax : k ≤ 50) :
    (k : ℝ) / Real.pi + afeDirectMaximum (afeBandLower k) 10000000000 ≤ (k : ℝ) / Real.pi + 1.1601 ∧
    (k : ℝ) * (1 + afeDelta0 10000000000) / Real.pi + afeReflectedMaximum (afeBandLower k) 10000000000 ≤
      (k : ℝ) / Real.pi + 1.1601 := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_band_coefficients_large_k hk hkmax


/-- The unchanged large-k decimal is certified on the entire stated integer range and consumed by actual source objects. -/
theorem large_k_direct_source {σ t x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 10000000000 ≤ |t|)
    (hk : 11 ≤ k) (hkmax : k ≤ 50) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hyx : y ≤ x)
    (hband : y ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      ((k : ℝ) / Real.pi + 1.1601) * (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_large_k_direct hσ ht hk hkmax hx hy hyx hband hxhalf hyhalf hscale


/-- The unchanged large-k decimal is certified on the entire stated integer range and consumed by actual source objects. -/
theorem large_k_reflected_source {σ t x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 10000000000 ≤ |t|)
    (hk : 11 ≤ k) (hkmax : k ≤ 50) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hxy : x ≤ y)
    (hband : x ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤ ((k : ℝ) / Real.pi + 1.1601) * x ^ (-σ) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_large_k_reflected hσ ht hk hkmax hx hy hxy hband hxhalf hyhalf hscale

/-- The unchanged Table 3 piecewise bound is certified on the entire stated integer range and consumed by actual source objects. -/
theorem table_three_constants_source {k : ℕ} (hk : 11 ≤ k) (hkmax : k ≤ 50) :
    (k : ℝ) / Real.pi + afeDirectMaximum (afeBandLower k) 10000000000 ≤ afeTableThreeConstant k ∧
    (k : ℝ) * (1 + afeDelta0 10000000000) / Real.pi + afeReflectedMaximum (afeBandLower k) 10000000000 ≤
      afeTableThreeConstant k := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_table_three_constants hk hkmax


/-- The unchanged Table 3 piecewise bound is certified on the entire stated integer range and consumed by actual source objects. -/
theorem table_three_direct_source {σ t x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 10000000000 ≤ |t|)
    (hk : 11 ≤ k) (hkmax : k ≤ 50) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hyx : y ≤ x)
    (hband : y ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      (afeTableThreeConstant k) * (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_table_three_direct hσ ht hk hkmax hx hy hyx hband hxhalf hyhalf hscale


/-- The unchanged Table 3 piecewise bound is certified on the entire stated integer range and consumed by actual source objects. -/
theorem table_three_reflected_source {σ t x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 10000000000 ≤ |t|)
    (hk : 11 ≤ k) (hkmax : k ≤ 50) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hxy : x ≤ y)
    (hband : x ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤ (afeTableThreeConstant k) * x ^ (-σ) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using afe_table_three_reflected hσ ht hk hkmax hx hy hxy hband hxhalf hyhalf hscale


/-- A displayed Table 1 maximum is refuted by an actual sigma-one source value. -/
theorem table_one_two_pi_direct_rounding_fails_source :
    (2.265204 : ℝ) < afeDirectMaximum (3 / 2) (2 * Real.pi) := by
  exact table_one_two_pi_direct_rounding_fails

/-- A displayed Table 1 maximum is refuted by an actual sigma-one source value. -/
theorem table_one_thousand_direct_rounding_fails_source :
    (1.792736 : ℝ) < afeDirectMaximum (3 / 2) 1000 := by
  exact table_one_thousand_direct_rounding_fails

/-- A displayed Table 1 maximum is refuted by an actual sigma-one source value. -/
theorem table_one_large_direct_rounding_fails_source :
    (1.750701 : ℝ) < afeDirectMaximum (3 / 2) 10000000000 := by
  exact table_one_large_direct_rounding_fails
/-- The proposed outward Table 2 bound is certified on the entire stated integer range and consumed by actual source objects. -/
theorem proposed_table_two_constants_source {k : ℕ} (hk : 1 ≤ k) (hkmax : k ≤ 10) :
    (k : ℝ) / Real.pi + afeDirectMaximum (afeBandLower k) 10000000000 ≤ proposedTableTwoDirect k ∧
    (k : ℝ) * (1 + afeDelta0 10000000000) / Real.pi + afeReflectedMaximum (afeBandLower k) 10000000000 ≤
      proposedTableTwoReflected k := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using proposed_table_two_constants hk hkmax


/-- The proposed outward Table 2 bound is certified on the entire stated integer range and consumed by actual source objects. -/
theorem proposed_table_two_direct_source {σ t x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 10000000000 ≤ |t|)
    (hk : 1 ≤ k) (hkmax : k ≤ 10) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hyx : y ≤ x)
    (hband : y ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      (proposedTableTwoDirect k) * (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using proposed_table_two_direct hσ ht hk hkmax hx hy hyx hband hxhalf hyhalf hscale


/-- The proposed outward Table 2 bound is certified on the entire stated integer range and consumed by actual source objects. -/
theorem proposed_table_two_reflected_source {σ t x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 10000000000 ≤ |t|)
    (hk : 1 ≤ k) (hkmax : k ≤ 10) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hxy : x ≤ y)
    (hband : x ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤ (proposedTableTwoReflected k) * x ^ (-σ) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using proposed_table_two_reflected hσ ht hk hkmax hx hy hxy hband hxhalf hyhalf hscale


/-- The actual global chi excess consumes the exact rational certificate over the whole source strip. -/
theorem chi_table_two_pi_source : afeDelta0 (2 * Real.pi) ≤ 596193 / 10000000 := by
  exact afeDelta0_le_two_pi_table

/-- The actual global chi excess consumes the exact rational certificate over the whole source strip. -/
theorem chi_table_thousand_source : afeDelta0 (1000) ≤ 3692901 / 10000000000 := by
  exact afeDelta0_le_thousand_table

/-- The actual global chi excess consumes the exact rational certificate over the whole source strip. -/
theorem chi_table_large_source : afeDelta0 (10000000000) ≤ 923147 / 25000000000000000 := by
  exact afeDelta0_le_large_table

/-- The actual global chi excess consumes the exact rational certificate over the whole source strip. -/
theorem chi_table_trillion_source : afeDelta0 (3000000000000) ≤ 1230863 / 10000000000000000000 := by
  exact afeDelta0_le_trillion_table

/-- The proposed table certificate is consumed at the full source domain with exact cutoffs and actual polynomials. -/
theorem proposed_table_one_constants_source {r : ℕ} (hr : r ≤ 3) :
    afeDirectMaximum (3 / 2) (tableOneHeight r) ≤ proposedTableOneDirect r ∧
    afeReflectedMaximum (3 / 2) (tableOneHeight r) ≤ proposedTableOneReflected r ∧
    afeDirectMaximum (tableOneSymmetricCutoff r) (tableOneHeight r) ≤ proposedTableOneSymmetric r ∧
    afeDelta0 (tableOneHeight r) ≤ proposedTableOneDelta r := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using proposed_table_one_constants hr


/-- The proposed table certificate is consumed at the full source domain with exact cutoffs and actual polynomials. -/
theorem table_one_symmetric_cutoff_eq_source_source {r : ℕ} (hr : r ≤ 3) :
    tableOneSymmetricCutoff r = (⌊Real.sqrt (tableOneHeight r / (2 * Real.pi))⌋₊ : ℝ) + 1 / 2 := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using table_one_symmetric_cutoff_eq_source hr


/-- The proposed table certificate is consumed at the full source domain with exact cutoffs and actual polynomials. -/
theorem proposed_table_one_direct_source {σ t x y : ℝ} {r : ℕ} (hr : r ≤ 3)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : tableOneHeight r ≤ |t|)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2) (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2)
    (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      (Real.log y / Real.pi + proposedTableOneDirect r) *
        (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using proposed_table_one_direct hr hσ ht hx hy hyx hxhalf hyhalf hscale


/-- The proposed table certificate is consumed at the full source domain with exact cutoffs and actual polynomials. -/
theorem proposed_table_one_reflected_source {σ t x y : ℝ} {r : ℕ} (hr : r ≤ 3)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : tableOneHeight r ≤ |t|)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x ≤ y)
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2) (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2)
    (hscale : 2 * Real.pi * x * y = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      ((1 + proposedTableOneDelta r) / Real.pi * Real.log x + proposedTableOneReflected r) * x ^ (-σ) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using proposed_table_one_reflected hr hσ ht hx hy hxy hxhalf hyhalf hscale


/-- The proposed table certificate is consumed at the full source domain with exact cutoffs and actual polynomials. -/
theorem proposed_table_one_symmetric_source {σ t x : ℝ} {r : ℕ} (hr : r ≤ 3)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : tableOneHeight r ≤ |t|) (hx : 1 ≤ x)
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * x = |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) - chi ((σ : ℂ) + (t : ℂ) * Complex.I) * (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1))‖ ≤
      (Real.log x / Real.pi + proposedTableOneSymmetric r) * x ^ (-σ) := by
  simpa only [afeRemainder, sharpZetaSum, zetaTerm, neg_sub] using proposed_table_one_symmetric hr hσ ht hx hxhalf hscale

/-- The exact repaired Part-II conclusion consumes analytic inputs and retains the actual sum. -/
theorem second_poisson_from_shift_inputs_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (r : PartIRegularityAt f g a b N)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hg : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv g) u)
    (hgc : ContinuousOn (deriv (deriv g)) (Set.Icc a b))
    (hfa : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hgn : ∀ u ∈ Set.Icc a b, 0 ≤ deriv (deriv g) u)
    (hga : AntitoneOn (deriv (deriv g)) (Set.Icc a b))
    (hq : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ n : ℕ, AntitoneOn (fun u => |deriv h u| / (((n : ℝ) + 1) + deriv f u - N) ^ 2) (Set.Icc a b))
    (hc : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ n : ℕ, AntitoneOn (fun u => |h u * deriv (deriv f) u| /
        (((n : ℝ) + 1) + deriv f u - N) ^ 3) (Set.Icc a b)) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, ((g (n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ)))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      secondPoissonError (phaseShift f N) g a b := by
  simpa only [weightedWave] using second_poisson_from_shift_inputs r hf hfc hg hgc hfa hgn hga hq hc

/-- The exact repaired Part-II conclusion consumes analytic inputs and retains the actual sum. -/
theorem second_poisson_half_from_shift_inputs_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (r : PartIRegularityAt f g a b N)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hg : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv g) u)
    (hgc : ContinuousOn (deriv (deriv g)) (Set.Icc a b))
    (hfa : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hgn : ∀ u ∈ Set.Icc a b, 0 ≤ deriv (deriv g) u)
    (hga : AntitoneOn (deriv (deriv g)) (Set.Icc a b))
    (hq : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ n : ℕ, AntitoneOn (fun u => |deriv h u| / (((n : ℝ) + 1) + deriv f u - N) ^ 2) (Set.Icc a b))
    (hc : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ n : ℕ, AntitoneOn (fun u => |h u * deriv (deriv f) u| /
        (((n : ℝ) + 1) + deriv f u - N) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ 1 - Int.fract (deriv f a)) :
    let F := phaseShift f N
    let y := deriv f a - N
    let M := ⌊deriv f a⌋₊ - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, ((g (n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ)))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH F g b / (4 * Real.pi ^ 2) * halfSecondEndpointBound M (deriv f b - N) +
      secondH F g a / (4 * Real.pi ^ 2) * halfSecondEndpointBound M y +
      secondH1 F g a / (4 * Real.pi ^ 3) * (minusSquareBound M y + plusSquareBound y) +
      (secondH F g a * |deriv (deriv F) a| / (4 * Real.pi ^ 3)) *
        (minusCubeBound M y + plusCubeBound y) := by
  simpa only [weightedWave] using second_poisson_half_from_shift_inputs r hf hfc hg hgc hfa hgn hga hq hc hah hbh hδ

/-- The exact repaired Part-II conclusion consumes analytic inputs and retains the actual sum. -/
theorem partIISquareTailEnvelope_half_offset_source {y : ℝ} (hy : 0 < y)
    (hδ : (⌊y⌋₊ : ℝ) + 1 - y = 1 / 2) :
    partIISquareTailEnvelope y = 46 / 9 +
      (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
        2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y := by
  simpa only [weightedWave] using partIISquareTailEnvelope_half_offset hy hδ

/-- The exact repaired Part-II conclusion consumes analytic inputs and retains the actual sum. -/
theorem partIICubeCoefficient_half_offset_source {y : ℝ} (hy : 0 < y)
    (hδ : (⌊y⌋₊ : ℝ) + 1 - y = 1 / 2) :
    partIICubeCoefficient y = 230 / 27 - (14 / 3) / y +
      (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
        2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
        (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 2 := by
  simpa only [weightedWave] using partIICubeCoefficient_half_offset hy hδ

/-- The exact repaired Part-II conclusion consumes analytic inputs and retains the actual sum. -/
theorem second_poisson_half_offset_from_inputs_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (r : PartIRegularityAt f g a b N)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hg : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv g) u)
    (hgc : ContinuousOn (deriv (deriv g)) (Set.Icc a b))
    (hfa : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hgn : ∀ u ∈ Set.Icc a b, 0 ≤ deriv (deriv g) u)
    (hga : AntitoneOn (deriv (deriv g)) (Set.Icc a b))
    (hq : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ n : ℕ, AntitoneOn (fun u => |deriv h u| / (((n : ℝ) + 1) + deriv f u - N) ^ 2) (Set.Icc a b))
    (hc : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ n : ℕ, AntitoneOn (fun u => |h u * deriv (deriv f) u| /
        (((n : ℝ) + 1) + deriv f u - N) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 - Int.fract (deriv f a) = 1 / 2) :
    let F := phaseShift f N
    let y := deriv f a - N
    let z := deriv f b - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, ((g (n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ)))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH F g b / (4 * Real.pi ^ 2) *
        ((1 / z) * (Real.pi / 2 + 1 / (y + 1 / 2) + Real.log 2 + 3 / (2 * (z + 1)))) +
      secondH F g a / (4 * Real.pi ^ 2) *
        ((1 / y) * (Real.pi / 2 + 1 / (y + 1 / 2) + Real.log 2 + 3 / (2 * (y + 1)))) +
      secondH1 F g a / (4 * Real.pi ^ 3) *
        ((46 / 9) / y + (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
          2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y ^ 2) +
      (secondH F g a * |deriv (deriv F) a| / (4 * Real.pi ^ 3)) *
        ((230 / 27) / y - (14 / 3) / y ^ 2 +
          (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
            2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
            (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 3) := by
  simpa only [weightedWave] using second_poisson_half_offset_from_inputs r hf hfc hg hgc hfa hgn hga hq hc hah hbh hδ

/-- The exact source quantity is checked independently of its implementation proof. -/
theorem quadratic_taylor_remainder_bound_source {f : ℝ → ℝ} {c x D : ℝ}
    (hf : ∀ u ∈ Set.uIcc c x, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.uIcc c x, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.uIcc c x, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ Set.uIcc c x, |deriv (deriv (deriv f)) u| ≤ D) :
    |f x - f c - (x - c) * deriv f c - (x - c) ^ 2 * deriv (deriv f) c / 2| ≤
      D * |x - c| ^ 3 / 6 := by
  simpa only [stationaryTaylorError] using quadratic_taylor_remainder_bound hf hf' hf'' hD

/-- The exact source quantity is checked independently of its implementation proof. -/
theorem derivative_taylor_remainder_bound_source {f : ℝ → ℝ} {c x D : ℝ}
    (hf' : ∀ u ∈ Set.uIcc c x, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.uIcc c x, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ Set.uIcc c x, |deriv (deriv (deriv f)) u| ≤ D) :
    |deriv f x - deriv f c - (x - c) * deriv (deriv f) c| ≤ D * |x - c| ^ 2 / 2 := by
  simpa only [stationaryTaylorError] using derivative_taylor_remainder_bound hf' hf'' hD

/-- The exact source quantity is checked independently of its implementation proof. -/
theorem stationaryTaylorError_exp_bound_source {f : ℝ → ℝ} {c x D : ℝ}
    (hf : ∀ u ∈ Set.uIcc c (c + x), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.uIcc c (c + x), DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.uIcc c (c + x), DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ Set.uIcc c (c + x), |deriv (deriv (deriv f)) u| ≤ D) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - f c - x * deriv f c - x ^ 2 * deriv (deriv f) c / 2 : ℝ) : ℂ)) - 1‖ ≤
      Real.pi * D * |x| ^ 3 / 3 := by
  simpa only [stationaryTaylorError] using stationaryTaylorError_exp_bound hf hf' hf'' hD

/-- The exact source quantity is checked independently of its implementation proof. -/
theorem stationary_phase_factorization_source {f : ℝ → ℝ} {c ν : ℝ} (hc : deriv f c = ν) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((deriv (deriv f) c * x ^ 2 / 2 : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - f c - x * deriv f c - x ^ 2 * deriv (deriv f) c / 2 : ℝ) : ℂ)) := by
  simpa only [stationaryTaylorError] using stationary_phase_factorization hc x

/-- The exact source quantity is checked independently of its implementation proof. -/
theorem interior_reciprocal_bound_fails_source :
    2 / Real.pi * Real.log ((5 / 2 : ℝ) - 99 / 100) + 1.251 <
      ∑ ν ∈ Finset.Icc 1 (⌊(5 / 2 : ℝ)⌋₊ - 1),
        (1 / Real.pi) * (1 / |(5 / 2 : ℝ) - ν| + 1 / |(ν : ℝ) - 99 / 100|) := by
  simpa only [stationaryTaylorError] using BProcessReview.interior_reciprocal_bound_fails

/-- The exact source quantity is checked independently of its implementation proof. -/
theorem omitted_stationary_term_norm_source (f : ℝ → ℝ) (ξ : ℕ → ℝ) {M : ℕ} (hM : 1 ≤ M) :
    ‖(∑ ν ∈ Finset.Icc 1 M,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - ν * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)) -
      ∑ ν ∈ Finset.Icc 1 (M - 1),
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - ν * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ = 1 / Real.sqrt |deriv (deriv f) (ξ M)| := by
  simpa only [stationaryTaylorError] using BProcessReview.omitted_stationary_term_norm f ξ hM


/-- The exact central integral estimate retains the genuine nonlinear phase and error constant. -/
theorem stationary_perturbation_integral_bound_source {g : ℝ → ℝ} {κ δ D : ℝ}
    (hκ : κ ≠ 0) (hδ : 0 < δ)
    (hd : ∀ x ∈ Set.Icc (-δ) δ, DifferentiableAt ℝ g x)
    (hg : ∀ x ∈ Set.Icc (-δ) δ, |g x| ≤ D * |x| ^ 3 / 6)
    (hg' : ∀ x ∈ Set.Icc (-δ) δ, |deriv g x| ≤ D * |x| ^ 2 / 2) :
    ‖∫ x in (-δ)..δ,
      Complex.exp (Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) ^ 2) *
        (Complex.exp (2 * Real.pi * Complex.I * (g x : ℂ)) - 1)‖ ≤ D * δ ^ 2 / |κ| := by
  simpa only [stationaryTaylorError] using stationary_perturbation_integral_bound hκ hδ hd hg hg'

/-- The exact central integral estimate retains the genuine nonlinear phase and error constant. -/
theorem stationary_taylor_integral_bound_source {f : ℝ → ℝ} {c δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c ≠ 0)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv (deriv f)) u| ≤ D) :
    ‖∫ x in (-δ)..δ,
      Complex.exp (Real.pi * Complex.I * ((deriv (deriv f) c : ℝ) : ℂ) * (x : ℂ) ^ 2) *
        (Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - f c - x * deriv f c - x ^ 2 * deriv (deriv f) c / 2 : ℝ) : ℂ)) - 1)‖ ≤
      D * δ ^ 2 / |deriv (deriv f) c| := by
  simpa only [stationaryTaylorError] using stationary_taylor_integral_bound hδ hκ hf hf' hf'' hD

/-- The exact central integral estimate retains the genuine nonlinear phase and error constant. -/
theorem stationary_centered_window_bound_source {f : ℝ → ℝ} {c ν δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c ≠ 0) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ x in (-δ)..δ,
        Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c : ℝ) : ℂ)) *
        ∫ x in (-δ)..δ,
          Complex.exp (Real.pi * Complex.I * ((deriv (deriv f) c : ℝ) : ℂ) * (x : ℂ) ^ 2)‖ ≤
      D * δ ^ 2 / |deriv (deriv f) c| := by
  simpa only [stationaryTaylorError] using stationary_centered_window_bound hδ hκ hc hf hf' hf'' hD


/-- The sharp actual quadratic integral keeps both endpoint scales and the source phase. -/
theorem norm_fresnel_finite_tail_sharp_source {ρ a b : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (ρ : ℂ) * (x : ℂ) ^ 2)‖ ≤
      1 / (2 * ρ * a) + 1 / (2 * ρ * b) := by
  exact norm_fresnel_finite_tail_sharp hρ ha hab

/-- The sharp actual quadratic integral keeps both endpoint scales and the source phase. -/
theorem quadratic_stationary_phase_sharp_source (A : ℝ) {κ H : ℝ} (hκ : κ < 0) (hH : 0 < H) :
    ‖(∫ v in (-H)..H,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((A + κ * v ^ 2 / 2 : ℝ) : ℂ))) -
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((A - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |κ| : ℂ)‖ ≤ 1 / (Real.pi * |κ| * H) := by
  exact quadratic_stationary_phase_sharp A hκ hH


/-- The actual interval and main term are retained with the explicit window-placement hypotheses. -/
theorem stationary_central_fresnel_bound_source {f : ℝ → ℝ} {c ν δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c < 0) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in (c - δ)..(c + δ),
        Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      D * δ ^ 2 / |deriv (deriv f) c| + 1 / (Real.pi * |deriv (deriv f) c| * δ) := by
  exact stationary_central_fresnel_bound hδ hκ hc hf hf' hf'' hD

/-- The actual interval and main term are retained with the explicit window-placement hypotheses. -/
theorem stationary_interval_bound_of_window_source {f : ℝ → ℝ} {a b c ν δ D ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (ha : a ≤ c - δ) (hb : c + δ ≤ b)
    (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      D * δ ^ 2 / ℓ + 3 / (Real.pi * ℓ * δ) := by
  exact stationary_interval_bound_of_window hδ hℓ ha hb hc hf hf' hf'' hcurv hD

/-- The actual interval and main term are retained with the explicit window-placement hypotheses. -/
theorem stationary_interval_source_constant_of_window_source {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hD : 0 < D) (hℓ : 0 < ℓ)
    (ha : a ≤ c - (3 / (Real.pi * D)) ^ (1 / 3 : ℝ))
    (hb : c + (3 / (Real.pi * D)) ^ (1 / 3 : ℝ) ≤ b)
    (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hthird : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ := by
  exact stationary_interval_source_constant_of_window hD hℓ ha hb hc hf hf' hf'' hcurv hthird


/-- The actual asymmetric integral and endpoint-frequency gaps remain explicit. -/
theorem quadratic_asymmetric_stationary_sharp_source (A : ℝ) {κ a b : ℝ}
    (hκ : κ < 0) (ha : a < 0) (hb : 0 < b) :
    ‖(∫ x in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((A + κ * x ^ 2 / 2 : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((A - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |κ| : ℂ)‖ ≤
      1 / (2 * Real.pi * |κ| * (-a)) + 1 / (2 * Real.pi * |κ| * b) := by
  exact quadratic_asymmetric_stationary_sharp A hκ ha hb

/-- The actual asymmetric integral and endpoint-frequency gaps remain explicit. -/
theorem stationary_zero_third_endpoint_bound_source {f : ℝ → ℝ} {a b c ν : ℝ}
    (ha : a < c) (hb : c < b) (hc : deriv f c = ν) (hκ : deriv (deriv f) c < 0)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hthird : ∀ u ∈ Set.Icc a b, deriv (deriv (deriv f)) u = 0) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      1 / (2 * Real.pi) * (1 / |deriv f a - ν| + 1 / |deriv f b - ν|) := by
  exact stationary_zero_third_endpoint_bound ha hb hc hκ hf hf' hf'' hthird


/-- The exact source-facing statement checks genuine derivatives, intervals and the constructed extension. -/
theorem quadratic_taylor_remainder_lipschitz_source {f : ℝ → ℝ} {c x D : ℝ}
    (hf : ∀ u ∈ Set.uIcc c x, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.uIcc c x, DifferentiableAt ℝ (deriv f) u)
    (hL : ∀ u ∈ Set.uIcc c x, |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    |f x - f c - (x - c) * deriv f c - (x - c) ^ 2 * deriv (deriv f) c / 2| ≤
      D * |x - c| ^ 3 / 6 := by
  simpa only [extendedPhase, extendedSlope, extendedCurvature] using quadratic_taylor_remainder_lipschitz hf hf' hL

/-- The exact source-facing statement checks genuine derivatives, intervals and the constructed extension. -/
theorem stationary_lipschitz_interval_window_source {f : ℝ → ℝ} {a b c ν δ D ℓ : ℝ}
    (hDn : 0 ≤ D) (hδ : 0 < δ) (hℓ : 0 < ℓ) (ha : a ≤ c - δ) (hb : c + δ ≤ b)
    (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hL : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      D * δ ^ 2 / ℓ + 3 / (Real.pi * ℓ * δ) := by
  simpa only [extendedPhase, extendedSlope, extendedCurvature] using stationary_lipschitz_interval_window hDn hδ hℓ ha hb hc hf hf' hcurv hL

/-- The exact source-facing statement checks genuine derivatives, intervals and the constructed extension. -/
theorem extendedPhase_eq_source {f : ℝ → ℝ} {a b c x : ℝ} (hab : a ≤ b)
    (hc : c ∈ Set.Icc a b) (hx : x ∈ Set.Icc a b)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b)) :
    f c + ∫ u in c..x, (deriv f c + ∫ v in c..u, deriv (deriv f) (Set.projIcc a b hab v)) = f x := by
  simpa only [extendedPhase, extendedSlope, extendedCurvature] using extendedPhase_eq hab hc hx hf hf' hfc

/-- The exact source-facing statement checks genuine derivatives, intervals and the constructed extension. -/
theorem extendedCurvature_lipschitz_source {f : ℝ → ℝ} {a b D : ℝ} (hab : a ≤ b)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) (x y : ℝ) :
    |deriv (deriv f) (Set.projIcc a b hab x) - deriv (deriv f) (Set.projIcc a b hab y)| ≤ D * |x - y| := by
  simpa only [extendedPhase, extendedSlope, extendedCurvature] using extendedCurvature_lipschitz hab hf'' hD x y

/-- The exact source-facing statement checks genuine derivatives, intervals and the constructed extension. -/
theorem stationary_phase_source_scales_source {f : ℝ → ℝ} {a b c ν h₃ ℓ₂ ℓ₃ : ℝ}
    (hℓ₂ : 0 < ℓ₂) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃)
    (ha : a < c) (hb : c < b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ₂)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₃ ^ (1 / 3 : ℝ) *
        ℓ₃ ^ (1 / 3 : ℝ) / ℓ₂ +
        1 / Real.pi * (1 / |deriv f a - ν| + 1 / |deriv f b - ν|) := by
  simpa only [extendedPhase, extendedSlope, extendedCurvature] using stationary_phase_source_scales hℓ₂ hℓ₃ hh₃ ha hb hc hf hf' hf'' hcurv hD

/-- The exact source-facing statement checks genuine derivatives, intervals and the constructed extension. -/
theorem exists_stationary_phase_bound_source {f : ℝ → ℝ} {a b ν D ℓ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hνa : ν < deriv f a) (hνb : deriv f b < ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ c ∈ Set.Ioo a b, deriv f c = ν ∧
      ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
        Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ +
          1 / Real.pi * (1 / |deriv f a - ν| + 1 / |deriv f b - ν|) := by
  simpa only [extendedPhase, extendedSlope, extendedCurvature] using exists_stationary_phase_bound hab hℓ hνa hνb hf hf' hf'' hcurv hD

/-- The actual frequency sum, stationary main terms and endpoint gaps remain explicit. -/
theorem stationary_sum_bound_source {f : ℝ → ℝ} {a b D ℓ : ℝ} (S : Finset ℕ) (ξ : ℕ → ℝ)
    (hℓ : 0 < ℓ)
    (hξ : ∀ ν ∈ S, ξ ν ∈ Set.Ioo a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ S, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ S, Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      (S.card : ℝ) * ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) +
        1 / Real.pi * ∑ ν ∈ S, (1 / |deriv f a - (ν : ℝ)| + 1 / |deriv f b - (ν : ℝ)|) := by
  exact stationary_sum_bound S ξ hℓ hξ hf hf' hf'' hcurv hD

/-- The actual frequency sum, stationary main terms and endpoint gaps remain explicit. -/
theorem stationary_interior_sum_bound_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hξ : ∀ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        1 / Real.pi * ∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
          (1 / |deriv f a - (ν : ℝ)| + 1 / |deriv f b - (ν : ℝ)|) := by
  exact stationary_interior_sum_bound ξ hab hℓ hαpos hα hξ hf hf' hf'' hcurv hupper hD

/-- The exact frequency sum and derivative gaps preserve the explicitly stated domain. -/
theorem stationary_reciprocal_sum_eq_source (N : ℕ) {α β : ℝ}
    (hα : α < 1) (hβ : (N : ℝ) < β) :
    (∑ ν ∈ Finset.Icc 1 N, (1 / |β - (ν : ℝ)| + 1 / |α - (ν : ℝ)|)) =
      (Complex.digamma (β : ℂ)).re - (Complex.digamma ((β - (N : ℝ) : ℝ) : ℂ)).re +
        (Complex.digamma (((N : ℝ) + 1 - α : ℝ) : ℂ)).re -
          (Complex.digamma ((1 - α : ℝ) : ℂ)).re := by
  exact stationary_reciprocal_sum_eq N hα hβ

/-- The exact frequency sum and derivative gaps preserve the explicitly stated domain. -/
theorem stationary_interior_digamma_bound_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hξ : ∀ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        1 / Real.pi * (
          (Complex.digamma ((deriv f a : ℝ) : ℂ)).re -
            (Complex.digamma ((deriv f a - (⌊deriv f a⌋₊ - 1 : ℕ) : ℝ) : ℂ)).re +
          (Complex.digamma (((⌊deriv f a⌋₊ - 1 : ℕ) + 1 - deriv f b : ℝ) : ℂ)).re -
            (Complex.digamma ((1 - deriv f b : ℝ) : ℂ)).re) := by
  exact stationary_interior_digamma_bound ξ hab hℓ hαpos hα hξ hf hf' hf'' hcurv hupper hD

/-- The exact frequency sum and derivative gaps preserve the explicitly stated domain. -/
theorem stationary_interior_log_bound_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b ≤ 1 / 2) (hβ : 1 ≤ deriv f a)
    (hξ : ∀ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        (2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251) := by
  exact stationary_interior_log_bound ξ hab hℓ hαpos hα hβ hξ hf hf' hf'' hcurv hupper hD

/-- Actual source derivatives construct the full stationary family and bound its interior integral sum. -/
theorem exists_stationary_interior_digamma_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        1 / Real.pi * (
          (Complex.digamma ((deriv f a : ℝ) : ℂ)).re -
            (Complex.digamma ((deriv f a - (⌊deriv f a⌋₊ - 1 : ℕ) : ℝ) : ℂ)).re +
          (Complex.digamma (((⌊deriv f a⌋₊ - 1 : ℕ) + 1 - deriv f b : ℝ) : ℂ)).re -
            (Complex.digamma ((1 - deriv f b : ℝ) : ℂ)).re) := by
  exact exists_stationary_interior_digamma hab hℓ hαpos hα hf hf' hf'' hanti hlower hupper hD

/-- Actual source derivatives construct the full stationary family and bound its interior integral sum. -/
theorem exists_stationary_interior_log_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b ≤ 1 / 2) (hβ : 1 ≤ deriv f a)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        (2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251) := by
  exact exists_stationary_interior_log hab hℓ hαpos hα hβ hf hf' hf'' hanti hlower hupper hD

/-- The actual finite Fresnel or quadratic integral carries its certified uniform decimal. -/
theorem norm_fresnel_segment_le_all_source (x : ℝ) :
    ‖∫ t in (0 : ℝ)..x, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤ 119 / 100 := by
  exact norm_fresnel_segment_le_all x

/-- The actual finite Fresnel or quadratic integral carries its certified uniform decimal. -/
theorem quadratic_integral_bound_1343_source (A a b : ℝ) {κ : ℝ} (hκ : κ < 0) :
    ‖∫ t in a..b, Complex.exp (2 * Real.pi * Complex.I * ((A + κ * t ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      1.343 / Real.sqrt |κ| := by
  exact quadratic_integral_bound_1343 A a b hκ

/-- The actual finite Fresnel or quadratic integral carries its certified uniform decimal. -/
theorem quadratic_cos_prefix_le_source (θ x : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ t in (0 : ℝ)..x, Real.cos (θ + ρ * t ^ 2)) ≤ 119 / (100 * Real.sqrt ρ) := by
  exact quadratic_cos_prefix_le θ x hρ

/-- The actual source phase and frequency sum retain their proved curvature constant. -/
theorem norm_positive_curvature_integral_source {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u) :
    ‖∫ u in a..b, Complex.exp ((f u : ℂ) * Complex.I)‖ ≤ 119 / (50 * Real.sqrt (ℓ / 2)) := by
  exact norm_positive_curvature_integral hab hℓ hf hf' hcurv

/-- The actual source phase and frequency sum retain their proved curvature constant. -/
theorem kershner_integral_bound_source {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) (ν : ℝ) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      1.343 / Real.sqrt ℓ := by
  exact kershner_integral_bound hab hℓ hf hf' hfc hcurv ν

/-- The actual source phase and frequency sum retain their proved curvature constant. -/
theorem kershner_integral_source_source {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a < b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|) (ν : ℝ) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      1.343 / Real.sqrt ℓ := by
  exact kershner_integral_source hab hℓ hf hf' hf'' hanti hlower ν

/-- The actual source phase and frequency sum retain their proved curvature constant. -/
theorem kershner_boundary_integrals_source {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a < b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|) (M : ℕ) :
    ‖(∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      (∑ ν ∈ Finset.Icc 1 (M - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ)))‖ ≤
      2.686 / Real.sqrt ℓ := by
  exact kershner_boundary_integrals hab hℓ hf hf' hf'' hanti hlower M

/-- Exact source objects retain the one-sided constant and all endpoint frequencies. -/
theorem kershner_monotone_bound_source {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) (ν : ℝ)
    (hside : (∀ u ∈ Set.Icc a b, ν ≤ deriv f u) ∨ (∀ u ∈ Set.Icc a b, deriv f u ≤ ν)) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      0.6715 / Real.sqrt ℓ := by
  exact kershner_monotone_bound hab hℓ hf hf' hfc hcurv ν hside

/-- Exact source objects retain the one-sided constant and all endpoint frequencies. -/
theorem kershner_boundary_positive_source {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a < b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b)) (hpos : 0 ≤ deriv f b)
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|) (M : ℕ) :
    ‖(∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      (∑ ν ∈ Finset.Icc 1 (M - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ)))‖ ≤
      2.0145 / Real.sqrt ℓ := by
  exact kershner_boundary_positive hab hℓ hf hf' hf'' hanti hpos hlower M

/-- Exact source objects retain the one-sided constant and all endpoint frequencies. -/
theorem stationary_phase_gap_bound_source {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ +
        (if deriv f a - ν = 0 then 0.6715 / Real.sqrt ℓ else min (0.6715 / Real.sqrt ℓ) (1 / (Real.pi * |deriv f a - ν|))) + (if deriv f b - ν = 0 then 0.6715 / Real.sqrt ℓ else min (0.6715 / Real.sqrt ℓ) (1 / (Real.pi * |deriv f b - ν|))) := by
  simpa only [stationaryEndpointCap] using stationary_phase_gap_bound hℓ ha hb hc hf hf' hf'' hcurv hD

/-- Exact source objects retain the one-sided constant and all endpoint frequencies. -/
theorem exists_full_stationary_gap_bound_source {f : ℝ → ℝ} {a b D ℓ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      0.6715 / Real.sqrt ℓ + (⌊deriv f a⌋₊ : ℝ) *
        ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) +
        ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
          ((if deriv f a - (ν : ℝ) = 0 then 0.6715 / Real.sqrt ℓ else min (0.6715 / Real.sqrt ℓ) (1 / (Real.pi * |deriv f a - (ν : ℝ)|))) + (if deriv f b - (ν : ℝ) = 0 then 0.6715 / Real.sqrt ℓ else min (0.6715 / Real.sqrt ℓ) (1 / (Real.pi * |deriv f b - (ν : ℝ)|)))) := by
  simpa only [stationaryEndpointCap] using exists_full_stationary_gap_bound hab hℓ hαpos hα hf hf' hf'' hanti hlower hD

/-- The actual phase integral and stationary main term retain their uniform curvature error. -/
theorem norm_positive_half_sub_main_source {f : ℝ → ℝ} {a b ℓ A : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hpos : ∀ u ∈ Set.Icc a b, 0 ≤ deriv f u)
    (hcurv : ∀ u ∈ Set.Icc a b, 2 * Real.pi * ℓ ≤ deriv (deriv f) u) (ha : f a = 0)
    (hA : 0 ≤ A) (hAmax : A ≤ 1 / (2 * Real.sqrt ℓ)) :
    ‖(∫ u in a..b, Complex.exp ((f u : ℂ) * Complex.I)) -
      (A : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ ≤ 0.928 / Real.sqrt ℓ := by
  exact norm_positive_half_sub_main hab hℓ hf hf' hpos hcurv ha hA hAmax

/-- The actual phase integral and stationary main term retain their uniform curvature error. -/
theorem stationary_right_uniform_source {f : ℝ → ℝ} {a b ℓ ν A : ℝ}
    (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) (hslope : deriv f a ≤ ν)
    (hA : 0 ≤ A) (hAmax : A ≤ 1 / (2 * Real.sqrt ℓ)) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      (A : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((f a - ν * a - 1 / 8 : ℝ) : ℂ))‖ ≤
      0.928 / Real.sqrt ℓ := by
  exact stationary_right_uniform hab hℓ hf hf' hfc hcurv hslope hA hAmax

/-- The actual phase integral and stationary main term retain their uniform curvature error. -/
theorem stationary_uniform_bound_source {f : ℝ → ℝ} {a b c ℓ ν : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤ 1.856 / Real.sqrt ℓ := by
  exact stationary_uniform_bound hℓ ha hb hc hf hf' hfc hcurv

/-- The actual stationary half and endpoint frequency keep their exact nonlinear coefficient. -/
theorem stationary_half_fresnel_lipschitz_source {f : ℝ → ℝ} {c ν δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c < 0) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hL : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    ‖(∫ u in c..(c + δ),
        Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ) / 2‖ ≤
      D * δ ^ 2 / (2 * |deriv (deriv f) c|) + 1 / (2 * Real.pi * |deriv (deriv f) c| * δ) := by
  exact stationary_half_fresnel_lipschitz hδ hκ hc hf hf' hL

/-- The actual stationary half and endpoint frequency keep their exact nonlinear coefficient. -/
theorem stationary_right_phase_bound_source {f : ℝ → ℝ} {a b ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (hab : a ≤ b) (ha : deriv f a = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f a - ν * a - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) a| : ℂ) / 2‖ ≤
      ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        stationaryEndpointCap ℓ (deriv f b - ν) := by
  exact stationary_right_phase_bound hℓ hab ha hf hf' hf'' hcurv hD

/-- The actual stationary half and endpoint frequency keep their exact nonlinear coefficient. -/
theorem stationary_left_phase_bound_source {f : ℝ → ℝ} {a b ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (hab : a ≤ b) (hb : deriv f b = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f b - ν * b - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) b| : ℂ) / 2‖ ≤
      ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        stationaryEndpointCap ℓ (deriv f a - ν) := by
  exact stationary_left_phase_bound hℓ hab hb hf hf' hf'' hcurv hD

/-- The actual stationary half and endpoint frequency keep their exact nonlinear coefficient. -/
theorem stationary_error_drop_left_source {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        0.928 / Real.sqrt ℓ + stationaryEndpointCap ℓ (deriv f b - ν) := by
  exact stationary_error_drop_left hℓ ha hb hc hf hf' hf'' hcurv hD

/-- The actual stationary half and endpoint frequency keep their exact nonlinear coefficient. -/
theorem stationary_error_drop_right_source {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        0.928 / Real.sqrt ℓ + stationaryEndpointCap ℓ (deriv f a - ν) := by
  exact stationary_error_drop_right hℓ ha hb hc hf hf' hf'' hcurv hD

/-- Exact-type regression for the complete stationary aggregation proof. -/
theorem stationary_far_caps_log_source {α β ℓ : ℝ} {M : ℕ} (hM : 2 ≤ M)
    (hα : α < 1) (hβ : (M : ℝ) ≤ β) :
    (∑ ν ∈ Finset.Icc 1 (M - 1), stationaryEndpointCap ℓ (β - (ν : ℝ))) +
      (∑ ν ∈ Finset.Icc 2 M, stationaryEndpointCap ℓ (α - (ν : ℝ))) ≤
        2 / Real.pi * Real.log (β - α) + 1.251 := by
  exact DhimanKadiriQuesadaHerrera2026.stationary_far_caps_log hM hα hβ

/-- Exact-type regression for the complete stationary aggregation proof. -/
theorem stationary_small_width_absorb_source {ℓ w : ℝ} (hℓ : 0 < ℓ) (hℓw : ℓ ≤ w) :
    1.856 / Real.sqrt ℓ + 2 / Real.pi ≤
      2.686 / Real.sqrt ℓ + 2 / Real.pi * Real.log w + 1.251 := by
  exact DhimanKadiriQuesadaHerrera2026.stationary_small_width_absorb hℓ hℓw

/-- Exact-type regression for the complete stationary aggregation proof. -/
theorem stationary_full_sum_large_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 := by
  exact DhimanKadiriQuesadaHerrera2026.stationary_full_sum_large ξ hab hℓ hαpos hα hM hξ hf hf' hf'' hanti hlower hupper hD

/-- Exact-type regression for the complete stationary aggregation proof. -/
theorem stationary_full_sum_bound_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hlen : 1 ≤ b - a)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 := by
  exact DhimanKadiriQuesadaHerrera2026.stationary_full_sum_bound ξ hab hℓ hαpos hα hlen hξ hf hf' hf'' hanti hlower hupper hD

/-- Exact-type regression for the complete stationary aggregation proof. -/
theorem exists_source_stationary_transform_source {f : ℝ → ℝ} {a b ℓ₂ ℓ₃ h₂ h₃ : ℝ}
    (hab : a < b) (hℓ₂ : 0 < ℓ₂) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ₂ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ₂)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ₂ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 := by
  exact DhimanKadiriQuesadaHerrera2026.exists_source_stationary_transform hab hℓ₂ hℓ₃ hh₃ hαpos hα hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact-type regression preserving the actual discrete sum and all Poisson inputs. -/
theorem exists_b_process_partI_source {f : ℝ → ℝ} {a b ℓ₂ ℓ₃ h₂ h₃ : ℝ}
    (hab : a < b) (hℓ₂ : 0 < ℓ₂) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ₂ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ₂)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ₂ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 +
      (1 / Real.pi) *
        (Real.log (1 + deriv f a) + Real.log (1 + (⌊deriv f a⌋₊ : ℝ)) +
          Real.eulerMascheroniConstant - 1 / (2 * (1 + (⌊deriv f a⌋₊ : ℝ))) -
            1 / (2 * (1 + deriv f a)) -
              (Complex.digamma ((1 - Int.fract (deriv f a) : ℝ) : ℂ)).re +
                Real.log 2 + 1 / deriv f a) := by
  exact DhimanKadiriQuesadaHerrera2026.exists_b_process_partI hab hℓ₂ hℓ₃ hh₃ hαpos hα hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact-type regression preserving the actual discrete sum and all Poisson inputs. -/
theorem exists_b_process_partII_source {f : ℝ → ℝ} {a b ℓ₂ ℓ₃ h₂ h₃ : ℝ}
    (r : SecondOrderRegularity f (fun _ => 1) a b)
    (hδ : 1 / 2 ≤ (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a)
    (hℓ₂ : 0 < ℓ₂) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ₂ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ₂)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ₂ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 +
      ((Real.log 2 + 1 / (deriv f a)) / Real.pi +
      (deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) + (deriv f a) * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) * (minusSquareBound ⌊deriv f a⌋₊ (deriv f a) + plusSquareBound (deriv f a)) +
      (deriv f a * |deriv (deriv f) a| / (2 * Real.pi ^ 2)) * (minusCubeBound ⌊deriv f a⌋₊ (deriv f a) + plusCubeBound (deriv f a))) := by
  exact DhimanKadiriQuesadaHerrera2026.exists_b_process_partII r hδ hℓ₂ hℓ₃ hh₃ hα hah hbh hf'' hanti hlower hupper hD

/-- Exact-type regression for the source counterexample or the explicit all-δ repair. -/
theorem poisson_half_counterexample_hypotheses :
    ContDiff ℝ 3 PoissonHalfReview.phase ∧ ContinuousOn (deriv PoissonHalfReview.phase) (Set.Icc (1 / 2 : ℝ) (11 / 2)) ∧
    StrictAntiOn (deriv PoissonHalfReview.phase) (Set.Icc (1 / 2 : ℝ) (11 / 2)) ∧
    (∀ u ∈ Set.Icc (1 / 2 : ℝ) (11 / 2), 0 < deriv PoissonHalfReview.phase u) ∧
    (∀ u ∈ Set.Icc (1 / 2 : ℝ) (11 / 2), 0 < |deriv (deriv PoissonHalfReview.phase) u|) ∧
    StrictAntiOn (fun u => |deriv (deriv PoissonHalfReview.phase) u|) (Set.Icc (1 / 2 : ℝ) (11 / 2)) := by
  exact DhimanKadiriQuesadaHerrera2026.PoissonHalfReview.phase_source_hypotheses

/-- Exact-type regression for the source counterexample or the explicit all-δ repair. -/
theorem poisson_half_literal_bound_false :
    ¬ ‖(∑ n ∈ Finset.Ioc ⌊(1 / 2 : ℝ)⌋ ⌊(11 / 2 : ℝ)⌋,
      Complex.exp (2 * Real.pi * Complex.I * (PoissonHalfReview.phase (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 ⌊deriv PoissonHalfReview.phase (1 / 2)⌋₊, ∫ u in (1 / 2 : ℝ)..(11 / 2),
        Complex.exp (2 * Real.pi * Complex.I * ((PoissonHalfReview.phase u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤ PoissonHalfReview.printedBound := by
  exact DhimanKadiriQuesadaHerrera2026.PoissonHalfReview.printed_poisson_bound_false

/-- Exact-type regression for the source counterexample or the explicit all-δ repair. -/
theorem second_endpoint_half_integer_delta_source {M : ℕ} {x y : ℝ}
    (hx : ∃ k : ℤ, x = (k : ℝ) + 1 / 2) (hy : 0 < y) (hM : y < (M : ℝ) + 1) :
    ‖negativeTail M x y‖ + ‖positiveTail (-x) y‖ ≤ halfSecondEndpointDelta M y := by
  exact DhimanKadiriQuesadaHerrera2026.second_endpoint_half_integer_delta hx hy hM

/-- Exact-type regression for the source counterexample or the explicit all-δ repair. -/
theorem second_poisson_shifted_delta_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N)
    (r : SecondOrderRegularity (phaseShift f N) g a b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    :
    let F := phaseShift f N
    let y := deriv f a - N
    let M := ⌊deriv f a⌋₊ - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH F g b / (4 * Real.pi ^ 2) * halfSecondEndpointDelta M (deriv f b - N) +
      secondH F g a / (4 * Real.pi ^ 2) * halfSecondEndpointDelta M y +
      secondH1 F g a / (4 * Real.pi ^ 3) * (minusSquareBound M y + plusSquareBound y) +
      (secondH F g a * |deriv (deriv F) a| / (4 * Real.pi ^ 3)) *
        (minusCubeBound M y + plusCubeBound y) := by
  exact DhimanKadiriQuesadaHerrera2026.second_poisson_shifted_delta h r hah hbh

/-- Exact-type regression for the source counterexample or the explicit all-δ repair. -/
theorem constant_second_poisson_delta_source {f : ℝ → ℝ} {a b : ℝ}
    (r : SecondOrderRegularity f (fun _ => 1) a b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    :
    let y := deriv f a
    let M := ⌊y⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / y) / Real.pi +
      (deriv f b * halfSecondEndpointDelta M (deriv f b) + y * halfSecondEndpointDelta M y) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) * (minusSquareBound M y + plusSquareBound y) +
      (y * |deriv (deriv f) a| / (2 * Real.pi ^ 2)) * (minusCubeBound M y + plusCubeBound y) := by
  exact DhimanKadiriQuesadaHerrera2026.constant_second_poisson_delta r hah hbh

/-- Exact-type regression for the source counterexample or the explicit all-δ repair. -/
theorem exists_b_process_delta_source {f : ℝ → ℝ} {a b ℓ₂ ℓ₃ h₂ h₃ : ℝ}
    (r : SecondOrderRegularity f (fun _ => 1) a b)
    (hℓ₂ : 0 < ℓ₂) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ₂ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ₂)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ₂ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 +
      ((Real.log 2 + 1 / (deriv f a)) / Real.pi +
      (deriv f b * halfSecondEndpointDelta ⌊deriv f a⌋₊ (deriv f b) + (deriv f a) * halfSecondEndpointDelta ⌊deriv f a⌋₊ (deriv f a)) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) * (minusSquareBound ⌊deriv f a⌋₊ (deriv f a) + plusSquareBound (deriv f a)) +
      (deriv f a * |deriv (deriv f) a| / (2 * Real.pi ^ 2)) * (minusCubeBound ⌊deriv f a⌋₊ (deriv f a) + plusCubeBound (deriv f a))) := by
  exact DhimanKadiriQuesadaHerrera2026.exists_b_process_delta r hℓ₂ hℓ₃ hh₃ hα hah hbh hf'' hanti hlower hupper hD

/-- Exact-type regression for the logarithmic application or its sharp stationary input. -/
theorem afePhase_constant_secondOrderRegularity_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b) :
    SecondOrderRegularity (afePhase c) (fun _ => 1) a b := by
  exact DhimanKadiriQuesadaHerrera2026.afePhase_constant_secondOrderRegularity hc ha hab

/-- Exact-type regression for the logarithmic application or its sharp stationary input. -/
theorem afePhase_stationary_term_source {c u ν : ℝ} (hc : 0 < c) (hu : 0 < u) (hν : 0 < ν)
    (hstat : deriv (afePhase c) u = ν) :
    Complex.exp (2 * Real.pi * Complex.I * ((afePhase c u - ν * u - 1 / 8 : ℝ) : ℂ)) /
      (Real.sqrt |deriv (deriv (afePhase c)) u| : ℂ) =
    ((Real.sqrt c / ν : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / ν) - c - 1 / 8 : ℝ) : ℂ)) := by
  exact DhimanKadiriQuesadaHerrera2026.afePhase_stationary_term hc hu hν hstat

/-- Exact-type regression for the logarithmic application or its sharp stationary input. -/
theorem logarithmic_b_process_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) + 1.251 +
      ((Real.log 2 + 1 / (c / a)) / Real.pi +
        ((c / b) * halfSecondEndpointDelta ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointDelta ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) / (2 * Real.pi ^ 2) * (minusSquareBound ⌊c / a⌋₊ (c / a) + plusSquareBound (c / a)) +
        ((c / a) * (c / a ^ 2) / (2 * Real.pi ^ 2)) *
          (minusCubeBound ⌊c / a⌋₊ (c / a) + plusCubeBound (c / a))) := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_b_process hc ha hab hα hah hbh

/-- Exact-type regression for the logarithmic application or its sharp stationary input. -/
theorem stationary_full_sum_sharp_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi := by
  exact DhimanKadiriQuesadaHerrera2026.stationary_full_sum_sharp ξ hab hℓ hαpos hα hM hξ hf hf' hf'' hanti hlower hupper hD

/-- Exact-type regression preserving the literal B-process coefficients on the explicitly restricted logarithmic domain. -/
theorem printed_poisson_gap_absorb_source {β κ : ℝ} (hβ : 2 ≤ β) (hκ : 0 ≤ κ) (hκβ : κ ≤ 2 * β) :
    2 / Real.pi + (Real.log 2 + 1 / β) / (2 * Real.pi) +
      κ / (2 * Real.pi ^ 2) * (partIISquareTailEnvelope β / β - printedPartIIE1 β / β) ≤ 1.251 := by
  exact DhimanKadiriQuesadaHerrera2026.printed_poisson_gap_absorb hβ hκ hκβ

/-- Exact-type regression preserving the literal B-process coefficients on the explicitly restricted logarithmic domain. -/
theorem logarithmic_b_process_printed_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1) (hβ : 2 ≤ c / a)
    (hδ : 1 / 2 ≤ (⌊c / a⌋₊ : ℝ) + 1 - c / a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_b_process_printed hc ha hab hα hβ hδ hah hbh


/-- Exact-type regression for the single-frequency source error and its proved budget. -/
theorem printed_poisson_gap_one_source {β κ : ℝ} (hβ : 1 ≤ β) (hκ : 0 ≤ κ) (hκβ : κ ≤ 2 * β) :
    (Real.log 2 + 1 / β) / (2 * Real.pi) +
      κ / (2 * Real.pi ^ 2) * (partIISquareTailEnvelope β / β - printedPartIIE1 β / β) ≤ 2 / 3 := by
  exact DhimanKadiriQuesadaHerrera2026.printed_poisson_gap_one hβ hκ hκβ

/-- Exact-type regression for the single-frequency source error and its proved budget. -/
theorem stationary_full_sum_one_budget_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b)
    (hlen : 1 ≤ b - a) (hone : ⌊deriv f a⌋₊ = 1)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ + 2 / 3 ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 := by
  exact DhimanKadiriQuesadaHerrera2026.stationary_full_sum_one_budget ξ hab hℓ hαpos hlen hone hξ hf hf' hf'' hanti hlower hupper hD

/-- Exact-type regression for the single-frequency source error and its proved budget. -/
theorem logarithmic_b_process_printed_one_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1) (hone : ⌊c / a⌋₊ = 1)
    (hδ : 1 / 2 ≤ (⌊c / a⌋₊ : ℝ) + 1 - c / a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_b_process_printed_one hc ha hab hα hone hδ hah hbh


/-- Exact-type regression for the genuine logarithmic sums and literal half-offset B-process. -/
theorem logarithmic_range_cancellation_source {c A b : ℝ} {N : ℕ}
    (hc : 0 < c) (hA : 0 < A) (hN : 0 < N) (hAN : A + N ≤ 2 * b)
    (hcA : c / A ≤ 1 / 2) :
    ‖∑ n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (A + n) : ℝ) : ℂ))‖ ≤ 2 * b / c := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_range_cancellation hc hA hN hAN hcA

/-- Exact-type regression for the genuine logarithmic sums and literal half-offset B-process. -/
theorem logarithmic_zero_norm_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hβ : c / a ≤ 1 / 2)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
      Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))‖ ≤
      2 / Real.sqrt (c / b ^ 2) := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_zero_norm hc ha hab hβ hah hbh

/-- Exact-type regression for the genuine logarithmic sums and literal half-offset B-process. -/
theorem logarithmic_b_process_printed_zero_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hzero : ⌊c / a⌋₊ = 0)
    (hδ : 1 / 2 ≤ (⌊c / a⌋₊ : ℝ) + 1 - c / a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_b_process_printed_zero hc ha hab hzero hδ hah hbh

/-- Exact-type regression for the genuine logarithmic sums and literal half-offset B-process. -/
theorem logarithmic_b_process_printed_half_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1)
    (hδ : 1 / 2 ≤ (⌊c / a⌋₊ : ℝ) + 1 - c / a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_b_process_printed_half hc ha hab hα hδ hah hbh


/-- Exact-type regression for the full positive-gap zero-frequency logarithmic source bound. -/
theorem cubic_gap_absorb_source {x δ : ℝ} (hx : 0 < x) (hd : 0 < δ) :
    1 / δ ≤ 2 * x + 1 / (2 * Real.pi ^ 2 * x ^ 2 * δ ^ 3) := by
  exact DhimanKadiriQuesadaHerrera2026.cubic_gap_absorb hx hd

/-- Exact-type regression for the full positive-gap zero-frequency logarithmic source bound. -/
theorem logarithmic_zero_gap_norm_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hβ : c / a < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
      Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))‖ ≤
      max (2 * b / c) (1 / (1 - c / a)) := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_zero_gap_norm hc ha hab hβ hah hbh

/-- Exact-type regression for the full positive-gap zero-frequency logarithmic source bound. -/
theorem printed_zero_coefficients_lower_source {β : ℝ} (hβ : 0 < β) (hh : β < 1) :
    1 / (1 - β) ^ 3 ≤ printedPartIIE1 β / β + partIICubeCoefficient β := by
  exact DhimanKadiriQuesadaHerrera2026.printed_zero_coefficients_lower hβ hh

/-- Exact-type regression for the full positive-gap zero-frequency logarithmic source bound. -/
theorem logarithmic_b_process_printed_zero_full_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hzero : ⌊c / a⌋₊ = 0)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_b_process_printed_zero_full hc ha hab hzero hah hbh


/-- Exact-type regression for the actual Poisson sum with an enlarged upper frequency cutoff. -/
theorem partI_half_arbitrary_cutoff_source {f g : ℝ → ℝ} {a b : ℝ} {M : ℕ}
    (h : PartIRegularity f g a b) (hM : 1 ≤ M) (hβ : deriv f a < (M : ℝ) + 1)
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M‖ ≤
      (partICoefficient f g a / deriv f a) *
        (Real.log ((M : ℝ) + 1) - 1 / (2 * ((M : ℝ) + 1)) -
          (Complex.digamma ((M : ℝ) + 1 - deriv f a : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + deriv f a) - 1 / (2 * (1 + deriv f a))) +
        (g a + g b) / (2 * Real.pi) * (Real.log 2 + 1 / (M : ℝ)) := by
  exact DhimanKadiriQuesadaHerrera2026.partI_half_arbitrary_cutoff h hM hβ ha hb

/-- Exact-type regression for the actual Poisson sum with an enlarged upper frequency cutoff. -/
theorem poisson_next_cutoff_bound_source {f : ℝ → ℝ} {a b ℓ : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b) (hℓ : 0 < ℓ)
    (hβ : deriv f a < (M : ℝ) + 1)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      min (0.6715 / Real.sqrt ℓ) (1 / (Real.pi * ((M : ℝ) + 1 - deriv f a))) +
      (1 / Real.pi) * (Real.log ((M : ℝ) + 2) - 1 / (2 * ((M : ℝ) + 2)) -
          (Complex.digamma ((M : ℝ) + 2 - deriv f a : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + deriv f a) - 1 / (2 * (1 + deriv f a)) +
          Real.log 2 + 1 / ((M : ℝ) + 1)) := by
  exact DhimanKadiriQuesadaHerrera2026.poisson_next_cutoff_bound h hℓ hβ hf' hfc hcurv ha hb

/-- Exact-type regression for the actual Poisson sum with an enlarged upper frequency cutoff. -/
theorem exists_b_process_next_cutoff_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi +
      min (0.6715 / Real.sqrt ℓ) (1 / (Real.pi * ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a))) +
      (1 / Real.pi) * (Real.log ((⌊deriv f a⌋₊ : ℝ) + 2) - 1 / (2 * ((⌊deriv f a⌋₊ : ℝ) + 2)) -
          (Complex.digamma ((⌊deriv f a⌋₊ : ℝ) + 2 - deriv f a : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + deriv f a) - 1 / (2 * (1 + deriv f a)) +
          Real.log 2 + 1 / ((⌊deriv f a⌋₊ : ℝ) + 1)) := by
  exact DhimanKadiriQuesadaHerrera2026.exists_b_process_next_cutoff hab hℓ hαpos hα hM hah hbh hf hf' hf'' hanti hlower hupper hD


/-- Exact-type regression for the literal many-frequency logarithmic B-process and its small-gap comparison. -/
theorem printed_constant_tail_lower_source {β κ : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ) (hκβ : κ ≤ 2 * β) :
    κ / (2 * Real.pi ^ 2 * ((⌊β⌋₊ : ℝ) + 1 - β) ^ 3) - 1 / 72 ≤
      κ / (2 * Real.pi ^ 2) * (printedPartIIE1 β / β + partIICubeCoefficient β) := by
  exact DhimanKadiriQuesadaHerrera2026.printed_constant_tail_lower hβ hκ hκβ

/-- Exact-type regression for the literal many-frequency logarithmic B-process and its small-gap comparison. -/
theorem many_gap_printed_budget_source {α β κ x : ℝ} (hαp : 0 < α) (hα : α < 1) (hβ : 5 / 2 ≤ β)
    (hx : 0 < x) (hscale : κ * x ^ 2 = 1) (hκβ : κ ≤ 2 * β)
    (hdh : (⌊β⌋₊ : ℝ) + 1 - β ≤ 1 / 2) :
    2 / Real.pi + 1 / (Real.pi * ((⌊β⌋₊ : ℝ) + 1 - β)) +
      (1 / Real.pi) * (Real.log ((⌊β⌋₊ : ℝ) + 2) - 1 / (2 * ((⌊β⌋₊ : ℝ) + 2)) -
          (Complex.digamma ((⌊β⌋₊ : ℝ) + 2 - β : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + β) - 1 / (2 * (1 + β)) +
          Real.log 2 + 1 / ((⌊β⌋₊ : ℝ) + 1)) ≤
      0.1585 * β * x + ((α * halfSecondEndpointBound ⌊β⌋₊ α +
          β * halfSecondEndpointBound ⌊β⌋₊ β) / (2 * Real.pi) +
        κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact DhimanKadiriQuesadaHerrera2026.many_gap_printed_budget hαp hα hβ hx hscale hκβ hdh

/-- Exact-type regression for the literal many-frequency logarithmic B-process and its small-gap comparison. -/
theorem logarithmic_b_process_printed_small_gap_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1) (hM : 2 ≤ ⌊c / a⌋₊)
    (hδ : (⌊c / a⌋₊ : ℝ) + 1 - c / a ≤ 1 / 2)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_b_process_printed_small_gap hc ha hab hα hM hδ hah hbh

/-- Exact-type regression for the literal many-frequency logarithmic B-process and its small-gap comparison. -/
theorem logarithmic_b_process_printed_many_full_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1) (hβ : 2 ≤ c / a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_b_process_printed_many_full hc ha hab hα hβ hah hbh


/-- Exact-type regression for the literal logarithmic B-process on its full domain. -/
theorem stationary_one_left_far_source {f : ℝ → ℝ} {a b c ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hβ : 3 / 2 ≤ deriv f a) (hc : c ∈ Set.Icc a b) (hstat : deriv f c = 1)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc (0 : ℕ) 1, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      1.5995 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) + 2 / Real.pi := by
  exact DhimanKadiriQuesadaHerrera2026.stationary_one_left_far hab hℓ hαpos hα hβ hc hstat hf hf' hf'' hanti hlower hupper hD

/-- Exact-type regression for the literal logarithmic B-process on its full domain. -/
theorem one_gap_printed_budget_source {α β κ x : ℝ} (hαp : 0 < α) (hα : α < 1)
    (hβ : 3 / 2 ≤ β) (hβ2 : β < 2) (hx : 0 < x) (hscale : κ * x ^ 2 = 1) (hκβ : κ ≤ 2 * β) :
    2 / Real.pi + 1 / (Real.pi * (2 - β)) +
      (1 / Real.pi) * (Real.log 3 - 1 / (2 * 3) - (Complex.digamma ((3 - β : ℝ) : ℂ)).re +
        Real.eulerMascheroniConstant + Real.log (1 + β) - 1 / (2 * (1 + β)) + Real.log 2 + 1 / 2) ≤
      1.0865 * β * x + 2 / Real.pi * Real.log (β - α) +
      ((α * halfSecondEndpointBound 1 α + β * halfSecondEndpointBound 1 β) / (2 * Real.pi) +
        κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact DhimanKadiriQuesadaHerrera2026.one_gap_printed_budget hαp hα hβ hβ2 hx hscale hκβ

/-- Exact-type regression for the literal logarithmic B-process on its full domain. -/
theorem logarithmic_b_process_printed_one_gap_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1) (hone : ⌊c / a⌋₊ = 1)
    (hδ : (⌊c / a⌋₊ : ℝ) + 1 - c / a ≤ 1 / 2)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_b_process_printed_one_gap hc ha hab hα hone hδ hah hbh

/-- Exact-type regression for the literal logarithmic B-process on its full domain. -/
theorem logarithmic_b_process_printed_full_source {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact DhimanKadiriQuesadaHerrera2026.logarithmic_b_process_printed_full hc ha hab hα hah hbh

/-- Exact general-phase consumer retaining every endpoint and error term. -/
theorem exterior_integral_half_recip_source {f : ℝ → ℝ} {a b ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (hab : a ≤ b) (hν : deriv f a < ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        stationaryEndpointCap ℓ (deriv f b - ν) + 1 / (2 * Real.pi * (ν - deriv f a)) := by
  exact exterior_integral_half_recip hℓ hab hν hf hf' hf'' hcurv hD

/-- Exact general-phase consumer retaining every endpoint and error term. -/
theorem stationary_full_sum_counted_source {f : ℝ → ℝ} {a b D ℓ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        ((⌊deriv f a⌋₊ - 1 : ℕ) : ℝ) *
          ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi := by
  exact stationary_full_sum_counted ξ hab hℓ hαpos hα hM hξ hf hf' hf'' hanti hlower hD

/-- Exact general-phase consumer retaining every endpoint and error term. -/
theorem stationary_sum_next_half_gap_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊) (hδ : (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a ≤ 1 / 2)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 (⌊deriv f a⌋₊ + 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi +
        1 / (Real.pi * (⌊deriv f a⌋₊ : ℝ)) +
        1 / (2 * Real.pi * ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a)) := by
  exact stationary_sum_next_half_gap ξ hab hℓ hαpos hα hM hδ hξ hf hf' hf'' hanti hlower hupper hD

/-- Exact general-phase consumer retaining every endpoint and error term. -/
theorem exists_b_process_half_gap_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊) (hδ : (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a ≤ 1 / 2)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi +
        1 / (Real.pi * (⌊deriv f a⌋₊ : ℝ)) +
        1 / (2 * Real.pi * ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a)) +
      (1 / Real.pi) * (Real.log ((⌊deriv f a⌋₊ : ℝ) + 2) - 1 / (2 * ((⌊deriv f a⌋₊ : ℝ) + 2)) -
          (Complex.digamma ((⌊deriv f a⌋₊ : ℝ) + 2 - deriv f a : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + deriv f a) - 1 / (2 * (1 + deriv f a)) +
          Real.log 2 + 1 / ((⌊deriv f a⌋₊ : ℝ) + 1)) := by
  exact exists_b_process_half_gap hab hℓ hαpos hα hM hδ hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact literal source consumer for the indicated general-phase frequency range. -/
theorem printed_constant_coefficient_nonneg_source {β : ℝ} (hβ : 0 < β) :
    0 ≤ printedPartIIE1 β / β + partIICubeCoefficient β := by
  exact printed_constant_coefficient_nonneg hβ

/-- Exact literal source consumer for the indicated general-phase frequency range. -/
theorem b_process_printed_zero_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hzero : ⌊deriv f a⌋₊ = 0)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact b_process_printed_zero hab hℓ hαpos hzero hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact literal source consumer for the indicated general-phase frequency range. -/
theorem exists_b_process_printed_one_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hone : ⌊deriv f a⌋₊ = 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_b_process_printed_one hab hℓ hαpos hα hone hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact literal source consumer for the indicated general-phase frequency range. -/
theorem exists_b_process_printed_small_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hβsmall : deriv f a < 2)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_b_process_printed_small hab hℓ hαpos hα hβsmall hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact literal source consumer for the indicated general-phase frequency range. -/
theorem exists_source_b_process_small_source {f : ℝ → ℝ} {a b ℓ ℓ₃ h₂ h₃ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hβsmall : deriv f a < 2)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_source_b_process_small hab hℓ hℓ₃ hh₃ hαpos hα hβsmall hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact actual-phase consumer preserving the improved nonlinear coefficient. -/
theorem stationary_radius_tight_eq_source {D ℓ : ℝ} (hD : 0 < D) (hℓ : 0 < ℓ) :
    let δ := (4 / 5 : ℝ) * (3 / (Real.pi * D)) ^ (1 / 3 : ℝ)
    D * δ ^ 2 / ℓ + 3 / (Real.pi * ℓ * δ) =
      (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ := by
  exact stationary_radius_tight_eq hD hℓ

/-- Exact actual-phase consumer preserving the improved nonlinear coefficient. -/
theorem stationary_phase_gap_tight_source {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ +
        stationaryEndpointCap ℓ (deriv f a - ν) + stationaryEndpointCap ℓ (deriv f b - ν) := by
  exact stationary_phase_gap_tight hℓ ha hb hc hf hf' hf'' hcurv hD

/-- Exact actual-phase consumer preserving the improved nonlinear coefficient. -/
theorem stationary_right_phase_tight_source {f : ℝ → ℝ} {a b ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (hab : a ≤ b) (ha : deriv f a = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f a - ν * a - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) a| : ℂ) / 2‖ ≤
      ((1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        stationaryEndpointCap ℓ (deriv f b - ν) := by
  exact stationary_right_phase_tight hℓ hab ha hf hf' hf'' hcurv hD

/-- Exact actual-phase consumer preserving the improved nonlinear coefficient. -/
theorem stationary_full_sum_sharp_tight_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi := by
  exact stationary_full_sum_sharp_tight ξ hab hℓ hαpos hα hM hξ hf hf' hf'' hanti hlower hupper hD

/-- Exact actual-phase consumer preserving the improved nonlinear coefficient. -/
theorem exists_b_process_next_tight_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi +
      min (0.6715 / Real.sqrt ℓ) (1 / (Real.pi * ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a))) +
      (1 / Real.pi) * (Real.log ((⌊deriv f a⌋₊ : ℝ) + 2) - 1 / (2 * ((⌊deriv f a⌋₊ : ℝ) + 2)) -
          (Complex.digamma ((⌊deriv f a⌋₊ : ℝ) + 2 - deriv f a : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + deriv f a) - 1 / (2 * (1 + deriv f a)) +
          Real.log 2 + 1 / ((⌊deriv f a⌋₊ : ℝ) + 1)) := by
  exact exists_b_process_next_tight hab hℓ hαpos hα hM hah hbh hf hf' hf'' hanti hlower hupper hD


section CubicRegression
open Complex MeasureTheory

/-- Preserve the actual cubic error, complex endpoint factor and ordinary derivative hypotheses. -/
theorem oscillatory_parts_twice_source {f p k : ℝ → ℝ} {a b D : ℝ}
    (hf : ∀ u ∈ Set.uIcc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.uIcc a b, HasDerivAt p (k u) u)
    (hk : ∀ u ∈ Set.uIcc a b, DifferentiableAt ℝ k u)
    (hn : ∀ u ∈ Set.uIcc a b, p u ≠ 0)
    (hD : ∀ u ∈ Set.uIcc a b, |deriv k u| ≤ D) :
    (∫ u in a..b, exp (I * (f u : ℂ))) =
      (((1 / p b : ℝ) : ℂ) * exp (I * (f b : ℂ)) -
        ((1 / p a : ℝ) : ℂ) * exp (I * (f a : ℂ))) / I -
      (((k b / (p b) ^ 3 : ℝ) : ℂ) * exp (I * (f b : ℂ)) -
        ((k a / (p a) ^ 3 : ℝ) : ℂ) * exp (I * (f a : ℂ))) +
      ∫ u in a..b, (((deriv k u / (p u) ^ 3 - 3 * (k u) ^ 2 / (p u) ^ 4 : ℝ) : ℂ)) *
        exp (I * (f u : ℂ)) := by
  exact oscillatory_parts_twice hf hp hk hn hD

/-- Preserve the actual cubic error, complex endpoint factor and ordinary derivative hypotheses. -/
theorem curvature_square_integral_source {p k : ℝ → ℝ} {a b κ : ℝ} (hab : a ≤ b)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (k u) u)
    (hkc : ContinuousOn k (Set.Icc a b))
    (hpos : ∀ u ∈ Set.Icc a b, 0 < p u)
    (hkneg : ∀ u ∈ Set.Icc a b, k u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |k u| ≤ κ) :
    (∫ u in a..b, 3 * (k u) ^ 2 / (p u) ^ 4) ≤ κ * (1 / (p b) ^ 3 - 1 / (p a) ^ 3) := by
  exact curvature_square_integral hab hp hkc hpos hkneg hkb

/-- Preserve the actual cubic error, complex endpoint factor and ordinary derivative hypotheses. -/
theorem norm_oscillatory_positive_cubic_source {f p k : ℝ → ℝ} {a b κ D ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (k u) u)
    (hk : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ k u)
    (hmin : ∀ u ∈ Set.Icc a b, ρ ≤ p u)
    (hkneg : ∀ u ∈ Set.Icc a b, k u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |k u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv k u| ≤ D) :
    ‖(∫ u in a..b, exp (I * (f u : ℂ))) -
      (((1 / p b : ℝ) : ℂ) * exp (I * (f b : ℂ)) -
        ((1 / p a : ℝ) : ℂ) * exp (I * (f a : ℂ))) / I‖ ≤
      (2 * κ + D * (b - a)) / ρ ^ 3 := by
  exact norm_oscillatory_positive_cubic hab hρ hf hp hk hmin hkneg hkb hD

/-- Preserve the actual cubic error, complex endpoint factor and ordinary derivative hypotheses. -/
theorem norm_oscillatory_negative_cubic_source {f p k : ℝ → ℝ} {a b κ D ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (k u) u)
    (hk : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ k u)
    (hmax : ∀ u ∈ Set.Icc a b, p u ≤ -ρ)
    (hkneg : ∀ u ∈ Set.Icc a b, k u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |k u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv k u| ≤ D) :
    ‖(∫ u in a..b, exp (I * (f u : ℂ))) -
      (((1 / p b : ℝ) : ℂ) * exp (I * (f b : ℂ)) -
        ((1 / p a : ℝ) : ℂ) * exp (I * (f a : ℂ))) / I‖ ≤
      (2 * κ + D * (b - a)) / ρ ^ 3 := by
  exact norm_oscillatory_negative_cubic hab hρ hf hp hk hmax hkneg hkb hD

/-- Preserve the actual cubic error, complex endpoint factor and ordinary derivative hypotheses. -/
theorem norm_expMode_cubic_source {f p k : ℝ → ℝ} {a b κ D ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (k u) u)
    (hk : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ k u)
    (hside : (∀ u ∈ Set.Icc a b, ρ ≤ p u) ∨ (∀ u ∈ Set.Icc a b, p u ≤ -ρ))
    (hkneg : ∀ u ∈ Set.Icc a b, k u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |k u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv k u| ≤ D) :
    ‖(∫ u in a..b, exp (2 * Real.pi * I * (f u : ℂ))) -
      (((1 / p b : ℝ) : ℂ) * exp (2 * Real.pi * I * (f b : ℂ)) -
        ((1 / p a : ℝ) : ℂ) * exp (2 * Real.pi * I * (f a : ℂ))) / (2 * Real.pi * I)‖ ≤
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2 * ρ ^ 3) := by
  exact norm_expMode_cubic hab hρ hf hp hk hside hkneg hkb hD

end CubicRegression


section CubicCoefficientsRegression
open Complex MeasureTheory

/-- Preserve the actual Fourier coefficient, endpoint denominator and cubic error. -/
theorem positiveCoefficient_eq_boundary_sub_integral_source {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) {n : ℕ} (hn : 0 < n) :
    positiveCoefficient f g a b n =
      weightedWave f g b * expMode (-b) n / (2 * Real.pi * Complex.I * n) -
      weightedWave f g a * expMode (-a) n / (2 * Real.pi * Complex.I * n) -
        ∫ x in a..b, weightedWave f g x * expMode (-x) n := by
  exact positiveCoefficient_eq_boundary_sub_integral h hn

/-- Preserve the actual Fourier coefficient, endpoint denominator and cubic error. -/
theorem norm_shifted_cubic_source {f : ℝ → ℝ} {a b κ D ρ ν : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hside : (∀ u ∈ Set.Icc a b, ρ ≤ deriv f u - ν) ∨ (∀ u ∈ Set.Icc a b, deriv f u - ν ≤ -ρ))
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, exp (2 * Real.pi * I * ((f u - ν * u : ℝ) : ℂ))) -
      (((1 / (deriv f b - ν) : ℝ) : ℂ) * exp (2 * Real.pi * I * ((f b - ν * b : ℝ) : ℂ)) -
        ((1 / (deriv f a - ν) : ℝ) : ℂ) * exp (2 * Real.pi * I * ((f a - ν * a : ℝ) : ℂ))) / (2 * Real.pi * I)‖ ≤
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2 * ρ ^ 3) := by
  exact norm_shifted_cubic hab hρ hf hf' hf'' hside hkneg hkb hD

/-- Preserve the actual Fourier coefficient, endpoint denominator and cubic error. -/
theorem negativeCoefficient_cubic_source {f : ℝ → ℝ} {a b κ D : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    (hM : deriv f a < (M : ℝ) + 1) (n : ℕ) :
    ‖negativeCoefficient f (fun _ => 1) a b (n + M + 1) -
      (2 * Real.pi : ℂ) * (upperModeEndpoint f (deriv f) (deriv f) b M n -
        upperModeEndpoint f (deriv f) (deriv f) a M n)‖ ≤
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2 * ((n : ℝ) + M + 1 - deriv f a) ^ 3) := by
  exact negativeCoefficient_cubic h hf' hf'' hkneg hkb hD hM n

/-- Preserve the actual Fourier coefficient, endpoint denominator and cubic error. -/
theorem positiveCoefficient_cubic_source {f : ℝ → ℝ} {a b κ D : ℝ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) (n : ℕ) :
    ‖positiveCoefficient f (fun _ => 1) a b (n + 1) -
      (2 * Real.pi : ℂ) * (secondModeEndpoint f (deriv f) (deriv f) b n -
        secondModeEndpoint f (deriv f) (deriv f) a n)‖ ≤
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2 * ((n : ℝ) + 1 + deriv f b) ^ 3) := by
  exact positiveCoefficient_cubic h hf' hf'' hkneg hkb hD n

end CubicCoefficientsRegression


section CubicTailRegression
open Complex MeasureTheory

/-- Preserve the actual infinite tail or discrete Poisson sum with its explicit curvature error. -/
theorem negative_tail_cubic_source {f : ℝ → ℝ} {a b κ D : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    (hM : deriv f a < (M : ℝ) + 1) :
    ‖∑' n : ℕ, negativeCoefficient f (fun _ => 1) a b (n + M + 1)‖ ≤
      deriv f b / (2 * Real.pi) * ‖negativeTail M b (deriv f b)‖ +
      deriv f a / (2 * Real.pi) * ‖negativeTail M a (deriv f a)‖ +
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) *
        (∑' n : ℕ, 1 / ((n : ℝ) + ((M : ℝ) + 1 - deriv f a)) ^ 3) := by
  exact negative_tail_cubic h hf' hf'' hkneg hkb hD hM

/-- Preserve the actual infinite tail or discrete Poisson sum with its explicit curvature error. -/
theorem positive_tail_cubic_source {f : ℝ → ℝ} {a b κ D : ℝ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    :
    ‖∑' n : ℕ, positiveCoefficient f (fun _ => 1) a b (n + 1)‖ ≤
      deriv f b / (2 * Real.pi) * ‖positiveTail (-b) (deriv f b)‖ +
      deriv f a / (2 * Real.pi) * ‖positiveTail (-a) (deriv f a)‖ +
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) *
        (∑' n : ℕ, 1 / ((n : ℝ) + (1 + deriv f b)) ^ 3) := by
  exact positive_tail_cubic h hf' hf'' hkneg hkb hD

/-- Preserve the actual infinite tail or discrete Poisson sum with its explicit curvature error. -/
theorem constant_poisson_cubic_series_source {f : ℝ → ℝ} {a b κ D : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    (hM : 1 ≤ M) (hδ : 1 / 2 ≤ (M : ℝ) + 1 - deriv f a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, exp (2 * Real.pi * I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        exp (2 * Real.pi * I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / (M : ℝ)) / Real.pi + 1 / 2 + Real.log 2 / Real.pi +
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) *
        ((∑' n : ℕ, 1 / ((n : ℝ) + ((M : ℝ) + 1 - deriv f a)) ^ 3) +
          ∑' n : ℕ, 1 / ((n : ℝ) + (1 + deriv f b)) ^ 3) := by
  exact constant_poisson_cubic_series h hf' hf'' hkneg hkb hD hM hδ hah hbh

/-- Preserve the actual infinite tail or discrete Poisson sum with its explicit curvature error. -/
theorem constant_poisson_cubic_source {f : ℝ → ℝ} {a b κ D : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    (hM : 1 ≤ M) (hδ : 1 / 2 ≤ (M : ℝ) + 1 - deriv f a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, exp (2 * Real.pi * I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        exp (2 * Real.pi * I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / (M : ℝ)) / Real.pi + 1 / 2 + Real.log 2 / Real.pi +
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) *
        (1 / ((M : ℝ) + 1 - deriv f a) ^ 3 +
          1 / ((M : ℝ) + 2 - deriv f a) ^ 3 + 1 / (2 * ((M : ℝ) + 2 - deriv f a) ^ 2) +
          1 / (1 + deriv f b) ^ 3 + 1 / (2 + deriv f b) ^ 3 + 1 / (2 * (2 + deriv f b) ^ 2)) := by
  exact constant_poisson_cubic h hf' hf'' hkneg hkb hD hM hδ hah hbh

/-- Preserve the actual infinite tail or discrete Poisson sum with its explicit curvature error. -/
theorem positive_tail_from_two_source {x y : ℝ} (hy : 0 < y) (hx : |Real.sin (Real.pi * x)| = 1) :
    ‖∑' n : ℕ, expMode x (n + 2) / (((n : ℝ) + 2) * ((n : ℝ) + 2 + y) : ℝ)‖ ≤
      1 / (2 * (2 + y)) := by
  exact positive_tail_from_two hy hx

/-- Preserve the actual infinite tail or discrete Poisson sum with its explicit curvature error. -/
theorem second_endpoint_from_two_source {f p : ℝ → ℝ} {x : ℝ} (hp : 0 < p x)
    (hx : ∃ k : ℤ, x = (k : ℝ) + 1 / 2) :
    ‖∑' n : ℕ, secondModeEndpoint f p p x (n + 1)‖ ≤ 1 / (8 * Real.pi ^ 2) := by
  exact second_endpoint_from_two hp hx

/-- Preserve the actual infinite tail or discrete Poisson sum with its explicit curvature error. -/
theorem positive_tail_cubic_split_source {f : ℝ → ℝ} {a b κ D : ℝ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖∑' n : ℕ, positiveCoefficient f (fun _ => 1) a b n‖ ≤
      3 / (2 * Real.pi) + (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) *
        (∑' n : ℕ, 1 / ((n : ℝ) + (2 + deriv f b)) ^ 3) := by
  exact positive_tail_cubic_split h hf' hf'' hkneg hkb hD hah hbh

end CubicTailRegression


section CubicBudgetRegression
open Complex MeasureTheory

/-- Preserve the exact quantitative error allowance and its actual source inputs. -/
theorem printed_coefficient_after_cubic_source {α β : ℝ} (hα : 0 ≤ α) (hβ : 2 ≤ β) :
    let d := (⌊β⌋₊ : ℝ) + 1 - β
    (∑' n : ℕ, 1 / ((n : ℝ) + (d + 1)) ^ 3) +
      (∑' n : ℕ, 1 / ((n : ℝ) + (2 + α)) ^ 3) + 25 / (36 * d ^ 3) ≤
        printedPartIIE1 β / β + partIICubeCoefficient β := by
  exact printed_coefficient_after_cubic hα hβ

/-- Preserve the exact quantitative error allowance and its actual source inputs. -/
theorem cubic_half_gap_budget_source {x d : ℝ} (hx : 0 < x) (hd : 0 < d) :
    1 / (2 * Real.pi * d) ≤ 0.1585 / x + 25 * x ^ 2 / (72 * Real.pi ^ 2 * d ^ 3) := by
  exact cubic_half_gap_budget hx hd

/-- Preserve the exact quantitative error allowance and its actual source inputs. -/
theorem cubic_curvature_gap_budget_source {α β κ ℓ : ℝ} (hα : 0 ≤ α) (hβ : 2 ≤ β)
    (hℓ : 0 < ℓ) (hκ : ℓ ≤ κ) :
    let d := (⌊β⌋₊ : ℝ) + 1 - β
    κ / (2 * Real.pi ^ 2) * ((∑' n : ℕ, 1 / ((n : ℝ) + (d + 1)) ^ 3) +
      (∑' n : ℕ, 1 / ((n : ℝ) + (2 + α)) ^ 3)) + 1 / (2 * Real.pi * d) ≤
      0.1585 / Real.sqrt ℓ + κ / (2 * Real.pi ^ 2) *
        (printedPartIIE1 β / β + partIICubeCoefficient β) := by
  exact cubic_curvature_gap_budget hα hβ hℓ hκ

/-- Preserve the exact quantitative error allowance and its actual source inputs. -/
theorem cubic_small_D_budget_source {D L h₂ S : ℝ} (hD : 0 ≤ D) (hD1 : D ≤ 1)
    (hL : 0 ≤ L) (hh₂ : 1 ≤ h₂) (hS : S ≤ 7 / 4) :
    D * L / (4 * Real.pi ^ 2) * S ≤
      (0.06 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * L := by
  exact cubic_small_D_budget hD hD1 hL hh₂ hS

/-- Preserve the exact quantitative error allowance and its actual source inputs. -/
theorem cubic_constant_budget_source {α β : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (M : ℕ) :
    1 / 2 + (Real.log 2 + 1 / ((M : ℝ) + 1) + 4.5) / Real.pi ≤
      (α * halfSecondEndpointBound M α + β * halfSecondEndpointBound M β) / (2 * Real.pi) +
        1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi) := by
  exact cubic_constant_budget hα hα1 hβ M

/-- Preserve the exact quantitative error allowance and its actual source inputs. -/
theorem constant_poisson_cubic_split_source {f : ℝ → ℝ} {a b κ D : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    (hM : 1 ≤ M) (hδ : 1 / 2 ≤ (M : ℝ) + 1 - deriv f a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, exp (2 * Real.pi * I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        exp (2 * Real.pi * I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / (M : ℝ)) / Real.pi + 1 / 2 + 3 / (2 * Real.pi) +
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) *
        ((∑' n : ℕ, 1 / ((n : ℝ) + ((M : ℝ) + 1 - deriv f a)) ^ 3) +
          ∑' n : ℕ, 1 / ((n : ℝ) + (2 + deriv f b)) ^ 3) := by
  exact constant_poisson_cubic_split h hf' hf'' hkneg hkb hD hM hδ hah hbh

/-- Preserve the exact quantitative error allowance and its actual source inputs. -/
theorem stationary_sum_next_hybrid_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 (⌊deriv f a⌋₊ + 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        (1.94 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi +
        1 / Real.pi +
        1 / (2 * Real.pi * ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a)) := by
  exact stationary_sum_next_hybrid ξ hab hℓ hαpos hα hM hξ hf hf' hf'' hanti hlower hupper hD

end CubicBudgetRegression


/-- Preserve every literal B-process constant, actual stationary main term and the explicit bound on the third derivative. -/
theorem exists_b_process_cubic_small_D_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊) (hD1 : D ≤ 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_b_process_cubic_small_D hab hℓ hαpos hα hM hD1 hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Preserve every literal B-process constant, actual stationary main term and the explicit bound on the third derivative. -/
theorem exists_b_process_small_D_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hD1 : D ≤ 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_b_process_small_D hab hℓ hαpos hα hD1 hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Preserve every literal B-process constant, actual stationary main term and the explicit bound on the third derivative. -/
theorem exists_source_b_process_small_D_source {f : ℝ → ℝ} {a b ℓ ℓ₃ h₂ h₃ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hD1 : h₃ * ℓ₃ ≤ 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_source_b_process_small_D hab hℓ hℓ₃ hh₃ hαpos hα hD1 hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact-type regression for the enlarged bounded-third-derivative argument. -/
theorem third_root_four_budget_source {D : ℝ} (hD : 0 ≤ D) (hD4 : D ≤ 4) :
    D ≤ (13 / 5 : ℝ) * D ^ (1 / 3 : ℝ) := by
  exact third_root_four_budget hD hD4

/-- Exact-type regression for the enlarged bounded-third-derivative argument. -/
theorem cubic_series_uniform_sharp_source {α d : ℝ} (hα : 0 ≤ α) (hd : 0 ≤ d) :
    (∑' n : ℕ, 1 / ((n : ℝ) + (d + 1)) ^ 3) +
      (∑' n : ℕ, 1 / ((n : ℝ) + (2 + α)) ^ 3) ≤ 3 / 2 := by
  exact cubic_series_uniform_sharp hα hd

/-- Exact-type regression for the enlarged bounded-third-derivative argument. -/
theorem cubic_series_gap_nine_twentieths_source {α d : ℝ} (hα : 0 ≤ α) (hd : 9 / 20 ≤ d) :
    (∑' n : ℕ, 1 / ((n : ℝ) + (d + 1)) ^ 3) +
      (∑' n : ℕ, 1 / ((n : ℝ) + (2 + α)) ^ 3) ≤ 102 / 125 := by
  exact cubic_series_gap_nine_twentieths hα hd

/-- Exact-type regression for the enlarged bounded-third-derivative argument. -/
theorem cubic_four_length_small_gap_source {D L h₂ S : ℝ} (hD : 0 ≤ D) (hD4 : D ≤ 4)
    (hL : 0 ≤ L) (hh₂ : 1 ≤ h₂) (hS : S ≤ 3 / 2) :
    D * L / (4 * Real.pi ^ 2) * S ≤
      (0.11 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * L := by
  exact cubic_four_length_small_gap hD hD4 hL hh₂ hS

/-- Exact-type regression for the enlarged bounded-third-derivative argument. -/
theorem cubic_four_length_large_gap_source {D L h₂ S : ℝ} (hD : 0 ≤ D) (hD4 : D ≤ 4)
    (hL : 0 ≤ L) (hh₂ : 1 ≤ h₂) (hS : S ≤ 102 / 125) :
    D * L / (4 * Real.pi ^ 2) * S ≤
      (0.06 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * L := by
  exact cubic_four_length_large_gap hD hD4 hL hh₂ hS

/-- Exact-type regression for the enlarged bounded-third-derivative argument. -/
theorem stationary_sum_next_small_gap_source {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊) (hδ : (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a ≤ 9 / 20)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 (⌊deriv f a⌋₊ + 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi +
        1 / Real.pi +
        1 / (2 * Real.pi * ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a)) := by
  exact stationary_sum_next_small_gap ξ hab hℓ hαpos hα hM hδ hξ hf hf' hf'' hanti hlower hupper hD

/-- Exact-type regression for the enlarged bounded-third-derivative argument. -/
theorem exists_b_process_cubic_four_D_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊) (hD4 : D ≤ 4)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_b_process_cubic_four_D hab hℓ hαpos hα hM hD4 hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact-type regression for the enlarged bounded-third-derivative argument. -/
theorem exists_b_process_four_D_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hD4 : D ≤ 4)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_b_process_four_D hab hℓ hαpos hα hD4 hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact-type regression for the enlarged bounded-third-derivative argument. -/
theorem exists_source_b_process_four_D_source {f : ℝ → ℝ} {a b ℓ ℓ₃ h₂ h₃ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hD4 : h₃ * ℓ₃ ≤ 4)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_source_b_process_four_D hab hℓ hℓ₃ hh₃ hαpos hα hD4 hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem stationary_scale_lower_source :
    (0.969 : ℝ) ≤ (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ) := by
  exact stationary_scale_lower

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem large_D_nonlinear_lower_source {D : ℝ} (hD : 4 ≤ D) :
    (0.169 : ℝ) ≤ (0.11 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) := by
  exact large_D_nonlinear_lower hD

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem digamma_unit_chord_source {d : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    d - Real.eulerMascheroniConstant ≤ (Complex.digamma (1 + d : ℝ)).re := by
  exact digamma_unit_chord hd hd1

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem large_D_near_budget_source {x w d : ℝ} (hw : 0 < w) :
    min (0.6715 * x) (1 / (Real.pi * d)) ≤
      0.1585 * x + 0.01 * w * x ^ 2 + 1 / (2 * Real.pi * d) + 0.786 / w := by
  exact large_D_near_budget hw

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem large_D_rational_residual_source {w : ℝ} (hw : 25 ≤ w) :
    0.786 / w - 0.397 / (w + 3) ≤ 0.018 := by
  exact large_D_rational_residual hw

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem log_square_tangent_six_source {u : ℝ} (hu : 5 ≤ u) :
    Real.log (u ^ 2 + 2) ≤ (6 / 19 : ℝ) * u + Real.log 38 - 36 / 19 := by
  exact log_square_tangent_six hu

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem log_square_sharp_source {u : ℝ} (hu : 5 ≤ u) :
    Real.log (u ^ 2 + 2) ≤ 0.314 * u + 1.754 := by
  exact log_square_sharp hu

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem large_D_log_bound_source {β : ℝ} (hβ : 26 ≤ β) :
    Real.log (β + 1) ≤ 0.314 * Real.sqrt (β - 1) + 1.754 := by
  exact large_D_log_bound hβ

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem large_D_log_gap_budget_source {β d : ℝ} (hβ : 26 ≤ β) (hd : 0 < d) (hd1 : d ≤ 1) :
    (2 * Real.log (β + 1) + 2.433432 - d - 1.25 / (β + 2)) / Real.pi - 1.751 +
      1 / (2 * Real.pi * d) + 0.786 / (β - 1) ≤ 0.2 * Real.sqrt (β - 1) / d := by
  exact large_D_log_gap_budget hβ hd hd1

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem large_D_curvature_coefficient_source {β : ℝ} (hβ : 26 ≤ β) :
    (10 / 159 : ℝ) / ((⌊β⌋₊ : ℝ) + 1 - β) ^ 2 ≤
      (printedPartIIE1 β / β + partIICubeCoefficient β) / (2 * Real.pi ^ 2) := by
  exact large_D_curvature_coefficient hβ

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem large_D_amgm_source {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hprod : w ≤ u * v) :
    0.2 * Real.sqrt w ≤ 0.159 * u + (10 / 159 : ℝ) * v := by
  exact large_D_amgm hu hv hw hprod

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem large_D_small_quadratic_source {β x : ℝ} (hβ : 2 ≤ β) (hβ18 : β ≤ 18) :
    (β - 2.686) * x ≤ 2 * (β - 1) * x ^ 2 + 1.75 := by
  exact large_D_small_quadratic hβ hβ18

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem large_D_middle_quadratic_source {β x : ℝ} (hβ : 18 ≤ β) (hβ26 : β ≤ 26) :
    (β - 2.686) * x ≤ 2 * (β - 1) * x ^ 2 + 2.75 := by
  exact large_D_middle_quadratic hβ hβ26

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem large_D_poisson_excess_source {α β : ℝ} (hαp : 0 < α) (hα : α < 1) (hβ : 26 ≤ β) :
    let d := (⌊β⌋₊ : ℝ) + 1 - β
    let P := (Real.log ((⌊β⌋₊ : ℝ) + 2) - 1 / (2 * ((⌊β⌋₊ : ℝ) + 2)) -
      (Complex.digamma ((⌊β⌋₊ : ℝ) + 2 - β : ℝ)).re + Real.eulerMascheroniConstant +
      Real.log (1 + β) - 1 / (2 * (1 + β)) + Real.log 2 + 1 / ((⌊β⌋₊ : ℝ) + 1)) / Real.pi
    let H := (α * halfSecondEndpointBound ⌊β⌋₊ α + β * halfSecondEndpointBound ⌊β⌋₊ β) / (2 * Real.pi) +
      1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi)
    2 / Real.pi + P - H ≤
      (2 * Real.log (β + 1) + 2.433432 - d - 1.25 / (β + 2)) / Real.pi - 1.751 := by
  exact large_D_poisson_excess hαp hα hβ

/-- Exact-type regression for the large-derivative B-process budgets. -/
theorem large_D_curvature_length_source {β K κ : ℝ} (hβ : 26 ≤ β) (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hprod : β - 1 ≤ K * κ) :
    0.2 * Real.sqrt (β - 1) / ((⌊β⌋₊ : ℝ) + 1 - β) ≤
      0.159 * K + κ / (2 * Real.pi ^ 2) * (printedPartIIE1 β / β + partIICubeCoefficient β) := by
  exact large_D_curvature_length hβ hK hκ hprod

/-- Exact source regression for the full printed Corollary 0.2 and its actual sums. -/
theorem norm_source_exponential_source (t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
  exact norm_source_exponential t

/-- Exact source regression for the full printed Corollary 0.2 and its actual sums. -/
theorem norm_source_discrete_le_length_source {a b : ℝ} (f : ℝ → ℝ) (hab : a ≤ b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))‖ ≤ b - a := by
  exact norm_source_discrete_le_length f hab hah hbh

/-- Exact source regression for the full printed Corollary 0.2 and its actual sums. -/
theorem norm_source_stationary_le_source {f : ℝ → ℝ} {a b ℓ : ℝ} {M : ℕ} (ξ : ℕ → ℝ) (hℓ : 0 < ℓ)
    (hξ : ∀ ν ∈ Finset.Icc 1 M, ξ ν ∈ Set.Icc a b)
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|) :
    ‖∑ ν ∈ Finset.Icc 1 M,
      Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤ (M : ℝ) / Real.sqrt ℓ := by
  exact norm_source_stationary_le ξ hℓ hξ hlower

/-- Exact source regression for the full printed Corollary 0.2 and its actual sums. -/
theorem printed_half_remainder_full_lower_source {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hκ : 0 ≤ κ) :
    (1.751 : ℝ) ≤
      (α * halfSecondEndpointBound ⌊β⌋₊ α + β * halfSecondEndpointBound ⌊β⌋₊ β) / (2 * Real.pi) +
        κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi) := by
  exact printed_half_remainder_full_lower hα hβ hκ

/-- Exact source regression for the full printed Corollary 0.2 and its actual sums. -/
theorem exists_b_process_large_D_small_beta_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hβ : 2 ≤ deriv f a) (hβ26 : deriv f a ≤ 26) (hD4 : 4 ≤ D)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_b_process_large_D_small_beta hab hℓ hαpos hα hβ hβ26 hD4 hah hbh hf' hanti hlower hupper

/-- Exact source regression for the full printed Corollary 0.2 and its actual sums. -/
theorem exists_b_process_large_D_large_beta_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hβ : 26 ≤ deriv f a) (hD4 : 4 ≤ D)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_b_process_large_D_large_beta hab hℓ hαpos hα hβ hD4 hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact source regression for the full printed Corollary 0.2 and its actual sums. -/
theorem exists_b_process_printed_full_source {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_b_process_printed_full hab hℓ hαpos hα hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact source regression for the full printed Corollary 0.2 and its actual sums. -/
theorem exists_source_b_process_printed_full_source {f : ℝ → ℝ} {a b ℓ ℓ₃ h₂ h₃ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact exists_source_b_process_printed_full hab hℓ hℓ₃ hh₃ hαpos hα hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact source regression for the full printed Corollary 0.2 and its actual sums. -/
theorem source_b_process_printed_source {f : ℝ → ℝ} {a b ℓ ℓ₃ h₂ h₃ : ℝ}
    (ξ : ℕ → ℝ)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hab : a < b) (hℓ : 0 < ℓ) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  exact source_b_process_printed ξ hξ hab hℓ hℓ₃ hh₃ hαpos hα hah hbh hf hf' hf'' hanti hlower hupper hD

/-- Exact-type source object, indexing and branch regression. -/
theorem sharpZetaSum_eq_integer_source_source {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    sharpZetaSum s x = ∑ n ∈ Finset.Ioc (0 : ℤ) ⌊x⌋, (n : ℂ) ^ (-s) := by
  exact sharpZetaSum_eq_integer_source hx s

/-- Exact-type source object, indexing and branch regression. -/
theorem afeRemainder_eq_integer_source_source {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (σ t : ℝ) :
    afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y =
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) -
        (∑ n ∈ Finset.Ioc (0 : ℤ) ⌊x⌋, (n : ℂ) ^ (-(σ : ℂ) - (t : ℂ) * Complex.I)) -
        chi ((σ : ℂ) + (t : ℂ) * Complex.I) *
          (∑ m ∈ Finset.Ioc (0 : ℤ) ⌊y⌋, (m : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I - 1)) := by
  exact afeRemainder_eq_integer_source hx hy σ t

/-- Exact-type source object, indexing and branch regression. -/
theorem actual_wave_principal_power_source {u : ℝ} (hu : 0 < u) (σ t : ℝ) :
    starRingEnd ℂ ((u ^ (-σ) : ℝ) * Complex.exp
      (2 * Real.pi * Complex.I * ((t / (2 * Real.pi) * Real.log u : ℝ) : ℂ))) =
        (u : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  exact actual_wave_principal_power hu σ t

/-- Exact-type source object, indexing and branch regression. -/
theorem integer_sample_endpoints_source (a b : ℝ) (n : ℤ) :
    n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋ ↔ a < (n : ℝ) ∧ (n : ℝ) ≤ b := by
  exact integer_sample_endpoints a b n

/-- Exact-type source object, indexing and branch regression. -/
theorem integer_source_half_cutoff_source {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    (∑ n ∈ Finset.Ioc (0 : ℤ) ⌊afeHalfCutoff x⌋, (n : ℂ) ^ (-s)) =
      ∑ n ∈ Finset.Ioc (0 : ℤ) ⌊x⌋, (n : ℂ) ^ (-s) := by
  exact integer_source_half_cutoff hx s

/-- Exact accepted-contract regression for continuousOn_deriv_of_monotone. -/
theorem continuousOn_deriv_of_monotone_source {F : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ F u)
    (hm : MonotoneOn (deriv F) (Set.Icc a b)) :
    ContinuousOn (deriv F) (Set.Icc a b) := by
  exact DhimanKadiriQuesadaHerrera2026.continuousOn_deriv_of_monotone hd hm


/-- Exact accepted-contract regression for continuousOn_deriv_of_antitone. -/
theorem continuousOn_deriv_of_antitone_source {F : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ F u)
    (hm : AntitoneOn (deriv F) (Set.Icc a b)) :
    ContinuousOn (deriv F) (Set.Icc a b) := by
  exact DhimanKadiriQuesadaHerrera2026.continuousOn_deriv_of_antitone hd hm


/-- Exact accepted-contract regression for secondOrderRegularity_of_source. -/
theorem secondOrderRegularity_of_source_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hN : (N : ℝ) < deriv f b)
    (hfa : StrictAntiOn (deriv f) (Set.Icc a b))
    (hgd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ g u)
    (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ u ∈ Set.Icc a b, 0 < g u) (hga : AntitoneOn g (Set.Icc a b))
    (hgda : AntitoneOn (fun u => |deriv g u|) (Set.Icc a b))
    (hgdq : AntitoneOn (fun u => |deriv g u| / (1 + deriv f u - N)) (Set.Icc a b))
    (hf2p : ∀ u ∈ Set.Icc a b, 0 < |deriv (deriv f) u|)
    (hf2a : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hg2p : ∀ u ∈ Set.Icc a b, 0 < deriv (deriv g) u)
    (hg2a : AntitoneOn (deriv (deriv g)) (Set.Icc a b))
    (hq : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv h u| /
        ((ν : ℝ) + deriv f u - N) ^ 2) (Set.Icc a b))
    (hc : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |h u * deriv (deriv f) u| /
        ((ν : ℝ) + deriv f u - N) ^ 3) (Set.Icc a b)) :
    SecondOrderRegularity (phaseShift f N) g a b := by
  exact DhimanKadiriQuesadaHerrera2026.secondOrderRegularity_of_source hab hfd hfc hN hfa hgd hgdc hgp hga hgda hgdq hf2p hf2a hg2p hg2a hq hc


/-- Exact accepted-contract regression for corrected_poisson_partII. -/
theorem corrected_poisson_partII_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hN : (N : ℝ) < deriv f b)
    (hfa : StrictAntiOn (deriv f) (Set.Icc a b))
    (hgd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ g u)
    (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ u ∈ Set.Icc a b, 0 < g u) (hga : AntitoneOn g (Set.Icc a b))
    (hgda : AntitoneOn (fun u => |deriv g u|) (Set.Icc a b))
    (hgdq : AntitoneOn (fun u => |deriv g u| / (1 + deriv f u - N)) (Set.Icc a b))
    (hf2p : ∀ u ∈ Set.Icc a b, 0 < |deriv (deriv f) u|)
    (hf2a : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hg2p : ∀ u ∈ Set.Icc a b, 0 < deriv (deriv g) u)
    (hg2a : AntitoneOn (deriv (deriv g)) (Set.Icc a b))
    (hq : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv h u| /
        ((ν : ℝ) + deriv f u - N) ^ 2) (Set.Icc a b))
    (hc : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |h u * deriv (deriv f) u| /
        ((ν : ℝ) + deriv f u - N) ^ 3) (Set.Icc a b)) :
    let F := phaseShift f N
    let y := deriv f a - N
    let M := ⌊deriv f a⌋₊ - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, (g (n : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊, ∫ u in a..b, (g u : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (g b * poissonEndpointMajorant b y + g a * poissonEndpointMajorant a y) / (2 * Real.pi) +
      ‖poissonBoundary F g a b‖ +
      (secondH F g b * secondTailMajorant M b (deriv f b - N) +
        secondH F g a * secondTailMajorant M a y) / (4 * Real.pi ^ 2) +
      (secondH1 F g a * partIISquareTailEnvelope y +
        secondH F g a * |deriv (deriv f) a| * partIICubeCoefficient y) /
          (4 * Real.pi ^ 3 * y) := by
  exact DhimanKadiriQuesadaHerrera2026.corrected_poisson_partII hab hfd hfc hN hfa hgd hgdc hgp hga hgda hgdq hf2p hf2a hg2p hg2a hq hc


/-- Exact accepted-contract regression for corrected_poisson_partII_half_integer. -/
theorem corrected_poisson_partII_half_integer_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hN : (N : ℝ) < deriv f b)
    (hfa : StrictAntiOn (deriv f) (Set.Icc a b))
    (hgd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ g u)
    (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ u ∈ Set.Icc a b, 0 < g u) (hga : AntitoneOn g (Set.Icc a b))
    (hgda : AntitoneOn (fun u => |deriv g u|) (Set.Icc a b))
    (hgdq : AntitoneOn (fun u => |deriv g u| / (1 + deriv f u - N)) (Set.Icc a b))
    (hf2p : ∀ u ∈ Set.Icc a b, 0 < |deriv (deriv f) u|)
    (hf2a : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hg2p : ∀ u ∈ Set.Icc a b, 0 < deriv (deriv g) u)
    (hg2a : AntitoneOn (deriv (deriv g)) (Set.Icc a b))
    (hq : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv h u| /
        ((ν : ℝ) + deriv f u - N) ^ 2) (Set.Icc a b))
    (hc : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |h u * deriv (deriv f) u| /
        ((ν : ℝ) + deriv f u - N) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    let F := phaseShift f N
    let y := deriv f a - N
    let M := ⌊deriv f a⌋₊ - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, (g (n : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊, ∫ u in a..b, (g u : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH F g b / (4 * Real.pi ^ 2) * halfSecondEndpointDelta M (deriv f b - N) +
      secondH F g a / (4 * Real.pi ^ 2) * halfSecondEndpointDelta M y +
      (secondH1 F g a * partIISquareTailEnvelope y +
        secondH F g a * |deriv (deriv f) a| * partIICubeCoefficient y) /
          (4 * Real.pi ^ 3 * y) := by
  exact DhimanKadiriQuesadaHerrera2026.corrected_poisson_partII_half_integer hab hfd hfc hN hfa hgd hgdc hgp hga hgda hgdq hf2p hf2a hg2p hg2a hq hc hah hbh


/-- Exact accepted-contract regression for constant_secondOrderRegularity_source. -/
theorem constant_secondOrderRegularity_source_source {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hpos : 0 < deriv f b)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hfdd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hanti : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hq : ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv (deriv f) u| /
      ((ν : ℝ) + deriv f u) ^ 2) (Set.Icc a b))
    (hr : ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv f u * deriv (deriv f) u| /
      ((ν : ℝ) + deriv f u) ^ 3) (Set.Icc a b)) :
    SecondOrderRegularity f (fun _ => 1) a b := by
  exact DhimanKadiriQuesadaHerrera2026.constant_secondOrderRegularity_source hab hfd hfc hpos hfa hfdd hanti hq hr


/-- Exact accepted-contract regression for corrected_corollary_zero_one_partII. -/
theorem corrected_corollary_zero_one_partII_source {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hpos : 0 < deriv f b)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hfdd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hanti : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hq : ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv (deriv f) u| /
      ((ν : ℝ) + deriv f u) ^ 2) (Set.Icc a b))
    (hr : ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv f u * deriv (deriv f) u| /
      ((ν : ℝ) + deriv f u) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    let y := deriv f a
    let M := ⌊y⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / y) / Real.pi +
      (deriv f b * halfSecondEndpointDelta M (deriv f b) + y * halfSecondEndpointDelta M y) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) *
        (partIISquareTailEnvelope y / y + partIICubeCoefficient y) := by
  exact DhimanKadiriQuesadaHerrera2026.corrected_corollary_zero_one_partII hab hfd hfc hpos hfa hfdd hanti hq hr hah hbh


/-- Exact accepted-contract regression for corrected_corollary_zero_one_partII_pi. -/
theorem corrected_corollary_zero_one_partII_pi_source {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hpos : 0 < deriv f b)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hfdd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hanti : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hq : ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv (deriv f) u| /
      ((ν : ℝ) + deriv f u) ^ 2) (Set.Icc a b))
    (hr : ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv f u * deriv (deriv f) u| /
      ((ν : ℝ) + deriv f u) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a) :
    let y := deriv f a
    let M := ⌊y⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / y) / Real.pi +
      (deriv f b * halfSecondEndpointBound M (deriv f b) + y * halfSecondEndpointBound M y) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) *
        (partIISquareTailEnvelope y / y + partIICubeCoefficient y) := by
  exact DhimanKadiriQuesadaHerrera2026.corrected_corollary_zero_one_partII_pi hab hfd hfc hpos hfa hfdd hanti hq hr hah hbh hδ


/-- Exact accepted-contract regression for corrected_corollary_eight_one. -/
theorem corrected_corollary_eight_one_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hN : (N : ℝ) < deriv f b)
    (hfa : StrictAntiOn (deriv f) (Set.Icc a b))
    (hgd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ g u)
    (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ u ∈ Set.Icc a b, 0 < g u) (hga : AntitoneOn g (Set.Icc a b))
    (hgda : AntitoneOn (fun u => |deriv g u|) (Set.Icc a b))
    (hgdq : AntitoneOn (fun u => |deriv g u| / (1 + deriv f u - N)) (Set.Icc a b))
    (hf2p : ∀ u ∈ Set.Icc a b, 0 < |deriv (deriv f) u|)
    (hf2a : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hg2p : ∀ u ∈ Set.Icc a b, 0 < deriv (deriv g) u)
    (hg2a : AntitoneOn (deriv (deriv g)) (Set.Icc a b))
    (hq : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv h u| /
        ((ν : ℝ) + deriv f u - N) ^ 2) (Set.Icc a b))
    (hc : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |h u * deriv (deriv f) u| /
        ((ν : ℝ) + deriv f u - N) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 - Int.fract (deriv f a) = 1 / 2) :
    let F := phaseShift f N
    let y := deriv f a - N
    let z := deriv f b - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH F g b / (4 * Real.pi ^ 2) *
        ((1 / z) * (Real.pi / 2 + 1 / (y + 1 / 2) + Real.log 2 + 3 / (2 * (z + 1)))) +
      secondH F g a / (4 * Real.pi ^ 2) *
        ((1 / y) * (Real.pi / 2 + 1 / (y + 1 / 2) + Real.log 2 + 3 / (2 * (y + 1)))) +
      secondH1 F g a / (4 * Real.pi ^ 3) *
        ((46 / 9) / y + (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
          2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y ^ 2) +
      (secondH F g a * |deriv (deriv F) a| / (4 * Real.pi ^ 3)) *
        ((230 / 27) / y - (14 / 3) / y ^ 2 +
          (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
            2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
            (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 3) := by
  exact DhimanKadiriQuesadaHerrera2026.corrected_corollary_eight_one hab hfd hfc hN hfa hgd hgdc hgp hga hgda hgdq hf2p hf2a hg2p hg2a hq hc hah hbh hδ

end DhimanKadiriQuesadaHerrera2026.SemanticRegression
