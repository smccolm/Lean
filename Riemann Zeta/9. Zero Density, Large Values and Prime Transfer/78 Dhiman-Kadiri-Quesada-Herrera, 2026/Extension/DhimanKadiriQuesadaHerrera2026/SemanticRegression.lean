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

end DhimanKadiriQuesadaHerrera2026.SemanticRegression
