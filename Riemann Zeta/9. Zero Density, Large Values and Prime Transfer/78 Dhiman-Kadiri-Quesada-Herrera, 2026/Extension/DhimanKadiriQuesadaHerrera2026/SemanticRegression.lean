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

/-- The provisional general second-order analytic interface bounds the actual sum and literal Fourier integrals. -/
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

/-- The complete source-frequency range and actual weighted sum consume the explicit provisional second-order theorem. -/
theorem general_second_poisson_shifted_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N)
    (r : SecondOrderRegularity (phaseShift f N) g a b) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, (g (n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      secondPoissonError (phaseShift f N) g a b := by
  simpa only [weightedWave] using second_poisson_shifted_bound h r


/-- The complete source-frequency range and actual weighted sum consume the explicit provisional second-order theorem. -/
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

/-- The exact provisional Part-II conclusion consumes analytic inputs and retains the actual sum. -/
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

/-- The exact provisional Part-II conclusion consumes analytic inputs and retains the actual sum. -/
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

/-- The exact provisional Part-II conclusion consumes analytic inputs and retains the actual sum. -/
theorem partIISquareTailEnvelope_half_offset_source {y : ℝ} (hy : 0 < y)
    (hδ : (⌊y⌋₊ : ℝ) + 1 - y = 1 / 2) :
    partIISquareTailEnvelope y = 46 / 9 +
      (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
        2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y := by
  simpa only [weightedWave] using partIISquareTailEnvelope_half_offset hy hδ

/-- The exact provisional Part-II conclusion consumes analytic inputs and retains the actual sum. -/
theorem partIICubeCoefficient_half_offset_source {y : ℝ} (hy : 0 < y)
    (hδ : (⌊y⌋₊ : ℝ) + 1 - y = 1 / 2) :
    partIICubeCoefficient y = 230 / 27 - (14 / 3) / y +
      (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
        2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
        (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 2 := by
  simpa only [weightedWave] using partIICubeCoefficient_half_offset hy hδ

/-- The exact provisional Part-II conclusion consumes analytic inputs and retains the actual sum. -/
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

end DhimanKadiriQuesadaHerrera2026.SemanticRegression
