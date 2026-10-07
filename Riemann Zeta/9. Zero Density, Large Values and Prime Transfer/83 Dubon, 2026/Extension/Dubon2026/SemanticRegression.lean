import Dubon2026

/-! Exact unfolded consumers for the currently implemented source interfaces. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology

theorem positive_index_foundation_source (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) =
      RiemannZeta.dirichletPoly (fun n => a n.val) (positiveIndices N) s :=
  dirichletSum_eq_foundation a N s

theorem principal_power_source (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) =
      ∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-s * (Real.log n : ℂ)) :=
  dirichletSum_eq_sum_exp a N s

theorem entire_truncation_source (a : ℕ → ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) Set.univ :=
  analyticOnNhd_dirichletSum a N

theorem actual_support_maximum_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    1 ≤ lastIndex a N ∧ lastIndex a N ≤ N ∧ a (lastIndex a N) ≠ 0 ∧
      ∀ n, 1 ≤ n → n ≤ N → a n ≠ 0 → n ≤ lastIndex a N := by
  refine ⟨one_le_lastIndex hN ha, lastIndex_le a N,
    coefficient_lastIndex_ne_zero hN ha, ?_⟩
  intro n hn hupper hne
  exact le_lastIndex (mem_coefficientSupport.mpr ⟨hn, hupper, hne⟩)

theorem finite_analytic_multiplicity_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (s : ℂ) :
    (zeroMultiplicity a N s : ℕ∞) =
      analyticOrderAt (fun z : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-z)) s ∧
    analyticOrderAt (fun z : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-z)) s ≠ ⊤ :=
  ⟨zeroMultiplicity_cast hN ha s, analyticOrderAt_dirichletSum_ne_top hN ha s⟩

theorem actual_zero_rectangle_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (left right T : ℝ) (s : ℂ) :
    s ∈ zerosInOpenRectangleFinset a N hN ha left right T ↔
      left < s.re ∧ s.re < right ∧ |s.im| < T ∧
        (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) = 0 :=
  mem_zerosInOpenRectangleFinset a N hN ha left right T s

theorem multiplicity_weighted_count_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (left right T : ℝ) :
    verticalZeroCount a N hN ha left right T =
      ∑ s ∈ zerosInOpenRectangleFinset a N hN ha left right T,
        analyticOrderNatAt (fun z : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-z)) s :=
  rfl

theorem bohr_vertical_substitution_source (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-(σ : ℂ)) *
      ∏ p : PrimeCoordinate N,
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log p.val : ℂ)) ^ n.factorization p.val) =
      ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * t)) :=
  bohrLift_verticalFlow a N σ t

theorem trivial_prime_resonance_source (N : ℕ) (k : PrimeCoordinate N → ℤ)
    (h : (∑ p : PrimeCoordinate N, (k p : ℝ) * Real.log p.val) = 0) : k = 0 := by
  funext p
  exact prime_log_integer_independent k h p

theorem haar_probability_source (N : ℕ) : torusHaar N Set.univ = 1 :=
  measure_univ

theorem continuous_torus_test_source (N : ℕ) (f : C(PrimeTorus N, ℂ)) :
    Tendsto (fun T : ℝ => (2 * T)⁻¹ • ∫ t in -T..T,
      f (fun p => ((-t * Real.log p.val / (2 * Real.pi) : ℝ) : UnitAddCircle)))
      atTop (𝓝 (∫ z, f z ∂torusHaar N)) :=
  tendsto_torusAverage N f

theorem continuous_polynomial_test_source (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (φ : C(ℂ, ℂ)) :
    Tendsto (fun T : ℝ => (2 * T)⁻¹ • ∫ t in -T..T,
      φ (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * t))))
      atTop (𝓝 (∫ z, φ (bohrOnTorus a N σ z) ∂torusHaar N)) :=
  tendsto_vertical_polynomial_test a N σ φ

theorem quadratic_haar_energy_source (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    (∫ z, ‖bohrOnTorus a N σ z‖ ^ 2 ∂torusHaar N) =
      ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) :=
  integral_norm_sq_bohrOnTorus a N σ

theorem multivariate_log_integrability_source {ι : Type} [Fintype ι]
    (p : MvPolynomial ι ℂ) (hp : p ≠ 0) :
    (∀ᵐ z ∂circleProductHaar ι, MvPolynomial.eval (fun i => fourier 1 (z i)) p ≠ 0) ∧
    Integrable (fun z => Real.log ‖MvPolynomial.eval (fun i => fourier 1 (z i)) p‖)
      (circleProductHaar ι) :=
  ⟨polynomialOnTorus_ne_zero_ae p hp, integrable_polynomial_log p⟩

theorem actual_bohr_polynomial_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (σ : ℝ) :
    polynomialOnTorus (bohrPolynomial a N σ) = bohrOnTorus a N σ ∧
      (bohrPolynomial a N σ).coeff 0 = a 1 :=
  ⟨polynomialOnTorus_bohrPolynomial a N σ, coeff_zero_bohrPolynomial a hN σ⟩

theorem actual_haar_log_integrability_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (ha : a 1 = 1) (σ : ℝ) :
    (∀ᵐ z ∂torusHaar N, bohrOnTorus a N σ z ≠ 0) ∧
    Integrable (fun z => Real.log ‖bohrOnTorus a N σ z‖) (torusHaar N) :=
  ⟨bohrOnTorus_ne_zero_ae hN (ha.trans_ne one_ne_zero) σ,
    integrable_bohrOnTorus_log a N σ⟩

theorem normalized_haar_log_bounds_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (ha : a 1 = 1) (σ : ℝ) :
    0 ≤ (∫ z, Real.log ‖bohrOnTorus a N σ z‖ ∂torusHaar N) ∧
    (∫ z, Real.log ‖bohrOnTorus a N σ z‖ ∂torusHaar N) ≤
      Real.log (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) / 2 :=
  haarLogPotential_bounds hN ha σ

theorem vertical_log_integrability_source (a : ℕ → ℂ) (N : ℕ) (σ left right : ℝ) :
    IntervalIntegrable (fun t => Real.log ‖∑ n ∈ Finset.Icc 1 N,
      a n * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * t))‖) volume left right :=
  intervalIntegrable_vertical_log a N σ left right

theorem truncated_vertical_then_haar_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ t in -T..T,
        Real.log (max ‖dirichletSum a N ((σ : ℂ) + Complex.I * t)‖ ε)) atTop
        (𝓝 (∫ z, Real.log (max ‖bohrOnTorus a N σ z‖ ε) ∂torusHaar N))) ∧
    Tendsto (fun ε : ℝ => ∫ z, Real.log (max ‖bohrOnTorus a N σ z‖ ε) ∂torusHaar N)
      (𝓝[>] 0) (𝓝 (∫ z, Real.log ‖bohrOnTorus a N σ z‖ ∂torusHaar N)) :=
  ⟨fun _ hε => tendsto_truncated_vertical_log a N σ hε, tendsto_haar_truncated_log hN ha σ⟩

theorem actual_vertical_mean_upper_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop,
      (2 * T)⁻¹ * (∫ t in -T..T, Real.log ‖dirichletSum a N ((σ : ℂ) + Complex.I * t)‖) ≤
        (∫ z, Real.log ‖bohrOnTorus a N σ z‖ ∂torusHaar N) + δ :=
  eventually_verticalLogMean_le_haar_add hN ha σ hδ

theorem actual_uniform_log_tail_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    ∃ (K : ℕ) (η C : ℝ), 0 < K ∧ 0 < η ∧ 0 < C ∧
      ∀ R : ℝ, 0 ≤ R → ∀ T : ℝ, 1 ≤ T →
        (2 * T)⁻¹ * (∫ t in -T..T,
          (Real.log (max ‖∑ n ∈ Finset.Icc 1 N,
            a n * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * t))‖
              (η * Real.exp (-(K : ℝ) * R))) -
          Real.log ‖∑ n ∈ Finset.Icc 1 N,
            a n * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * t))‖)) ≤
          2 * (K : ℝ) * C * Real.exp (-R) :=
  exists_uniform_vertical_logTruncationError_bound hN ha σ

theorem actual_jessen_mean_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (σ : ℝ) :
    Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ t in -T..T,
      Real.log ‖∑ n ∈ Finset.Icc 1 N,
        a n * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * t))‖) atTop
      (𝓝 (∫ z, Real.log ‖bohrOnTorus a N σ z‖ ∂torusHaar N)) ∧
    jessenFunction a N σ = (∫ z, Real.log ‖bohrOnTorus a N σ z‖ ∂torusHaar N) ∧
    0 ≤ jessenFunction a N σ ∧
      jessenFunction a N σ ≤
        Real.log (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) / 2 :=
  ⟨tendsto_verticalLogMean_haar hN (ha.trans_ne one_ne_zero) σ,
    jessenFunction_eq_haar hN (ha.trans_ne one_ne_zero) σ, jessenFunction_bounds hN ha σ⟩

theorem bohr_jessen_proposition_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) :
    ConvexOn ℝ Set.univ (jessenFunction a N) ∧ Continuous (jessenFunction a N) ∧
      ∀ σ : ℝ,
        Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ t in -T..T,
          Real.log ‖∑ n ∈ Finset.Icc 1 N,
            a n * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * t))‖) atTop
          (𝓝 (jessenFunction a N σ)) ∧
        jessenFunction a N σ = (∫ z, Real.log ‖bohrOnTorus a N σ z‖ ∂torusHaar N) :=
  ⟨convexOn_jessenFunction hN (ha.trans_ne one_ne_zero),
    continuous_jessenFunction hN (ha.trans_ne one_ne_zero),
    fun σ => ⟨tendsto_verticalLogMean_jessen hN (ha.trans_ne one_ne_zero) σ,
      jessenFunction_eq_haar hN (ha.trans_ne one_ne_zero) σ⟩⟩

theorem actual_jessen_measure_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) :
    jessenMeasure hN (ha.trans_ne one_ne_zero) Set.univ =
      ENNReal.ofReal (Real.log (lastIndex a N)) ∧
    (∀ l u : ℝ, jessenMeasure hN (ha.trans_ne one_ne_zero) (Set.Ioo l u) =
      ENNReal.ofReal (derivWithin (jessenFunction a N) (Set.Iio u) u -
        derivWithin (jessenFunction a N) (Set.Ioi l) l)) ∧
    (∀ x : ℝ, jessenMeasure hN (ha.trans_ne one_ne_zero) {x} =
      ENNReal.ofReal (derivWithin (jessenFunction a N) (Set.Ioi x) x -
        derivWithin (jessenFunction a N) (Set.Iio x) x)) ∧
    (ENNReal.ofReal (1 / (2 * Real.pi)) •
      jessenMeasure hN (ha.trans_ne one_ne_zero)) Set.univ =
        ENNReal.ofReal (Real.log (lastIndex a N) / (2 * Real.pi)) :=
  ⟨jessenMeasure_univ hN ha, jessenMeasure_Ioo hN (ha.trans_ne one_ne_zero),
    jessenMeasure_singleton hN (ha.trans_ne one_ne_zero), scaledJessenMeasure_univ hN ha⟩

theorem actual_jessen_probability_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (hM : 1 < lastIndex a N) :
    IsProbabilityMeasure ((ENNReal.ofReal (Real.log (lastIndex a N)))⁻¹ •
      jessenMeasure hN (ha.trans_ne one_ne_zero)) :=
  normalizedJessenMeasure_isProbability hN ha hM

theorem actual_jessen_asymptotes_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) :
    Tendsto (jessenFunction a N) atTop (𝓝 0) ∧
      Tendsto (fun σ => jessenFunction a N σ + σ * Real.log (lastIndex a N)) atBot
        (𝓝 (Real.log ‖a (lastIndex a N)‖)) :=
  ⟨tendsto_jessenFunction_atTop hN ha,
    tendsto_jessenFunction_affine_atBot hN (ha.trans_ne one_ne_zero)⟩

theorem actual_rectangle_count_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (l u T : ℝ) (hlu : l ≤ u) (hT : 0 ≤ T)
    (hb : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) ≠ 0) :
    RectangleIntegral' (logDeriv (fun s : ℂ =>
      ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s))) (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ) =
      ((∑ s ∈ zerosInOpenRectangleFinset a N hN (ha.trans_ne one_ne_zero) l u T,
        analyticOrderNatAt (fun w : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-w)) s) : ℕ) :=
  rectangleIntegral_logDeriv_eq_verticalZeroCount hN (ha.trans_ne one_ne_zero) hlu hT hb

theorem actual_uniform_local_zero_bound_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (l u : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (S : Finset ℂ),
      (∀ s ∈ S, l ≤ s.re ∧ s.re ≤ u ∧ |s.im - τ| ≤ 1 ∧
        (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) = 0) →
      (∑ s ∈ S, (analyticOrderNatAt (fun w : ℂ =>
        ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-w)) s : ℝ)) ≤ C :=
  exists_uniform_unit_strip_zero_bound hN (ha.trans_ne one_ne_zero) l u

theorem actual_zero_height_control_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (l u : ℝ) :
    (∃ L U : ℝ, L < U ∧ ∀ s : ℂ,
      (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) = 0 → L < s.re ∧ s.re < U) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T U : ℝ, 0 ≤ T → T ≤ U → U ≤ T + 1 →
      (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u U : ℝ) ≤
        (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) + B :=
  ⟨exists_zero_containing_vertical_strip hN (ha.trans_ne one_ne_zero),
    exists_verticalZeroCount_unit_increment_bound hN (ha.trans_ne one_ne_zero) l u⟩

theorem actual_nearby_height_limit_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (l u : ℝ) (U : ℝ → ℝ) (L : ℝ)
    (hU : ∀ᶠ T in atTop, T ≤ U T ∧ U T ≤ T + 1)
    (hlim : Tendsto (fun T => (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u (U T) : ℝ) /
      (2 * U T)) atTop (𝓝 L)) :
    Tendsto (fun T => (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) /
      (2 * T)) atTop (𝓝 L) :=
  tendsto_verticalZeroCount_of_nearby_heights hN (ha.trans_ne one_ne_zero) l u hU hlim

theorem binomial_normalization_potential_source (κ : ℝ) (hκ : 0 < κ) :
    (∀ σ : ℝ, Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ t in -T..T,
      Real.log ‖1 + Complex.exp (-(κ : ℂ) * ((σ : ℂ) + Complex.I * t))‖) atTop
        (𝓝 (max 0 (-κ * σ)))) ∧
    (convexDerivativeStieltjes (convexOn_binomialJessen hκ)).measure =
      ENNReal.ofReal κ • Measure.dirac 0 ∧
    (∀ s : ℂ, 1 + Complex.exp (-(κ : ℂ) * s) = 0 ↔
      ∃ m : ℤ, s = (((2 * (m : ℝ) + 1) * Real.pi / κ : ℝ) : ℂ) * Complex.I) ∧
    ∀ s : ℂ, 1 + Complex.exp (-(κ : ℂ) * s) = 0 →
      analyticOrderNatAt (fun w : ℂ => 1 + Complex.exp (-(κ : ℂ) * w)) s = 1 :=
  ⟨tendsto_binomial_vertical_log_mean hκ, binomialJessenMeasure_eq_dirac hκ,
    binomialDirichlet_zero_iff hκ.ne', fun _ hs => analyticOrderNatAt_binomial_zero hκ.ne' hs⟩

theorem binomial_normalization_count_source (κ : ℝ) (hκ : 0 < κ) :
    (∀ T : ℝ, ∀ s : ℂ, s ∈ binomialZerosFinset κ T ↔ |s.im| < T ∧
      1 + Complex.exp (-(κ : ℂ) * s) = 0) ∧
    Tendsto (fun T : ℝ =>
      (((∑ s ∈ binomialZerosFinset κ T, analyticOrderNatAt
        (fun w : ℂ => 1 + Complex.exp (-(κ : ℂ) * w)) s) : ℕ) : ℝ) / (2 * T)) atTop
      (𝓝 (κ / (2 * Real.pi))) ∧
    ∀ l u : ℝ,
      Tendsto (fun T : ℝ => (binomialStripZeroCount κ l u T : ℝ) / (2 * T)) atTop
        (𝓝 (((ENNReal.ofReal (1 / (2 * Real.pi)) • binomialJessenMeasure hκ)
          (Set.Ioo l u)).toReal)) :=
  ⟨mem_binomialZerosFinset hκ, tendsto_binomialVerticalZeroCount hκ,
    binomial_open_strip_frequency hκ⟩

theorem isolated_prime_support_normalization_source (a : ℕ → ℂ) (Q : ℕ → Finset ℕ) (α : ℝ)
    (ha : a 1 = 1)
    (hQ : ∀ N p, p ∈ Q N → Nat.Prime p ∧ (N : ℝ) / 2 < p ∧ p ≤ N)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : ∀ l u : ℝ, l ≤ u → u < α → ∃ K : ℝ, 1 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ∀ σ ∈ Set.Icc l u, ∀ p ∈ Q N, ∀ q ∈ Q N,
        K⁻¹ ≤ (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ∧
        (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ≤ K) :
    (∀ᶠ N : ℕ in atTop,
      (N : ℝ) / 2 < lastIndex a N ∧ lastIndex a N ≤ N ∧ 1 < lastIndex a N) ∧
    Tendsto (fun N => (lastIndex a N : ℝ)) atTop atTop ∧
    Tendsto (fun N => Real.log (lastIndex a N) / Real.log N) atTop (𝓝 1) ∧
    ∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N,
      IsProbabilityMeasure ((ENNReal.ofReal (Real.log (lastIndex a N)))⁻¹ •
        jessenMeasure hN (ha.trans_ne one_ne_zero)) :=
  ⟨eventually_isolated_lastIndex_bounds hQ hcard hc, tendsto_isolated_lastIndex_atTop hQ hcard hc,
    tendsto_isolated_log_lastIndex_ratio hQ hcard hc, eventually_isolated_jessen_probability ha hQ hcard hc⟩

theorem bessel_series_integral_bounds_source :
    (∀ u : ℝ, HasSum (fun n : ℕ =>
      (-1 : ℝ) ^ n / (n.factorial : ℝ) ^ 2 * (u / 2) ^ (2 * n)) (besselJ0 u)) ∧
    (∀ u : ℝ,
      ((∑' n : ℕ, (-1 : ℝ) ^ n / (n.factorial : ℝ) ^ 2 * (u / 2) ^ (2 * n) : ℝ) : ℂ) =
        (2 * Real.pi)⁻¹ • ∫ θ in 0..2 * Real.pi,
          Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ))) ∧
    (∀ u : ℝ, |besselJ0 u| ≤ 1) ∧
    (∀ u : ℝ, u ≠ 0 → |besselJ0 u| < 1) ∧
    (∀ u : ℝ, |u| ≤ 1 → |besselJ0 u| ≤ Real.exp (-u ^ 2 / Real.pi ^ 2)) ∧
    ∀ u : ℝ, 1 ≤ u → |besselJ0 u| ≤ (4 + 1 / Real.pi) * u ^ (-(1 / 2 : ℝ)) :=
  ⟨fun u => (hasSum_besselJ0 u).summable.hasSum, besselJ0_eq_circle_integral,
    abs_besselJ0_le_one, fun _ hu => abs_besselJ0_lt_one hu,
    fun _ hu => abs_besselJ0_le_gaussian hu, fun _ hu => abs_besselJ0_le_rpow hu⟩

theorem circle_radial_fourier_source (ξ : ℂ) (c : ℝ) (hc : 0 ≤ c) :
    (∫ z : UnitAddCircle, Complex.exp
      (Complex.I * ((((starRingEnd ℂ) ξ * ((c : ℂ) * fourier 1 z)).re : ℝ) : ℂ))
      ∂AddCircle.haarAddCircle) = (besselJ0 (c * ‖ξ‖) : ℂ) ∧
    (∫ z : UnitAddCircle, Complex.exp
      (-(2 * Real.pi : ℝ) * Complex.I *
        ((((starRingEnd ℂ) ξ * ((c : ℂ) * fourier 1 z)).re : ℝ) : ℂ))
      ∂AddCircle.haarAddCircle) = (besselJ0 (2 * Real.pi * c * ‖ξ‖) : ℂ) :=
  ⟨circle_radial_characteristic ξ hc, circle_radial_fourier ξ hc⟩

theorem actual_steinhaus_law_source {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    IsProbabilityMeasure ((Measure.pi (fun _ : ι => AddCircle.haarAddCircle)).map
      (fun z : ι → UnitAddCircle => ∑ i, (c i : ℂ) * fourier 1 (z i))) ∧
    ∀ ξ : ℂ, charFun ((Measure.pi (fun _ : ι => AddCircle.haarAddCircle)).map
      (fun z : ι → UnitAddCircle => ∑ i, (c i : ℂ) * fourier 1 (z i))) ξ =
        ∏ i, (besselJ0 (c i * ‖ξ‖) : ℂ) :=
  ⟨steinhausLaw_isProbabilityMeasure c, charFun_steinhausLaw c hc⟩

theorem actual_steinhaus_normalization_source {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (K : ℝ) (hK : 1 ≤ K)
    (hcomp : (Finset.univ.sup' Finset.univ_nonempty b) /
      (Finset.univ.inf' Finset.univ_nonempty b) ≤ K) :
    0 < Real.sqrt (∑ i, b i ^ 2) ∧
    (∑ i, (b i / Real.sqrt (∑ j, b j ^ 2)) ^ 2) = 1 ∧
    ∀ i, 1 / (K * Real.sqrt (Fintype.card ι)) ≤ b i / Real.sqrt (∑ j, b j ^ 2) ∧
      b i / Real.sqrt (∑ j, b j ^ 2) ≤ K / Real.sqrt (Fintype.card ι) :=
  ⟨steinhausScale_pos b hb, sum_normalizedSteinhausCoefficients_sq b hb,
    normalizedSteinhausCoefficients_bounds b hb hK (steinhaus_pairwise_of_max_min b hb hK hcomp)⟩

theorem uniform_steinhaus_planar_L1_source (K : ℝ) (hK : 1 ≤ K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (b : κ → ℝ), (∀ i, 0 < b i) → 5 ≤ Fintype.card κ →
      (Finset.univ.sup' Finset.univ_nonempty b) /
        (Finset.univ.inf' Finset.univ_nonempty b) ≤ K →
      let μ := (Measure.pi (fun _ : κ => AddCircle.haarAddCircle)).map
        (fun z : κ → UnitAddCircle => ∑ i,
          ((b i / Real.sqrt (∑ j, b j ^ 2) : ℝ) : ℂ) * fourier 1 (z i))
      IsProbabilityMeasure μ ∧ Integrable (charFun μ) ∧ (∫ ξ : ℂ, ‖charFun μ ξ‖) ≤ L := by
  obtain ⟨L, hL, hbound⟩ := exists_uniform_steinhaus_charFun_L1 hK
  refine ⟨L, hL, ?_⟩
  intro κ _ _ b hb hm hcomp
  exact ⟨steinhausLaw_isProbabilityMeasure (normalizedSteinhausCoefficients b),
    hbound κ b hb hm hcomp⟩

theorem uniform_steinhaus_density_smallBall_source (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (b : κ → ℝ), (∀ i, 0 < b i) → 5 ≤ Fintype.card κ →
      (Finset.univ.sup' Finset.univ_nonempty b) /
        (Finset.univ.inf' Finset.univ_nonempty b) ≤ K →
      let μ := (Measure.pi (fun _ : κ => AddCircle.haarAddCircle)).map
        (fun z : κ → UnitAddCircle => ∑ i,
          ((b i / Real.sqrt (∑ j, b j ^ 2) : ℝ) : ℂ) * fourier 1 (z i))
      let f := fun x : ℂ =>
        (((2 * Real.pi) ^ 2)⁻¹ • ∫ ξ : ℂ,
          Complex.exp (-Complex.I * (inner ℝ x ξ : ℝ)) * charFun μ ξ).re
      Continuous f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ C) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      (∀ a : ℂ, ∀ r : ℝ, 0 ≤ r →
        μ {z : ℂ | ‖a + z‖ ≤ r} ≤ ENNReal.ofReal (C * Real.pi * r ^ 2)) ∧
      (∀ a : ℂ, ∀ᵐ z ∂μ, a + z ≠ 0) :=
  exists_uniform_steinhaus_density_smallBall hK

theorem translated_haar_steinhaus_log_source (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (b : κ → ℝ), (∀ i, 0 < b i) → 5 ≤ Fintype.card κ →
      (Finset.univ.sup' Finset.univ_nonempty b) /
        (Finset.univ.inf' Finset.univ_nonempty b) ≤ K → ∀ a : ℂ,
      Integrable (fun z : κ → UnitAddCircle =>
        Real.log ‖a + ∑ i, (b i : ℂ) * fourier 1 (z i)‖)
        (Measure.pi (fun _ : κ => AddCircle.haarAddCircle)) ∧
      Real.log (Real.sqrt (∑ i, b i ^ 2)) - C ≤
        ∫ z : κ → UnitAddCircle, Real.log ‖a + ∑ i, (b i : ℂ) * fourier 1 (z i)‖
          ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle) :=
  exists_uniform_steinhaus_log hK

theorem translated_independent_steinhaus_log_source (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (b : κ → ℝ), (∀ i, 0 < b i) → 5 ≤ Fintype.card κ →
      (Finset.univ.sup' Finset.univ_nonempty b) /
        (Finset.univ.inf' Finset.univ_nonempty b) ≤ K →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : κ → Ω → ℂ), (∀ i, Measurable (Z i)) → ProbabilityTheory.iIndepFun Z P →
        (∀ i, P.map (Z i) = AddCircle.haarAddCircle.map
          (fun z : UnitAddCircle => fourier 1 z)) → ∀ a : ℂ,
      Integrable (fun ω => Real.log ‖a + ∑ i, (b i : ℂ) * Z i ω‖) P ∧
      Real.log (Real.sqrt (∑ i, b i ^ 2)) - C ≤
        ∫ ω, Real.log ‖a + ∑ i, (b i : ℂ) * Z i ω‖ ∂P :=
  steinhaus_translated_logarithmic_estimate hK

theorem isolated_prime_finite_lower_source (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → ℂ) (N : ℕ), 1 ≤ N → a 1 = 1 →
      ∀ (σ : ℝ) (Q : Finset ℕ) [Nonempty ↥Q],
      (∀ p ∈ Q, Nat.Prime p ∧ (N : ℝ) / 2 < p ∧ p ≤ N) → 5 ≤ Q.card →
      (∀ p ∈ Q, a p ≠ 0) →
      (Finset.univ.sup' Finset.univ_nonempty (fun p : ↥Q => ‖a p.val‖ * (p.val : ℝ) ^ (-σ))) /
        (Finset.univ.inf' Finset.univ_nonempty (fun p : ↥Q => ‖a p.val‖ * (p.val : ℝ) ^ (-σ))) ≤ K →
      (1 / 2 : ℝ) * Real.log (∑ p ∈ Q, ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ)) - C ≤
        jessenFunction a N σ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_isolated_prime_lower_max_min hK
  refine ⟨C, hC, ?_⟩
  intro a N hN ha σ Q _ hQ hm hap hcomp
  exact hbound a N hN (ha.trans_ne one_ne_zero) σ Q hQ hm hap hcomp

theorem isolated_prime_compact_lower_source (a : ℕ → ℂ) (Q : ℕ → Finset ℕ) (α : ℝ)
    (ha : a 1 = 1)
    (hQ : ∀ N p, p ∈ Q N → Nat.Prime p ∧ (N : ℝ) / 2 < p ∧ p ≤ N)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : ∀ l u : ℝ, l ≤ u → u < α → ∃ K : ℝ, 1 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ∀ σ ∈ Set.Icc l u, ∀ p ∈ Q N, ∀ q ∈ Q N,
        K⁻¹ ≤ (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ∧
        (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ≤ K) :
    ∀ l u : ℝ, l ≤ u → u < α → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ σ ∈ Set.Icc l u,
        (1 / 2 : ℝ) * Real.log (∑ p ∈ Q N, ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ)) - C ≤
          jessenFunction a N σ :=
  fun _ _ hlu hu => eventually_isolated_jessen_lower ha hQ hcard hc hlu hu

theorem abstract_potential_limit_source (a : ℕ → ℂ) (Q : ℕ → Finset ℕ) (α : ℝ)
    (ha : a 1 = 1)
    (hQ : ∀ N p, p ∈ Q N → Nat.Prime p ∧ (N : ℝ) / 2 < p ∧ p ≤ N)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : ∀ l u : ℝ, l ≤ u → u < α → ∃ K : ℝ, 1 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ∀ σ ∈ Set.Icc l u, ∀ p ∈ Q N, ∀ q ∈ Q N,
        K⁻¹ ≤ (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ∧
        (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ≤ K)
    (hH1 : ∀ σ : ℝ, Tendsto (fun N : ℕ =>
      Real.log (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) / (2 * Real.log N))
      atTop (𝓝 (max (α - σ) 0)))
    (hH2 : TendstoLocallyUniformlyOn
      (fun N : ℕ => fun σ : ℝ =>
        Real.log (∑ p ∈ Q N, ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ)) / (2 * Real.log N))
      (fun σ => α - σ) atTop (Set.Iio α)) :
    TendstoLocallyUniformly (fun N : ℕ => fun σ : ℝ => jessenFunction a N σ / Real.log N)
      (fun σ => max (α - σ) 0) atTop ∧
    Tendsto (fun N : ℕ => Real.log (lastIndex a N) / Real.log N) atTop (𝓝 1) :=
  ⟨tendstoLocallyUniformly_normalizedJessen ha hQ hcard hc hH1 hH2,
    tendsto_isolated_log_lastIndex_ratio hQ hcard hc⟩

theorem abstract_concentration_source (a : ℕ → ℂ) (Q : ℕ → Finset ℕ) (α : ℝ)
    (ha : a 1 = 1)
    (hQ : ∀ N p, p ∈ Q N → Nat.Prime p ∧ (N : ℝ) / 2 < p ∧ p ≤ N)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : ∀ l u : ℝ, l ≤ u → u < α → ∃ K : ℝ, 1 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ∀ σ ∈ Set.Icc l u, ∀ p ∈ Q N, ∀ q ∈ Q N,
        K⁻¹ ≤ (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ∧
        (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ≤ K)
    (hH1 : ∀ σ : ℝ, Tendsto (fun N : ℕ =>
      Real.log (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) / (2 * Real.log N))
      atTop (𝓝 (max (α - σ) 0)))
    (hH2 : TendstoLocallyUniformlyOn
      (fun N : ℕ => fun σ : ℝ =>
        Real.log (∑ p ∈ Q N, ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ)) / (2 * Real.log N))
      (fun σ => α - σ) atTop (Set.Iio α)) :
    TendstoLocallyUniformly (fun N : ℕ => fun σ : ℝ => jessenFunction a N σ / Real.log N)
      (fun σ => max (α - σ) 0) atTop ∧
    Tendsto (fun N : ℕ => Real.log (lastIndex a N) / Real.log N) atTop (𝓝 1) ∧
    IsTightMeasureSet (Set.range (fun N => (jessenProbability ha N : Measure ℝ))) ∧
    Tendsto (jessenProbability ha) atTop
      (𝓝 (⟨Measure.dirac α, inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun N => ∫ x, f x ∂(jessenProbability ha N : Measure ℝ)) atTop (𝓝 (f α))) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex a N ∧
      (jessenProbability ha N : Measure ℝ) =
        (ENNReal.ofReal (Real.log (lastIndex a N)))⁻¹ •
          (jessenStieltjes hN (ha.trans_ne one_ne_zero)).measure) :=
  abstract_jessen_concentration ha hQ hcard hc hH1 hH2

theorem dyadic_prime_count_source :
    let Q : ℕ → Finset ℕ := fun N => (Finset.Ioc (N / 2) N).filter Nat.Prime
    (∀ N p, p ∈ Q N ↔ Nat.Prime p ∧ (N : ℝ) / 2 < p ∧ p ≤ N) ∧
    (∀ N, (Q N).card = Nat.primeCounting N - Nat.primeCounting (N / 2)) ∧
    Tendsto (fun N : ℕ => ((Q N).card : ℝ) / ((N : ℝ) / Real.log N)) atTop (𝓝 (1 / 2)) ∧
    Tendsto (fun N => (Q N).card) atTop atTop ∧
    Tendsto (fun N : ℕ => Real.log (Q N).card / Real.log N) atTop (𝓝 1) :=
  ⟨fun _ _ => mem_dyadicPrimes, card_dyadicPrimes, tendsto_card_dyadicPrimes_ratio,
    tendsto_card_dyadicPrimes, tendsto_log_card_dyadicPrimes_ratio⟩

theorem zeta_energy_source :
    (∀ σ : ℝ, Tendsto (fun N : ℕ =>
      Real.log (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)) / (2 * Real.log N))
      atTop (𝓝 (max (1 / 2 - σ) 0))) ∧
    (∀ l u : ℝ, l ≤ u → u < 1 / 2 → ∃ K : ℝ, 1 ≤ K ∧
      ∀ᶠ N : ℕ in atTop, ∀ σ ∈ Set.Icc l u, ∀ p ∈ dyadicPrimes N, ∀ q ∈ dyadicPrimes N,
        K⁻¹ ≤ (p : ℝ) ^ (-σ) / (q : ℝ) ^ (-σ) ∧
        (p : ℝ) ^ (-σ) / (q : ℝ) ^ (-σ) ≤ K) ∧
    TendstoLocallyUniformly (fun N : ℕ => fun σ : ℝ =>
      Real.log (∑ p ∈ dyadicPrimes N, (p : ℝ) ^ (-2 * σ)) / (2 * Real.log N))
      (fun σ => 1 / 2 - σ) atTop := by
  simpa only [PrimeCoefficientComparability, norm_one, one_mul] using zeta_energy_hypotheses

theorem zeta_concentration_source :
    TendstoLocallyUniformly (fun N : ℕ => fun σ : ℝ =>
      jessenFunction (fun _ => (1 : ℂ)) N σ / Real.log N)
      (fun σ => max (1 / 2 - σ) 0) atTop ∧
    (∀ N : ℕ, ∀ hN : 2 ≤ N,
      (jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ) =
        (ENNReal.ofReal (Real.log N))⁻¹ •
          (jessenStieltjes (a := fun _ => (1 : ℂ)) (by omega : 1 ≤ N) one_ne_zero).measure) ∧
    IsTightMeasureSet (Set.range (fun N =>
      (jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ))) ∧
    Tendsto (jessenProbability (a := fun _ => (1 : ℂ)) rfl) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun N =>
      (jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ)
        {x | ε ≤ |x - 1 / 2|}) atTop (𝓝 0)) :=
  ⟨zeta_jessen_concentration.1, fun _ hN => zeta_jessenProbability_eq hN,
    zeta_jessen_concentration.2.1, zeta_jessen_concentration.2.2.1,
    zeta_jessen_concentration.2.2.2.2⟩

theorem character_energy_source (q : ℕ) (hq : 0 < q) (χ : DirichletCharacter ℂ q) :
    (∀ N : ℕ, ∀ σ : ℝ,
      (∑ n ∈ Finset.Icc 1 N, ‖χ (n : ZMod q)‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) =
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ) ^ (-2 * σ)) ∧
    (∀ σ : ℝ, Tendsto (fun N : ℕ =>
      Real.log (∑ n ∈ Finset.Icc 1 N, ‖χ (n : ZMod q)‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) /
        (2 * Real.log N)) atTop (𝓝 (max (1 / 2 - σ) 0))) ∧
    TendstoLocallyUniformly (fun N : ℕ => fun σ : ℝ =>
      Real.log (∑ p ∈ dyadicPrimes N, ‖χ (p : ZMod q)‖ ^ 2 * (p : ℝ) ^ (-2 * σ)) /
        (2 * Real.log N)) (fun σ => 1 / 2 - σ) atTop := by
  letI : NeZero q := ⟨hq.ne'⟩
  exact ⟨character_coefficientEnergy_eq χ, globalEnergyAsymptotic_character χ,
    tendstoLocallyUniformly_character_isolatedEnergy χ⟩

theorem character_concentration_source (q : ℕ) (hq : 0 < q) (χ : DirichletCharacter ℂ q) :
    TendstoLocallyUniformly (fun N : ℕ => fun σ : ℝ =>
      jessenFunction (fun n => χ (n : ZMod q)) N σ / Real.log N)
      (fun σ => max (1 / 2 - σ) 0) atTop ∧
    Tendsto (fun N : ℕ => Real.log (lastIndex (fun n => χ (n : ZMod q)) N) / Real.log N)
      atTop (𝓝 1) ∧
    IsTightMeasureSet (Set.range (fun N =>
      (jessenProbability (characterCoefficients_one χ) N : Measure ℝ))) ∧
    Tendsto (jessenProbability (characterCoefficients_one χ)) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex (fun n => χ (n : ZMod q)) N ∧
      (jessenProbability (characterCoefficients_one χ) N : Measure ℝ) =
        (ENNReal.ofReal (Real.log (lastIndex (fun n => χ (n : ZMod q)) N)))⁻¹ •
          (jessenStieltjes hN ((characterCoefficients_one χ).trans_ne one_ne_zero)).measure) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun N =>
      (jessenProbability (characterCoefficients_one χ) N : Measure ℝ)
        {x | ε ≤ |x - 1 / 2|}) atTop (𝓝 0)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hh := dirichlet_jessen_concentration χ
  exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.2,
    fun _ hε => tendsto_dirichlet_jessenProbability_outside χ hε⟩

theorem character_sharp_energy_source (q : ℕ) (hq : 0 < q) (χ : DirichletCharacter ℂ q) :
    (∀ N : ℕ, ∀ σ : ℝ,
      (∑ n ∈ Finset.Icc 1 N, ‖χ (n : ZMod q)‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) =
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ) ^ (-2 * σ)) ∧
    (∀ σ : ℝ, σ < 1 / 2 → Tendsto (fun N : ℕ =>
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ) ^ (-2 * σ)) -
        ((q.totient : ℝ) / q) * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ)) /
          (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |(∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ)⁻¹) -
        ((q.totient : ℝ) / q) * Real.log N| ≤ C) ∧
    (∀ σ : ℝ, 1 / 2 < σ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      0 ≤ (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ) ^ (-2 * σ)) ∧
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ) ^ (-2 * σ)) ≤ C) := by
  letI : NeZero q := ⟨hq.ne'⟩
  refine ⟨character_coefficientEnergy_eq χ, ?_, ?_, ?_⟩
  · intro σ hσ
    simpa only [character_coefficientEnergy_eq] using character_energy_left_asymptotic χ hσ
  · simpa only [character_coefficientEnergy_eq,
      show -2 * (1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one] using
      character_energy_center_error χ
  · intro σ hσ
    simpa only [character_coefficientEnergy_eq] using character_energy_right_bounded χ hσ

theorem horizontal_argument_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 = 1) :
    (∀ t : ℝ, ∃ Z : Finset ℝ, (∀ σ : ℝ, σ ∈ Z ↔
      (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * t))).re = 0) ∧
        Z.card < N) ∧
    (∀ t l u : ℝ, l ≤ u →
      (∀ σ ∈ Set.Icc l u,
        (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * t))) ≠ 0) →
      |(∫ σ in l..u, logDeriv (fun z : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-z))
        ((σ : ℂ) + Complex.I * t)).im| ≤ Real.pi * (2 : ℝ) ^ N) :=
  ⟨fun t => horizontal_real_zero_finset hN ha t,
    fun t _ _ hlu hn => abs_im_horizontal_logDeriv_integral_le hN ha t hlu hn⟩

theorem finite_height_log_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 = 1)
    (T : ℝ) (hT : 0 ≤ T) :
    Continuous (fun σ : ℝ => (2 * T)⁻¹ * ∫ t in -T..T,
      Real.log ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * t))‖) ∧
    (∀ σ : ℝ, (∀ t ∈ Set.Icc (-T) T,
      (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * t))) ≠ 0) →
      HasDerivAt (fun x : ℝ => (2 * T)⁻¹ * ∫ t in -T..T,
        Real.log ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-((x : ℂ) + Complex.I * t))‖)
        ((∫ t in -T..T, logDeriv (fun s : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s))
          ((σ : ℂ) + Complex.I * t)).re / (2 * T)) σ) :=
  ⟨continuous_verticalLogMean hN (ha.trans_ne one_ne_zero) T hT,
    fun σ hn => hasDerivAt_verticalLogMean a N σ T hT hn⟩

theorem contour_error_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 = 1)
    (l u T : ℝ) (hlu : l ≤ u) (hT : 0 < T)
    (hb : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) ≠ 0) :
    |(verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) / (2 * T) -
      (((∫ t in -T..T, logDeriv (fun s : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s))
        ((u : ℂ) + Complex.I * t)).re / (2 * T)) -
        ((∫ t in -T..T, logDeriv (fun s : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s))
          ((l : ℂ) + Complex.I * t)).re / (2 * T))) / (2 * Real.pi)| ≤
            (2 : ℝ) ^ N / (2 * T) :=
  abs_zeroDensity_sub_verticalLogDerivMean_le hN ha hlu hT hb

theorem regular_zero_density_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 = 1)
    (l u dl du : ℝ) (hlu : l ≤ u)
    (hl : ∀ s : ℂ, s.re = l → (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) ≠ 0)
    (hu : ∀ s : ℂ, s.re = u → (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) ≠ 0)
    (hdl : HasDerivAt (jessenFunction a N) dl l)
    (hdu : HasDerivAt (jessenFunction a N) du u) :
    Tendsto (fun T => (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) /
      (2 * T)) atTop (𝓝 ((du - dl) / (2 * Real.pi))) :=
  tendsto_zeroDensity_regular_endpoints hN ha hlu hl hu hdl hdu

theorem atom_free_zero_density_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 = 1)
    (l u : ℝ) (hlu : l ≤ u)
    (hl : (jessenStieltjes hN (ha.trans_ne one_ne_zero)).measure {l} = 0)
    (hu : (jessenStieltjes hN (ha.trans_ne one_ne_zero)).measure {u} = 0) :
    Tendsto (fun T => ((∑ s ∈ zerosInOpenRectangleFinset a N hN
      (ha.trans_ne one_ne_zero) l u T, zeroMultiplicity a N s) : ℝ) / (2 * T)) atTop
        (𝓝 (((jessenStieltjes hN (ha.trans_ne one_ne_zero)).measure (Set.Ioo l u)).toReal /
          (2 * Real.pi))) := by
  simpa only [verticalZeroCount, jessenMeasure, Nat.cast_sum] using
    tendsto_zeroDensity_atom_free hN ha hlu hl hu

theorem total_zero_density_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 = 1) :
    (∀ (T : ℝ) (s : ℂ), s ∈ verticalZerosFinset a N hN (ha.trans_ne one_ne_zero) T ↔
      |s.im| < T ∧ (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) = 0) ∧
    Tendsto (fun T => ((∑ s ∈ verticalZerosFinset a N hN (ha.trans_ne one_ne_zero) T,
      zeroMultiplicity a N s) : ℝ) / (2 * T)) atTop
        (𝓝 (Real.log (lastIndex a N) / (2 * Real.pi))) := by
  refine ⟨mem_verticalZerosFinset a N hN (ha.trans_ne one_ne_zero), ?_⟩
  simpa only [totalVerticalZeroCount, Nat.cast_sum] using tendsto_totalVerticalZeroDensity hN ha

theorem zeta_zero_count_source :
    ∃ B : Set ℝ, B.Countable ∧ ∀ ε : ℝ, 0 < ε → ε ∉ B →
      ∃ D : ℕ → ℝ,
        (∀ (N : ℕ) (hN : 2 ≤ N), Tendsto (fun T =>
          ((∑ s ∈ (verticalZerosFinset (fun _ => (1 : ℂ)) N (by omega) one_ne_zero T).filter
            (fun s => ε ≤ |s.re - 1 / 2|), zeroMultiplicity (fun _ => (1 : ℂ)) N s) : ℝ) /
              (2 * T)) atTop (𝓝 (D N))) ∧
        Tendsto (fun N : ℕ => (2 * Real.pi / Real.log N) * D N) atTop (𝓝 0) := by
  simpa only [outsideVerticalZeroCount, Nat.cast_sum] using zeta_zero_count_concentration_off_countable

theorem zeta_count_tail_source (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∃ hN : 2 ≤ N, ∀ᶠ T : ℝ in atTop,
      (2 * Real.pi / Real.log N) *
        (((∑ s ∈ (verticalZerosFinset (fun _ => (1 : ℂ)) N (by omega) one_ne_zero T).filter
          (fun s => ε ≤ |s.re - 1 / 2|), zeroMultiplicity (fun _ => (1 : ℂ)) N s) : ℝ) /
            (2 * T)) < δ := by
  simpa only [outsideVerticalZeroCount, Nat.cast_sum] using zeta_outside_count_eventually_small hε hδ

theorem zeta_atom_free_count_source (ε : ℝ) (hε : 0 < ε)
    (hb : ∀ N : ℕ, 2 ≤ N →
      (jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ) {1 / 2 - ε} = 0 ∧
      (jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ) {1 / 2 + ε} = 0) :
    ∃ D : ℕ → ℝ,
      (∀ (N : ℕ) (hN : 2 ≤ N), Tendsto (fun T =>
        ((∑ s ∈ (verticalZerosFinset (fun _ => (1 : ℂ)) N (by omega) one_ne_zero T).filter
          (fun s => ε ≤ |s.re - 1 / 2|), zeroMultiplicity (fun _ => (1 : ℂ)) N s) : ℝ) /
            (2 * T)) atTop (𝓝 (D N))) ∧
      Tendsto (fun N : ℕ => (2 * Real.pi / Real.log N) * D N) atTop (𝓝 0) := by
  simpa only [outsideVerticalZeroCount, Nat.cast_sum] using zeta_zero_count_concentration hε hb

theorem coefficient_shift_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (ha : a 1 ≠ 0) (c : ℝ) :
    (∀ s : ℂ, (∑ n ∈ Finset.Icc 1 N, (a n * (n : ℂ) ^ (c : ℂ)) * (n : ℂ) ^ (-s)) =
      ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-(s - c))) ∧
    (∀ s : ℂ, zeroMultiplicity (fun n => a n * (n : ℂ) ^ (c : ℂ)) N s =
      zeroMultiplicity a N (s - c)) ∧
    (∀ σ : ℝ, jessenFunction (fun n => a n * (n : ℂ) ^ (c : ℂ)) N σ =
      jessenFunction a N (σ - c)) ∧
    jessenMeasure (a := fun n => a n * (n : ℂ) ^ (c : ℂ)) hN (by simpa using ha) =
      Measure.map (fun x : ℝ => x + c) (jessenMeasure hN ha) :=
  ⟨dirichletSum_shiftedCoefficients a N c, zeroMultiplicity_shiftedCoefficients a N c,
    jessenFunction_shiftedCoefficients a N c, jessenMeasure_shiftedCoefficients hN ha c⟩

open scoped MatrixGroups CongruenceSubgroup in
theorem cusp_coefficients_source (Q : ℕ) (k : ℤ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : (UpperHalfPlane.qExpansion 1 f).coeff 1 = 1) (N : ℕ) (hN : 1 ≤ N) :
    (∀ τ : UpperHalfPlane, HasSum (fun n => (UpperHalfPlane.qExpansion 1 f).coeff n *
      (Function.Periodic.qParam 1 τ) ^ n) (f τ)) ∧
    (UpperHalfPlane.qExpansion 1 f).coeff 0 = 0 ∧
    (∀ n : ℕ, ‖normalizedCuspCoefficients f n‖ =
      ‖(UpperHalfPlane.qExpansion 1 f).coeff n‖ * (n : ℝ) ^ (-((k : ℝ) - 1) / 2)) ∧
    (∀ s : ℂ, (∑ n ∈ Finset.Icc 1 N,
      (UpperHalfPlane.qExpansion 1 f).coeff n * (n : ℂ) ^ (-s)) =
        ∑ n ∈ Finset.Icc 1 N, normalizedCuspCoefficients f n *
          (n : ℂ) ^ (-(s - ((k : ℂ) - 1) / 2))) ∧
    jessenMeasure (a := fun n => (UpperHalfPlane.qExpansion 1 f).coeff n)
      hN (hf.trans_ne one_ne_zero) =
        Measure.map (fun x : ℝ => x + ((k : ℝ) - 1) / 2)
          (jessenMeasure (a := normalizedCuspCoefficients f) hN
            ((normalizedCuspCoefficients_one f hf).trans_ne one_ne_zero)) :=
  ⟨cuspCoefficients_hasSum f, cuspCoefficients_zero f, norm_normalizedCuspCoefficients f,
    dirichletSum_classicalCuspCoefficients f N,
    cusp_jessenMeasure_classical f (hf.trans_ne one_ne_zero) hN⟩

theorem sliding_window_integral_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (l u : ℝ) (T : ℝ) (hT : 0 ≤ T) :
    (∀ (τ : ℝ) (s : ℂ), s ∈ slidingZerosFinset a N hN
      (ha.trans_ne one_ne_zero) l u 1 τ ↔
        l < s.re ∧ s.re < u ∧ |s.im - τ| < 1 ∧
          (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) = 0) ∧
    (∫ t in -T..T, ((∑ s ∈ slidingZerosFinset a N hN
      (ha.trans_ne one_ne_zero) l u 1 t, zeroMultiplicity a N s) : ℝ)) =
      ∑ s ∈ zerosInOpenRectangleFinset a N hN (ha.trans_ne one_ne_zero) l u (T + 1),
        volume.real (Set.Ioc (-T) T ∩ Set.Ioo (s.im - 1) (s.im + 1)) *
          (zeroMultiplicity a N s : ℝ) := by
  refine ⟨fun τ s => mem_slidingZerosFinset a N hN (ha.trans_ne one_ne_zero) l u 1 τ s, ?_⟩
  simpa only [slidingZeroCount, windowOverlap, Nat.cast_sum] using
    integral_slidingZeroCount_eq a N hN (ha.trans_ne one_ne_zero) l u hT

/-- The actual phase regularity and the height limit are both derived. -/
theorem twist_count_frequency_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (l u : ℝ) :
    Tendsto (fun T : ℝ => ((∑ s ∈ zerosInOpenRectangleFinset a N hN
      (ha.trans_ne one_ne_zero) l u T, zeroMultiplicity a N s) : ℝ) / (2 * T)) atTop
      (𝓝 ((∫ z, ((∑ s ∈ zerosInOpenRectangleFinset (twistedCoefficients a N z) N hN
        (by rw [twistedCoefficients_one, ha]; exact one_ne_zero) l u 1,
          zeroMultiplicity (twistedCoefficients a N z) N s) : ℝ) ∂torusHaar N) / 2)) := by
  simpa only [twistZeroCount, verticalZeroCount, Nat.cast_sum] using
    tendsto_zeroDensity_torus_mean hN (ha.trans_ne one_ne_zero) l u

theorem twist_count_measurable_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (l u H : ℝ) :
    LowerSemicontinuous (fun z : PrimeTorus N =>
      ∑ s ∈ zerosInOpenRectangleFinset (twistedCoefficients a N z) N hN
        (by rw [twistedCoefficients_one, ha]; exact one_ne_zero) l u H,
          zeroMultiplicity (twistedCoefficients a N z) N s) ∧
    Measurable (fun z : PrimeTorus N =>
      ∑ s ∈ zerosInOpenRectangleFinset (twistedCoefficients a N z) N hN
        (by rw [twistedCoefficients_one, ha]; exact one_ne_zero) l u H,
          zeroMultiplicity (twistedCoefficients a N z) N s) :=
  ⟨lowerSemicontinuous_twistZeroCount hN (ha.trans_ne one_ne_zero) l u H,
    measurable_twistZeroCount hN (ha.trans_ne one_ne_zero) l u H⟩

theorem horizontal_phase_boundary_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (l u τ : ℝ) :
    ∀ᵐ z ∂torusHaar N, ∀ s : ℂ, l ≤ s.re → s.re ≤ u → s.im = τ →
      (∑ n ∈ Finset.Icc 1 N,
        (a n * bohrMonomial N n (fun p => fourier 1 (z p))) * (n : ℂ) ^ (-s)) ≠ 0 := by
  simpa only [dirichletSum, twistedCoefficients] using
    ae_horizontal_phase_closed_segment_ne_zero hN (ha.trans_ne one_ne_zero) l u τ

theorem mean_count_small_height_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (l u : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ H : ℝ, 0 ≤ H → H ≤ 1 →
      (∫ z, ((∑ s ∈ zerosInOpenRectangleFinset (twistedCoefficients a N z) N hN
        (by rw [twistedCoefficients_one, ha]; exact one_ne_zero) l u H,
          zeroMultiplicity (twistedCoefficients a N z) N s) : ℝ) ∂torusHaar N) ≤ K * H := by
  simpa only [twistZeroCount, verticalZeroCount, Nat.cast_sum] using
    exists_integral_twistZeroCount_le_height hN (ha.trans_ne one_ne_zero) l u

theorem complex_phase_extension_source (a : ℕ → ℂ) (N : ℕ)
    (xs : (PrimeCoordinate N → ℂ) × ℂ) (x : PrimeCoordinate N → ℝ) (s : ℂ) :
    AnalyticAt ℂ (fun ys : (PrimeCoordinate N → ℂ) × ℂ =>
      ∑ n ∈ Finset.Icc 1 N, (a n * ∏ p : PrimeCoordinate N,
        Complex.exp (2 * Real.pi * Complex.I * ys.1 p) ^ n.factorization p.val) *
          (n : ℂ) ^ (-ys.2)) xs ∧
    (∑ n ∈ Finset.Icc 1 N, (a n * ∏ p : PrimeCoordinate N,
      Complex.exp (2 * Real.pi * Complex.I * (x p : ℂ)) ^ n.factorization p.val) *
        (n : ℂ) ^ (-s)) =
      dirichletSum (twistedCoefficients a N (fun p => (x p : UnitAddCircle))) N s := by
  constructor
  · exact analyticAt_complexPhaseFamily a N xs
  · exact complexPhaseFamily_real a N x s

theorem weighted_zero_moments_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 = 1)
    (l u T : ℝ) (hlu : l ≤ u) (hT : 0 ≤ T)
    (hb : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) ≠ 0) (k : ℕ) :
    RectangleIntegral' (fun s => s ^ k * logDeriv (fun w : ℂ =>
      ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-w)) s) (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ) =
      ∑ s ∈ zerosInOpenRectangleFinset a N hN (ha.trans_ne one_ne_zero) l u T,
        s ^ k * (analyticOrderNatAt (fun w : ℂ =>
          ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-w)) s : ℂ) :=
  rectangleIntegral_power_logDeriv_eq_zero_power_sum hN (ha.trans_ne one_ne_zero) hlu hT hb k

theorem analytic_zero_polynomial_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (x : PrimeCoordinate N → ℂ)
    (l u T : ℝ) (hlu : l ≤ u) (hT : 0 ≤ T)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      dirichletSum (complexPhaseCoefficients a N x) N s ≠ 0) :
    (∀ k : ℕ, AnalyticAt ℂ (fun y =>
      (((rectangleZeroMultiset (complexPhaseCoefficients a N y) N hN
        (by rw [complexPhaseCoefficients_one, ha]; exact one_ne_zero) l u T).map
          (fun s => Polynomial.X - Polynomial.C s)).prod).coeff k) x) ∧
    (∀ (y : PrimeCoordinate N → ℂ) (s : ℂ),
      (((rectangleZeroMultiset (complexPhaseCoefficients a N y) N hN
        (by rw [complexPhaseCoefficients_one, ha]; exact one_ne_zero) l u T).map
          (fun z => Polynomial.X - Polynomial.C z)).prod).rootMultiplicity s =
      if s ∈ zerosInOpenRectangleFinset (complexPhaseCoefficients a N y) N hN
          (by rw [complexPhaseCoefficients_one, ha]; exact one_ne_zero) l u T then
        analyticOrderNatAt (dirichletSum (complexPhaseCoefficients a N y) N) s else 0) := by
  refine ⟨fun k => ?_, fun y s => ?_⟩
  · exact analyticAt_complexPhaseZeroPolynomial_coeff hN (ha.trans_ne one_ne_zero) x hlu hT hn k
  · exact rectangleZeroPolynomial_rootMultiplicity (complexPhaseCoefficients a N y) N hN
      (by rw [complexPhaseCoefficients_one, ha]; exact one_ne_zero) l u T s

theorem real_vertical_zero_polynomial_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (x : PrimeCoordinate N → ℝ)
    (l u T σ : ℝ) (hlu : l ≤ u) (hT : 0 ≤ T)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      dirichletSum (twistedCoefficients a N (fun p => (x p : UnitAddCircle))) N s ≠ 0) :
    (∀ k : ℕ, AnalyticAt ℝ (fun y =>
      (phaseVerticalRealPolynomial a N hN (ha.trans_ne one_ne_zero) l u T σ y).coeff k) x) ∧
    (∀ (y : PrimeCoordinate N → ℝ) (t : ℝ), l < σ → σ < u → |t| < T →
      (phaseVerticalRealPolynomial a N hN (ha.trans_ne one_ne_zero) l u T σ y).rootMultiplicity t =
        2 * analyticOrderNatAt (fun s : ℂ => ∑ n ∈ Finset.Icc 1 N,
          (a n * bohrMonomial N n (fun p => fourier 1 (y p : UnitAddCircle))) *
            (n : ℂ) ^ (-s)) ((σ : ℂ) + Complex.I * t)) := by
  have hn' : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      complexPhaseFamily a N (complexifyPhase x, s) ≠ 0 := by
    intro s hs
    change complexPhaseFamily a N ((fun p => (x p : ℂ)), s) ≠ 0
    rw [complexPhaseFamily_real]
    exact hn s hs
  refine ⟨fun k => analyticAt_phaseVerticalRealPolynomial_coeff hN (ha.trans_ne one_ne_zero)
    x hlu hT hn' σ k, ?_⟩
  intro y t hl hu ht
  exact phaseVerticalRealPolynomial_rootMultiplicity_interior a N hN
    (ha.trans_ne one_ne_zero) hl hu ht y

theorem actual_phase_polynomial_signs_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (x : PrimeCoordinate N → ℝ)
    (l u T σ : ℝ) (hlu : l ≤ u) (hT : 0 ≤ T)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      dirichletSum (twistedCoefficients a N (fun p => (x p : UnitAddCircle))) N s ≠ 0)
    (d q : ℕ) (p : Fin q → MvPolynomial (Fin d) ℝ) (F : (Fin q → SignType) → ℕ) :
    ∃ r > 0, ∀ᵐ y ∂(volume : Measure (PrimeCoordinate N → ℝ)).restrict (Metric.ball x r),
      ContinuousAt (fun z => F (fun i => SignType.sign (MvPolynomial.aeval
        (fun j : Fin d => (phaseVerticalRealPolynomial a N hN (ha.trans_ne one_ne_zero)
          l u T σ z).coeff j.val) (p i)))) y := by
  have hn' : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      complexPhaseFamily a N (complexifyPhase x, s) ≠ 0 := by
    intro s hs
    change complexPhaseFamily a N ((fun p => (x p : ℂ)), s) ≠ 0
    rw [complexPhaseFamily_real]
    exact hn s hs
  exact phase_coefficient_signs_locally_ae_continuous hN (ha.trans_ne one_ne_zero)
    x hlu hT hn' σ p F

theorem sturm_multiplicity_root_count_source (P : Polynomial ℝ) (hP : P ≠ 0) (l u : ℝ) :
    (∑ k ∈ Finset.range P.natDegree,
      sturmOpenCount (derivativeRootQuotient (derivativeGcdLayer P k)) l u) =
        (P.roots.filter (fun t => l < t ∧ t < u)).card :=
  sturmMultiplicityCount_eq_root_count hP l u

theorem actual_phase_sturm_vertical_count_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (x : PrimeCoordinate N → ℝ)
    {l u T H σ : ℝ} (hl : l < σ) (hu : σ < u) (hH : H ≤ T) :
    sturmMultiplicityCount
      (phaseVerticalRealPolynomial a N hN (ha.trans_ne one_ne_zero) l u T σ x) (-H) H =
      2 * ∑ s ∈ (zerosInOpenRectangleFinset
        (twistedCoefficients a N (fun p => (x p : UnitAddCircle))) N hN
        (by rw [twistedCoefficients_one, ha]; exact one_ne_zero) l u H).filter (fun s => s.re = σ),
          analyticOrderNatAt (fun w : ℂ => ∑ n ∈ Finset.Icc 1 N,
            (a n * bohrMonomial N n (fun p => fourier 1 (x p : UnitAddCircle))) *
              (n : ℂ) ^ (-w)) s :=
  phase_sturm_count_eq_twice_vertical_count a N hN (ha.trans_ne one_ne_zero) hl hu hH x

theorem almost_analytic_root_count_source {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (μ : Measure V) [Measure.IsAddHaarMeasure μ] {s : Set V} {P : V → Polynomial ℝ}
    {d : ℕ} (hd : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k : ℕ, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y)
    (l u : ℝ) :
    ∀ᵐ y ∂μ.restrict s, ∀ᶠ z in 𝓝 y,
      ((P z).roots.filter (fun t => l < t ∧ t < u)).card =
        ((P y).roots.filter (fun t => l < t ∧ t < u)).card :=
  ae_realPolynomialRootCount_locally_constant μ hd hP l u

theorem torus_vertical_multiplicity_regularity_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) {l u σ : ℝ} (hl : l < σ) (hu : σ < u) (H : ℝ) :
    ∀ᵐ z ∂torusHaar N, ContinuousAt (fun w : PrimeTorus N =>
      ∑ s ∈ (zerosInOpenRectangleFinset (twistedCoefficients a N w) N hN
        (by rw [twistedCoefficients_one, ha]; exact one_ne_zero) l u H).filter (fun s => s.re = σ),
          analyticOrderNatAt (fun v : ℂ => ∑ n ∈ Finset.Icc 1 N,
            (a n * bohrMonomial N n (fun p => fourier 1 (w p))) * (n : ℂ) ^ (-v)) s) z :=
  ae_torus_vertical_count_continuous hN (ha.trans_ne one_ne_zero) hl hu H

theorem torus_rectangle_multiplicity_regularity_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) (l u : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    ∀ᵐ z ∂torusHaar N, ContinuousAt (fun w : PrimeTorus N =>
      ∑ s ∈ zerosInOpenRectangleFinset (twistedCoefficients a N w) N hN
        (by rw [twistedCoefficients_one, ha]; exact one_ne_zero) l u H,
          analyticOrderNatAt (fun v : ℂ => ∑ n ∈ Finset.Icc 1 N,
            (a n * bohrMonomial N n (fun p => fourier 1 (w p))) * (n : ℂ) ^ (-v)) s) z :=
  ae_continuousAt_twistZeroCount hN (ha.trans_ne one_ne_zero) l u hH

theorem jessen_tornehave_all_endpoints_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 = 1) {l u : ℝ} (hlu : l < u) :
    Tendsto (fun T : ℝ => ((∑ s ∈ zerosInOpenRectangleFinset a N hN
      (ha.trans_ne one_ne_zero) l u T,
        analyticOrderNatAt (fun v : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-v)) s) : ℝ) /
          (2 * T)) atTop (𝓝 ((derivWithin (jessenFunction a N) (Set.Iio u) u -
            derivWithin (jessenFunction a N) (Set.Ioi l) l) / (2 * Real.pi))) := by
  simpa only [verticalZeroCount, zeroMultiplicity, dirichletSum, Nat.cast_sum] using
    tendsto_zeroDensity_one_sided_derivatives hN ha hlu

theorem zeta_all_endpoints_count_source (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ → ℝ,
      (∀ (N : ℕ) (hN : 2 ≤ N), Tendsto (fun T =>
        ((∑ s ∈ (verticalZerosFinset (fun _ => (1 : ℂ)) N (by omega) one_ne_zero T).filter
          (fun s => ε ≤ |s.re - 1 / 2|), zeroMultiplicity (fun _ => (1 : ℂ)) N s) : ℝ) /
            (2 * T)) atTop (𝓝 (D N))) ∧
      Tendsto (fun N : ℕ => (2 * Real.pi / Real.log N) * D N) atTop (𝓝 0) := by
  simpa only [outsideVerticalZeroCount, Nat.cast_sum] using zeta_zero_count_concentration_all_endpoints hε

theorem abstract_actual_zero_measure_source {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α)
    (hH1 : GlobalEnergyAsymptotic a α) (hH2 : IsolatedEnergyAsymptotic a Q α) :
    Tendsto (jessenProbability ha) atTop
      (𝓝 (⟨Measure.dirac α, inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex a N ∧ ∀ l u : ℝ,
      Tendsto (fun T : ℝ => (2 * Real.pi / Real.log (lastIndex a N)) *
        (((∑ s ∈ zerosInOpenRectangleFinset a N hN (ha.trans_ne one_ne_zero) l u T,
          analyticOrderNatAt (fun v : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-v)) s) : ℝ) /
            (2 * T))) atTop (𝓝 (((jessenProbability ha N : Measure ℝ) (Set.Ioo l u)).toReal))) := by
  have hh := abstract_actual_zero_concentration ha hQ hcard hc hH1 hH2
  simpa only [verticalZeroCount, zeroMultiplicity, dirichletSum, Nat.cast_sum] using hh.2.2.2

theorem dirichlet_actual_zero_measure_source {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Tendsto (jessenProbability (characterCoefficients_one χ)) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex (fun n => χ (n : ZMod q)) N ∧ ∀ l u : ℝ,
      Tendsto (fun T : ℝ => (2 * Real.pi / Real.log (lastIndex (fun n => χ (n : ZMod q)) N)) *
        (((∑ s ∈ zerosInOpenRectangleFinset (characterCoefficients χ) N hN
          ((characterCoefficients_one χ).trans_ne one_ne_zero) l u T,
            analyticOrderNatAt (fun v : ℂ => ∑ n ∈ Finset.Icc 1 N,
              χ (n : ZMod q) * (n : ℂ) ^ (-v)) s) : ℝ) / (2 * T))) atTop
                (𝓝 (((jessenProbability (characterCoefficients_one χ) N : Measure ℝ)
                  (Set.Ioo l u)).toReal))) := by
  have hh := dirichlet_actual_zero_concentration χ
  simpa only [verticalZeroCount, zeroMultiplicity, dirichletSum, Nat.cast_sum,
    characterCoefficients] using hh.2.2.2

/-- The dyadic prime count is derived from density among all primes and the actual PNT. -/
theorem selected_prime_density_source {S : ℕ → Prop} {η : ℝ}
    (hd : Tendsto (fun N : ℕ => ((selectedPrimesUpTo S N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 η)) :
    Tendsto (fun N : ℕ => ((selectedDyadicPrimes S N).card : ℝ) /
      ((N : ℝ) / Real.log N)) atTop (𝓝 (η / 2)) := selected_dyadic_density hd

/-- The source quadratic sum is locally uniform; its logarithmic limit is derived. -/
theorem selected_prime_energy_source {a : ℕ → ℂ} {S : ℕ → Prop} {η : ℝ} (hη : 0 < η)
    (hd : Tendsto (fun N : ℕ => ((selectedPrimesUpTo S N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 η))
    (hb : ∀ p, Nat.Prime p → S p → 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun σ : ℝ => Real.log
        (∑ p ∈ selectedDyadicPrimes S N, ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ)) /
          (2 * Real.log N)) (fun σ => 1 / 2 - σ) atTop (Set.Iio (1 / 2)) :=
  (selected_primes_H2 hη hd hb).2.2.2

/-- A cumulative mean-square limit is strictly narrower than this all-abscissa energy limit. -/
theorem mean_square_energy_source {a : ℕ → ℂ} {S : ℕ → Prop} {c η : ℝ}
    (ha : a 1 = 1)
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / N) atTop (𝓝 c))
    (hη : 0 < η)
    (hd : Tendsto (fun N : ℕ => ((selectedPrimesUpTo S N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 η))
    (hb : ∀ p, Nat.Prime p → S p → 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) (σ : ℝ) :
    Tendsto (fun N : ℕ => Real.log
      (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) / (2 * Real.log N))
      atTop (𝓝 (max (1 / 2 - σ) 0)) := by
  obtain ⟨hQ, hcard, hc, hH2⟩ := selected_primes_H2 hη hd hb
  exact globalEnergyAsymptotic_of_mean_isolated ha hmean hQ hcard hc hH2 σ

/-- Exact positive-index Abel formula; it includes sigma=0 and the critical exponent. -/
theorem weighted_energy_abel_source (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) (σ : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) =
      (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * (N : ℝ) ^ (-2 * σ) +
        2 * σ * ∫ x in Set.Ioc (1 : ℝ) N,
          (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖a n‖ ^ 2) * x ^ (-2 * σ - 1) := by
  simpa only [coefficientEnergy, squareSummatory, Nat.floor_natCast] using coefficientEnergy_abel a hN σ

open scoped MatrixGroups CongruenceSubgroup in
/-- The conditional classical limit uses the actual period-one Fourier coefficients. -/
theorem cusp_classical_conditional_source {Q : ℕ} {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : (UpperHalfPlane.qExpansion 1 f).coeff 1 = 1) {c density : ℝ}
    (hmean : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2) / N) atTop (𝓝 c))
    (hdensity : 0 < density)
    (hd : Tendsto (fun N : ℕ => ((selectedPrimesUpTo (cuspPrimeSelection f) N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 density)) :
    Tendsto (jessenProbability (a := fun n => (UpperHalfPlane.qExpansion 1 f).coeff n) hf) atTop
      (𝓝 (⟨Measure.dirac ((k : ℝ) / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  (cusp_concentration_of_mean_prime_density f hf hmean hdensity hd).2.2.2.1

/-- Exact finite quadratic sums and all three ranges from the literal cumulative O-estimate. -/
theorem rankin_selberg_three_regimes_source {a : ℕ → ℂ} {c : ℝ}
    (hRS : (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖a n‖ ^ 2) - c * x) =O[atTop]
      (fun x : ℝ => x ^ (3 / 5 : ℝ))) :
    (∀ σ : ℝ, σ < 1 / 2 → Tendsto (fun N : ℕ => ((∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) -
      c * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ)) /
        (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0)) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 : ℝ))) - c * Real.log N| ≤ B) ∧
    (∀ σ : ℝ, 1 / 2 < σ → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      0 ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) ∧ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) ≤ B) :=
  rankin_selberg_weighted_energy_of_bigO hRS

open scoped MatrixGroups CongruenceSubgroup in
theorem cusp_classical_rankin_selberg_source {Q : ℕ} {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : (UpperHalfPlane.qExpansion 1 f).coeff 1 = 1) {c density : ℝ}
    (hRS : (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖normalizedCuspCoefficients f n‖ ^ 2) - c * x) =O[atTop]
      (fun x : ℝ => x ^ (3 / 5 : ℝ)))
    (hdensity : 0 < density)
    (hd : Tendsto (fun N : ℕ => ((selectedPrimesUpTo (cuspPrimeSelection f) N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 density)) :
    Tendsto (jessenProbability (a := fun n => (UpperHalfPlane.qExpansion 1 f).coeff n) hf) atTop
      (𝓝 (⟨Measure.dirac ((k : ℝ) / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  (cusp_concentration_of_rankin_selberg_prime_density f hf hRS hdensity hd).2.2.2.1


/-- The actual angle-density measure and literal coefficient band, with derived normalization. -/
theorem sato_tate_measure_source :
    (∫ θ in Set.Icc (0 : ℝ) Real.pi, (2 / Real.pi) * Real.sin θ ^ 2) = 1 ∧
    0 < (Measure.map (fun θ : ℝ => 2 * Real.cos θ)
      ((volume.restrict (Set.Icc (0 : ℝ) Real.pi)).withDensity
        (fun θ => ENNReal.ofReal ((2 / Real.pi) * Real.sin θ ^ 2))))
          (Set.Icc (-2) (-1) ∪ Set.Icc 1 2) ∧
    (satoTateProbability : Measure ℝ) (frontier (Set.Icc (-2) (-1) ∪ Set.Icc 1 2)) = 0 :=
  ⟨integral_satoTateAngleDensity, satoTateBand_pos, satoTateBand_null_frontier⟩

open scoped Classical in
/-- Density uses the exact filtered primes and discards only primes dividing the positive level. -/
theorem sato_tate_prime_count_source {a : ℕ → ℂ} {Q : ℕ} (hQ : 0 < Q)
    (hreal : ∀ p, Nat.Prime p → ¬p ∣ Q → (a p).im = 0)
    (hST : Tendsto (primeEmpirical (fun p => (a p).re)) atTop (𝓝 satoTateProbability)) :
    0 < satoTateBandDensity ∧
    Tendsto (fun N : ℕ =>
      (((Nat.primesLE N).filter (fun p => ¬p ∣ Q ∧ 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2)).card : ℝ) /
        Nat.primeCounting N) atTop (𝓝 satoTateBandDensity) :=
  by
    refine ⟨satoTateBandDensity_pos, ?_⟩
    apply (sato_tate_selected_prime_density hQ hreal hST).congr'
    apply Filter.Eventually.of_forall
    intro N
    have he : selectedPrimesUpTo (fun p => ¬p ∣ Q ∧ 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) N =
        (Nat.primesLE N).filter (fun p => ¬p ∣ Q ∧ 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) := by
      apply Finset.ext
      intro p
      simp only [mem_selectedPrimesUpTo, Finset.mem_filter, Nat.mem_primesLE]
      tauto
    exact congrArg (fun B : Finset ℕ => (B.card : ℝ) / Nat.primeCounting N) he

open scoped MatrixGroups CongruenceSubgroup in
/-- Classical Fourier coefficients consume separate cumulative energy and Sato–Tate inputs. -/
theorem cusp_classical_arithmetic_source {Q : ℕ} {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : (UpperHalfPlane.qExpansion 1 f).coeff 1 = 1) (hQ : 0 < Q) {c : ℝ}
    (hRS : (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖normalizedCuspCoefficients f n‖ ^ 2) - c * x) =O[atTop]
      (fun x : ℝ => x ^ (3 / 5 : ℝ)))
    (hreal : ∀ p, Nat.Prime p → ¬p ∣ Q → (normalizedCuspCoefficients f p).im = 0)
    (hST : Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f p).re))
      atTop (𝓝 satoTateProbability)) :
    Tendsto (jessenProbability (a := fun n => (UpperHalfPlane.qExpansion 1 f).coeff n) hf) atTop
      (𝓝 (⟨Measure.dirac ((k : ℝ) / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  (cusp_concentration_of_rankin_selberg_sato_tate f hf hQ hRS hreal hST).2.2.2.1


open scoped MatrixGroups in
/-- The actual hyperbolic integral is integrable and detects a zero cusp form. -/
theorem petersson_integral_source {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (f : CuspForm Γ k) :
    IntegrableOn (fun τ : UpperHalfPlane =>
      starRingEnd ℂ (f τ) * f τ * (τ.im : ℂ) ^ k) ModularGroup.fd volume ∧
    ((∫ τ in ModularGroup.fd,
      starRingEnd ℂ (f τ) * f τ * (τ.im : ℂ) ^ k ∂(volume : Measure UpperHalfPlane)) = 0 → f = 0) :=
  ⟨peterssonInner_integrableOn k Γ f f, cuspForm_eq_zero_of_peterssonIntegral f⟩

open scoped MatrixGroups ModularForm in
/-- The level pairing is the literal sum over all Gamma0 cosets, with actual slash integrals. -/
theorem petersson_coset_definiteness_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    letI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 Q) := Subgroup.fintypeQuotientOfFiniteIndex
    (∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 Q,
      ∫ τ in ModularGroup.fd,
        starRingEnd ℂ ((⇑f ∣[k] q.out⁻¹) τ) * ((⇑f ∣[k] q.out⁻¹) τ) * (τ.im : ℂ) ^ k
          ∂(volume : Measure UpperHalfPlane)) = 0 → f = 0 := by
  intro h
  exact cuspPetersson_definite f h


open scoped MatrixGroups in
/-- The actual Gamma0 degeneracy map has the literal sparse q-expansion. -/
theorem degeneracy_coefficient_source {M N : ℕ} (d : ℕ) [NeZero d] (h : d * M ∣ N)
    {k : ℤ} (f : CuspForm ((CongruenceSubgroup.Gamma0 M).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (cuspDegeneracyMap d h k f)).coeff n =
      if d ∣ n then (UpperHalfPlane.qExpansion 1 f).coeff (n / d) else 0 :=
  cuspDegeneracyMap_coeff d h f n

/-- The actual oldspace is zero at level one and its Petersson complement is full. -/
theorem level_one_newspace_source (k : ℤ) :
    cuspOldspace 1 k = ⊥ ∧ cuspNewspace 1 k = ⊤ :=
  ⟨cuspOldspace_one k, cuspNewspace_one k⟩

/-- The actual discriminant witnesses the missing ordinary inclusion at level two. -/
theorem ordinary_inclusion_counterexample_source :
    cuspCoefficients (levelDiscriminant 2) 1 = 1 ∧
    levelDiscriminant 2 ∈ cuspOldspace 2 12 ∧
    levelDiscriminant 2 ∉ strictCuspDilationSpan 2 12 :=
  ⟨levelDiscriminant_coeff_one 2, levelDiscriminant_mem_oldspace (by norm_num),
    levelDiscriminant_not_strictDilationSpan 2⟩


open scoped MatrixGroups in
/-- The literal divisor Fourier sum converges to the actual finite Hecke function. -/
theorem classical_hecke_fourier_source {Q : ℕ} {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (n : ℕ) (τ : UpperHalfPlane) :
    HasSum (fun m => (∑ d ∈ n.divisors, if Nat.Coprime d Q ∧ d ∣ m then
      (d : ℂ) ^ (k - 1) * (UpperHalfPlane.qExpansion 1 f).coeff ((n / d) * (m / d)) else 0) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (classicalHeckeFunction Q k n f τ) :=
  hasSum_classicalHeckeFunction Q k n f (cuspCoefficients f) τ
    (fun σ => by simpa only [smul_eq_mul] using cuspCoefficients_hasSum f σ)

/-- The genuine primitive-form object supplies the exact good-index multiplicativity. -/
theorem primitive_coefficients_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {n m : ℕ} (hn : 0 < n)
    (hnQ : Nat.Coprime n Q) (hnm : Nat.Coprime n m) :
    (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff (n * m) =
      (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n *
        (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff m :=
  cuspHeckeEigenform_coefficient_mul f.toCuspForm f.normalized f.isEigen hn hnQ hnm

open scoped MatrixGroups in
/-- Actual quadratic prime self-twists survive normalization and mean inert-prime vanishing. -/
theorem quadratic_self_twist_source {Q D : ℕ} {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic) :
    (∀ p : ℕ, Nat.Prime p → Nat.Coprime p (Q * D) →
      χ (p : ZMod D) * normalizedCuspCoefficients f p = normalizedCuspCoefficients f p) ↔
    ∀ p : ℕ, Nat.Prime p → Nat.Coprime p (Q * D) → χ (p : ZMod D) = -1 →
      (UpperHalfPlane.qExpansion 1 f).coeff p = 0 :=
  (cusp_selfTwist_normalization_iff f χ).trans
    (coefficientSelfTwist_iff_inert_zero χ hχ (cuspCoefficients f))


open scoped MatrixGroups Manifold in
/-- The literal finite Hecke function is holomorphic and vanishes at every cusp. -/
theorem hecke_cusp_behavior_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (n : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (classicalHeckeFunction Q k n f) ∧
    ∀ c : OnePoint ℝ, IsCusp c ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) →
      c.IsZeroAt (classicalHeckeFunction Q k n f) k :=
  ⟨classicalHeckeFunction_holomorphic Q k n f f.holo',
    fun _ hc => classicalHeckeFunction_zero_at_cusps Q k n f hc⟩

open scoped MatrixGroups in
/-- A genuine same-level cusp form realizes the actual prime operator and its two-term expansion. -/
theorem prime_hecke_cusp_source {Q p : ℕ} [NeZero Q] [NeZero p] {k : ℤ}
    (hp : Nat.Prime p)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    ∃ g : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k,
      (∀ τ, g τ = classicalHeckeFunction Q k p f τ) ∧
      ∀ m : ℕ, (UpperHalfPlane.qExpansion 1 g).coeff m =
        (UpperHalfPlane.qExpansion 1 f).coeff (p * m) +
        if Nat.Coprime p Q ∧ p ∣ m then (p : ℂ) ^ (k - 1) *
          (UpperHalfPlane.qExpansion 1 f).coeff (m / p) else 0 :=
  ⟨cuspHeckePrime hp f, fun _ => rfl, cuspHeckePrime_coeff_prime hp f⟩


open scoped MatrixGroups in
/-- Every literal classical finite Hecke sum is an actual same-level cusp form with exact coefficients. -/
theorem all_index_hecke_cusp_source {Q : ℕ} [NeZero Q] {k : ℤ} (n : ℕ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    ∃ g : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k,
      (∀ τ, g τ = classicalHeckeFunction Q k n f τ) ∧
      ∀ m, (UpperHalfPlane.qExpansion 1 g).coeff m =
        ∑ d ∈ n.divisors, if Nat.Coprime d Q ∧ d ∣ m then
          (d : ℂ) ^ (k - 1) * (UpperHalfPlane.qExpansion 1 f).coeff ((n / d) * (m / d)) else 0 :=
  exists_cuspForm_hecke_function n f

/-- The actual same-level operators satisfy the good/bad-prime recurrence. -/
theorem hecke_prime_power_source (Q : ℕ) [NeZero Q] (k : ℤ)
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (r : ℕ) :
    cuspHeckeLinear Q k (p ^ (r + 2)) =
      cuspHeckeLinear Q k p * cuspHeckeLinear Q k (p ^ (r + 1)) -
        (if Nat.Coprime p Q then (p : ℂ) ^ (k - 1) else 0) • cuspHeckeLinear Q k (p ^ r) :=
  cuspHeckeLinear_primePower_recurrence Q k hp r

open scoped MatrixGroups in
/-- Commutativity acts on actual cusp forms and the literal analytic Hecke formula. -/
theorem hecke_commuting_functions_source {Q : ℕ} [NeZero Q] {k : ℤ} (m n : ℕ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (τ : UpperHalfPlane) :
    classicalHeckeFunction Q k m (classicalHeckeFunction Q k n f) τ =
      classicalHeckeFunction Q k n (classicalHeckeFunction Q k m f) τ := by
  have h := LinearMap.congr_fun (cuspHeckeLinear_commute Q k m n).eq f
  have he := congrArg (fun g => g τ) h
  change cuspHecke m (cuspHecke n f) τ = cuspHecke n (cuspHecke m f) τ at he
  simpa only [cuspHecke_apply, funext (cuspHecke_apply n f), funext (cuspHecke_apply m f)] using he


open scoped MatrixGroups Pointwise in
/-- The actual Gamma0 coset pairing is the literal integral over its genuine faithful domain. -/
theorem gamma0_petersson_domain_source (Q : ℕ) [NeZero Q] {k : ℤ}
    (f g : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    MeasureTheory.IsFundamentalDomain (realProjectiveGamma0 Q)
      (gamma0FundamentalDomain Q) (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) ∧
    cuspPetersson f g = ∫ τ in gamma0FundamentalDomain Q,
      starRingEnd ℂ (f τ) * g τ * (τ.im : ℂ) ^ k
        ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) :=
  ⟨isFundamentalDomain_realGamma0 Q, cuspPetersson_eq_gamma0Domain_integral Q f g⟩

open scoped MatrixGroups ModularForm Pointwise in
/-- The genuine matrix slash moves across the literal hyperbolic integral with the exact determinant. -/
theorem petersson_inverse_slash_source (k : ℤ) (f g : UpperHalfPlane → ℂ)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) (S : Set UpperHalfPlane) :
    ∫ τ in S, UpperHalfPlane.petersson k (f ∣[k] A) g τ
      ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) =
      (A.det.val : ℂ) ^ (k - 2) * ∫ τ in A • S,
        UpperHalfPlane.petersson k f (g ∣[k] A⁻¹) τ
          ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) :=
  peterssonIntegral_slash_left k f g A hA S

end Dubon2026.SemanticRegression
