import Dubon2026

/-! Exact unfolded consumers for the currently implemented source interfaces. -/

namespace Dubon2026.SemanticRegression

open Filter MeasureTheory
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

end Dubon2026.SemanticRegression
