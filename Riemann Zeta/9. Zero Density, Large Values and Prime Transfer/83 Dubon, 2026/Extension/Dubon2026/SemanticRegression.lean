import Dubon2026
import Dubon2026.ArithmeticSemanticRegression

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

theorem isolated_prime_two_sided_source (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → ℂ) (N : ℕ), 1 ≤ N → a 1 ≠ 0 →
      ∀ (I : Set ℝ) (Q : Finset ℕ),
      (∀ p ∈ Q, Nat.Prime p ∧ (N : ℝ) / 2 < p ∧ p ≤ N) → 5 ≤ Q.card →
      (∀ σ ∈ I, ∀ p ∈ Q, ∀ q ∈ Q,
        K⁻¹ ≤ (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ∧
        (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ≤ K) →
      ∀ σ ∈ I, (1 / 2 : ℝ) * Real.log (∑ p ∈ Q, ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ)) - C ≤
        jessenFunction a N σ :=
  exists_uniform_isolated_prime_lower_two_sided hK

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


open scoped MatrixGroups in
/-- The two explicit p+1 families uniquely represent the actual congruence subgroup cosets. -/
theorem prime_hecke_transversals_source {p Q : ℕ} (hp : Nat.Prime p)
    (hpQ : Nat.Coprime p Q) :
    (∀ γ : CongruenceSubgroup.Gamma0 Q, ∃! x : Option (ZMod p),
      heckeUpperRepresentative p Q hpQ x * γ ∈ heckeUpperSubgroup Q p) ∧
    (∀ γ : CongruenceSubgroup.Gamma0 Q, ∃! x : Option (ZMod p),
      heckeLowerRepresentative p Q hpQ x * γ ∈ heckeLowerSubgroup Q p) := by
  constructor
  · intro γ
    obtain ⟨x, hx⟩ := heckeUpperCoset_surjective hp hpQ (QuotientGroup.mk γ)
    refine ⟨x, (heckeUpperCoset_eq_iff hpQ x γ).mp hx, ?_⟩
    intro y hy
    exact heckeUpperCoset_injective hp hpQ (((heckeUpperCoset_eq_iff hpQ y γ).mpr hy).trans hx.symm)
  · intro γ
    obtain ⟨x, hx⟩ := heckeLowerCoset_surjective hp hpQ (QuotientGroup.mk γ)
    refine ⟨x, (heckeLowerCoset_eq_iff hpQ x γ).mp hx, ?_⟩
    intro y hy
    exact heckeLowerCoset_injective hp hpQ (((heckeLowerCoset_eq_iff hpQ y γ).mpr hy).trans hx.symm)

open scoped MatrixGroups ModularForm Pointwise in
/-- The literal adjugate slash is the exact mixed adjoint after moving the integration domain. -/
theorem petersson_adjugate_source (k : ℤ) (f g : UpperHalfPlane → ℂ)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) (S : Set UpperHalfPlane) :
    ∫ τ in S, UpperHalfPlane.petersson k (f ∣[k] A) g τ
      ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) =
      ∫ τ in A • S, UpperHalfPlane.petersson k f (g ∣[k] peterssonAdj A) τ
        ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) :=
  peterssonInner_slash_adjugate S A hA f g


open scoped MatrixGroups in
/-- Actual classical Hecke functions move across the literal Gamma0 Petersson integral at good indices. -/
theorem good_hecke_petersson_source {Q : ℕ} [NeZero Q] {k : ℤ} (n : ℕ)
    (hnQ : Nat.Coprime n Q)
    (f g : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    (∫ τ in gamma0FundamentalDomain Q,
      starRingEnd ℂ (classicalHeckeFunction Q k n f τ) * g τ * (τ.im : ℂ) ^ k
        ∂(volume : Measure UpperHalfPlane)) =
      ∫ τ in gamma0FundamentalDomain Q,
        starRingEnd ℂ (f τ) * classicalHeckeFunction Q k n g τ * (τ.im : ℂ) ^ k
          ∂(volume : Measure UpperHalfPlane) := by
  have h := cuspHeckeLinear_coprime_selfAdjoint Q k n hnQ f g
  change cuspPetersson (cuspHecke n f) g = cuspPetersson f (cuspHecke n g) at h
  rw [cuspPetersson_eq_gamma0Domain_integral Q, cuspPetersson_eq_gamma0Domain_integral Q] at h
  simpa only [UpperHalfPlane.petersson, cuspHecke_apply] using h

/-- The actual primitive q-expansion and its automorphic normalization are real at good indices. -/
theorem primitive_coefficient_reality_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (n : ℕ) (hnQ : Nat.Coprime n Q) :
    ((UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n).im = 0 ∧
      (normalizedCuspCoefficients f.toCuspForm n).im = 0 :=
  ⟨primitiveCuspForm_coefficient_im f n hnQ, primitiveCuspForm_normalizedCoefficient_im f n hnQ⟩

/-- The genuine primitive form consumes the literal Rankin–Selberg and Sato–Tate inputs with reality proved. -/
theorem primitive_classical_arithmetic_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {c : ℝ}
    (hRS : (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ‖normalizedCuspCoefficients f.toCuspForm n‖ ^ 2) - c * x) =O[atTop]
        (fun x : ℝ => x ^ (3 / 5 : ℝ)))
    (hST : Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability)) :
    Tendsto (jessenProbability (a := fun n => (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n)
      f.normalized) atTop
      (𝓝 (⟨Measure.dirac ((k : ℝ) / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  (primitive_concentration_of_rankin_selberg_sato_tate f hRS hST).2.2.2.1


open scoped MatrixGroups in
/-- Literal good-prime Hecke functions commute with every actual lower-level dilation. -/
theorem good_prime_degeneracy_source {M N p : ℕ} [NeZero M] [NeZero N] [NeZero p]
    (d : ℕ) [NeZero d] (h : d * M ∣ N) (k : ℤ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 M).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (τ : UpperHalfPlane) :
    classicalHeckeFunction N k p (cuspDegeneracyMap d h k f) τ =
      classicalHeckeFunction M k p f (levelRaiseMatrix d • τ) := by
  have he := DFunLike.congr_fun (cuspHeckeLinear_prime_degeneracy d h k hp hpN f) τ
  change cuspHecke p (cuspDegeneracyMap d h k f) τ =
    cuspDegeneracyMap d h k (cuspHecke p f) τ at he
  simpa only [cuspHecke_apply, cuspDegeneracyMap_apply] using he

open scoped MatrixGroups in
/-- The genuine good-index operators preserve both full classical old and new spaces. -/
theorem old_new_hecke_stability_source {N : ℕ} [NeZero N] {k : ℤ} (n : ℕ)
    (hnN : Nat.Coprime n N)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    (f ∈ cuspOldspace N k → cuspHecke n f ∈ cuspOldspace N k) ∧
      (f ∈ cuspNewspace N k → cuspHecke n f ∈ cuspNewspace N k) :=
  ⟨cuspOldspace_hecke_coprime N k n hnN f, cuspNewspace_hecke_coprime n hnN f⟩

open scoped MatrixGroups in
/-- Cauchy–Schwarz holds for the literal Gamma0-domain Petersson integrals. -/
theorem petersson_cauchy_schwarz_source {N : ℕ} [NeZero N] {k : ℤ}
    (f g : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    ‖∫ τ in gamma0FundamentalDomain N, UpperHalfPlane.petersson k f g τ
      ∂(volume : Measure UpperHalfPlane)‖ ≤
    Real.sqrt (∫ τ in gamma0FundamentalDomain N, UpperHalfPlane.petersson k f f τ
      ∂(volume : Measure UpperHalfPlane)).re *
    Real.sqrt (∫ τ in gamma0FundamentalDomain N, UpperHalfPlane.petersson k g g τ
      ∂(volume : Measure UpperHalfPlane)).re := by
  simpa only [cuspPetersson_eq_gamma0Domain_integral N] using norm_cuspPetersson_le f g

attribute [local instance] principalNormal
open scoped MatrixGroups ModularForm in
/-- Actual principal-level orbits are finite dimensional and retain the literal slash action. -/
theorem principal_finite_slash_orbit_source (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    FiniteDimensional ℂ (principalCuspOrbit N k f) ∧
      f ∈ principalCuspOrbit N k f ∧
      ∀ (γ : SL(2, ℤ)) (v : principalCuspOrbit N k f),
        ⇑(principalCuspOrbitRepresentation N k f (QuotientGroup.mk γ) v).val =
          ⇑v.val ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹ :=
  ⟨inferInstance, mem_principalCuspOrbit N k f, principalCuspOrbitRepresentation_apply N k f⟩


open scoped MatrixGroups in
/-- Every actual determinant-one residue matrix has a determinant-one integral lift. -/
theorem finite_sl2_integral_lift_source (N : ℕ) [NeZero N] (g : SL(2, ZMod N)) :
    ∃ γ : SL(2, ℤ), ∀ i j : Fin 2, (γ i j : ZMod N) = g i j := by
  obtain ⟨γ, hγ⟩ := SL2Reduction.SL2_reduction_surjective N g
  exact ⟨γ, fun i j => congrArg (fun h : SL(2, ZMod N) => h i j) hγ⟩

open scoped MatrixGroups in
/-- The actual rescaling preserves all coefficients when the cusp parameter is changed to period N. -/
theorem principal_rescaling_coefficients_source (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    (∀ τ : UpperHalfPlane, cuspRescaledPrincipal N k f τ = f (heckeUpperPoint N 0 τ)) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (cuspRescaledPrincipal N k f)).coeff n =
        (UpperHalfPlane.qExpansion 1 f).coeff n :=
  ⟨cuspRescaledPrincipal_apply N k f, cuspRescaledPrincipal_coeff N k f⟩

/-- The finite symmetric-operator decomposition used in the support-to-oldspace argument is proved. -/
theorem finite_symmetric_kernel_source {V I : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (s : Finset I)
    (A : I → V →ₗ[ℂ] V)
    (hc : Set.Pairwise (↑s) (fun i j => Commute (A i) (A j)))
    (hA : ∀ i ∈ s, ∀ x y, inner ℂ (A i x) y = inner ℂ x (A i y)) :
    LinearMap.ker (s.noncommProd A hc) = ⨆ i ∈ s, LinearMap.ker (A i) :=
  symmetric_ker_noncommProd s A hc hA

open scoped MatrixGroups in
/-- Literal finite translates of the rescaled source form extract exactly its divisible coefficients. -/
theorem principal_divisor_coefficients_source {N d : ℕ} [NeZero N] [NeZero d]
    (hd : d ∣ N) (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (n : ℕ) :
    (UpperHalfPlane.qExpansion N
      (principalDivisorProjection N k d (cuspRescaledPrincipal N k f))).coeff n =
        if d ∣ n then (UpperHalfPlane.qExpansion 1 f).coeff n else 0 := by
  change principalCuspCoefficients
    (principalDivisorProjection N k d (cuspRescaledPrincipal N k f)) n = _
  rw [principalDivisorProjection_coeff hd, cuspRescaledPrincipal_coeff]
  rfl

open scoped MatrixGroups in
/-- Coprime coefficient vanishing is equivalent to annihilation by the actual translation product. -/
theorem principal_coprime_annihilation_source (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    principalAvoidProjection N k N.primeFactors (fun _ hp => Nat.dvd_of_mem_primeFactors hp)
      (cuspRescaledPrincipal N k f) = 0 ↔
        ∀ n, N.Coprime n → (UpperHalfPlane.qExpansion 1 f).coeff n = 0 := by
  simpa only [cuspRescaledPrincipal_coeff, cuspCoefficients] using
    principalCoprimeProjection_eq_zero_iff N k (cuspRescaledPrincipal N k f)

open scoped MatrixGroups in
/-- All actual divisor projections share a positive invariant inner product on the finite orbit. -/
theorem principal_common_projection_core_source (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    ∃ c : InnerProductSpace.Core ℂ (principalCuspOrbit N k f),
      ∀ (d : ℕ) [NeZero d] (hd : d ∣ N) (x y : principalCuspOrbit N k f),
        c.inner (principalOrbitDivisorProjection hd k f x) y =
          c.inner x (principalOrbitDivisorProjection hd k f y) :=
  principalOrbitDivisorProjection_commonCore N k f

open scoped MatrixGroups in
/-- Actual sparse source coefficients force period one after literal divisor rescaling. -/
theorem sparse_rescaling_period_source {N : ℕ} {k : ℤ} (d : ℕ) [NeZero d]
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : ∀ n, ¬d ∣ n → (UpperHalfPlane.qExpansion 1 f).coeff n = 0)
    (τ : UpperHalfPlane) :
    f (heckeUpperPoint d 0 ((1 : ℝ) +ᵥ τ)) = f (heckeUpperPoint d 0 τ) :=
  cusp_sparse_rescaling_period d f hf τ

open scoped MatrixGroups in
/-- Actual sparse coefficients construct a genuine lower-level cusp form with the exact coefficient subsequence. -/
theorem sparse_lower_cusp_source {N d : ℕ} [NeZero N] [NeZero d] (hd : d ∣ N) (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : ∀ n, ¬d ∣ n → (UpperHalfPlane.qExpansion 1 f).coeff n = 0) :
    ∃ g : CuspForm ((CongruenceSubgroup.Gamma0 (N / d)).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k,
      (∀ τ : UpperHalfPlane, g τ = f (heckeUpperPoint d 0 τ)) ∧
      cuspDegeneracyMap d (by rw [Nat.mul_div_cancel' hd]) k g = f ∧
      ∀ n, (UpperHalfPlane.qExpansion 1 g).coeff n = (UpperHalfPlane.qExpansion 1 f).coeff (d * n) :=
  ⟨cuspSparseLower hd k f hf, cuspSparseLower_apply hd k f hf,
    cuspSparseLower_degeneracy hd k f hf, cuspSparseLower_coeff hd k f hf⟩

open scoped MatrixGroups in
/-- Genuine sparse cusp forms belong to the full classical oldspace, with proper divided level. -/
theorem sparse_oldspace_source {N d : ℕ} [NeZero N] [NeZero d] (hd : d ∣ N) (hd1 : 1 < d)
    (k : ℤ) (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : ∀ n, ¬d ∣ n → (UpperHalfPlane.qExpansion 1 f).coeff n = 0) :
    f ∈ cuspOldspace N k := cusp_sparse_mem_oldspace hd hd1 k f hf

open scoped MatrixGroups in
/-- At every positive prime-power level the actual newspace has no nonzero vector with all good coefficients zero. -/
theorem primePower_newspace_coprime_source {p r : ℕ} [NeZero p] (hp : Nat.Prime p)
    (hr : 0 < r) (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 (p ^ r)).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hnew : f ∈ cuspNewspace (p ^ r) k)
    (hf : ∀ n, (p ^ r).Coprime n → (UpperHalfPlane.qExpansion 1 f).coeff n = 0) : f = 0 :=
  cusp_primePower_new_coprime_eq_zero hp hr k f hnew hf

open scoped MatrixGroups in
/-- Each actual local matrix factor embeds with precisely one nonidentity component. -/
theorem prime_factor_embedding_source (N : ℕ) [NeZero N] (p : N.primeFactors)
    (g : SL(2, ZMod (p.val ^ N.factorization p.val))) :
    principalPrimeFactorsEquiv N (principalPrimeFactorEmbedding N p g) = Pi.mulSingle p g :=
  principalPrimeFactorEmbedding_components N p g


open scoped MatrixGroups in
/-- Distinct local lower averages commute with the actual prime Fourier projections. -/
theorem local_lower_divisor_commute_source (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (p q : N.primeFactors) [NeZero q.val] (hpq : p ≠ q) :
    Commute (principalLowerProjection N k f p)
      (principalOrbitDivisorProjection (Nat.dvd_of_mem_primeFactors q.property) k f) :=
  principalLowerDivisorProjection_cross_commute N k f p q hpq

open scoped MatrixGroups in
/-- Actual upper-invariant principal forms descend by literal dilation with every coefficient preserved. -/
theorem upper_descent_coefficient_source (N : ℕ) [NeZero N] (k : ℤ)
    (v : principalUpperInvariantSpace N k) :
    (∀ τ : UpperHalfPlane, principalUpperToGamma0 N k v τ = v.val (levelRaiseMatrix N • τ)) ∧
    ∀ n, (UpperHalfPlane.qExpansion 1 (principalUpperToGamma0 N k v)).coeff n =
      (UpperHalfPlane.qExpansion N v.val).coeff n :=
  ⟨principalUpperToGamma0_apply N k v, principalUpperToGamma0_coeff N k v⟩

open scoped MatrixGroups in
/-- Literal coprime q-expansion vanishing forces full classical oldspace membership at every positive level. -/
theorem coprime_oldspace_source (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : ∀ n, N.Coprime n → (UpperHalfPlane.qExpansion 1 f).coeff n = 0) :
    f ∈ cuspOldspace N k := cusp_coprime_support_old N k f hf

open scoped MatrixGroups in
/-- Two genuine newspace forms are equal when their actual coprime Fourier coefficients agree. -/
theorem newspace_coprime_uniqueness_source (N : ℕ) [NeZero N] (k : ℤ)
    (f g : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ∈ cuspNewspace N k) (hg : g ∈ cuspNewspace N k)
    (hfg : ∀ n, N.Coprime n → (UpperHalfPlane.qExpansion 1 f).coeff n =
      (UpperHalfPlane.qExpansion 1 g).coeff n) : f = g :=
  cusp_new_eq_of_coprime_coefficients N k f g hf hg hfg


open scoped MatrixGroups in
/-- Actual primitive good eigenvalues determine every genuine newspace eigenvector by its first coefficient. -/
theorem primitive_multiplicity_one_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k)
    (g : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hg : g ∈ cuspNewspace N k)
    (he : ∀ n, 0 < n → n.Coprime N → ∀ τ : UpperHalfPlane,
      classicalHeckeFunction N k n g τ = (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n * g τ) :
    g = (UpperHalfPlane.qExpansion 1 g).coeff 1 • f.toCuspForm := by
  apply primitiveCuspForm_same_eigensystem_scalar f g hg
  intro n hn hnN
  ext τ
  change cuspHecke n g τ = _
  rw [cuspHecke_apply]
  exact he n hn hnN τ

open scoped MatrixGroups in
/-- Actual cusp forms at every positive Gamma0 level form a finite-dimensional complex space. -/
theorem modular_finite_dimension_source (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :=
  ModularDimension.cuspForm_finiteDimensional (CongruenceSubgroup.Gamma0 N) k

open scoped MatrixGroups in
/-- Every actual cusp form decomposes into its full oldspace and Petersson-newspace components. -/
theorem petersson_old_new_decomposition_source (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    ∃ g h : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k,
      g ∈ cuspOldspace N k ∧ h ∈ cuspNewspace N k ∧ f = g + h :=
  ⟨cuspOldProjection N k f, f - cuspOldProjection N k f,
    cuspOldProjection_mem N k f, cusp_sub_oldProjection_new N k f, by abel⟩

open scoped MatrixGroups in
/-- Every literal all-index Hecke function of an actual oldform is again a genuine oldform. -/
theorem oldspace_all_hecke_source (N : ℕ) [NeZero N] (k : ℤ) (n : ℕ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ∈ cuspOldspace N k) :
    ∃ g : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k,
      g ∈ cuspOldspace N k ∧ ∀ τ : UpperHalfPlane, g τ = classicalHeckeFunction N k n f τ :=
  ⟨cuspHeckeLinear N k n f, cuspOldspace_hecke_all N k n f hf, cuspHecke_apply n f⟩

open scoped MatrixGroups in
/-- Genuine primitive forms satisfy the full literal analytic eigenfunction identity at every positive index. -/
theorem primitive_all_index_eigen_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (n : ℕ) (hn : 0 < n) (τ : UpperHalfPlane) :
    classicalHeckeFunction N k n f.toCuspForm τ =
      (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n * f.toCuspForm τ := by
  have he := DFunLike.congr_fun (primitiveCuspForm_eigenvector_all f hn) τ
  change cuspHecke n f.toCuspForm τ = _ at he
  rwa [cuspHecke_apply] at he

open scoped MatrixGroups in
/-- The actual primitive good eigenspace has dimension one and is separated by its first Fourier coefficient. -/
theorem primitive_eigenspace_dimension_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) :
    Module.finrank ℂ (primitiveGoodEigenSpace f) = 1 ∧
      Function.Injective (fun g : primitiveGoodEigenSpace f => (UpperHalfPlane.qExpansion 1 g.val).coeff 1) :=
  ⟨primitiveGoodEigenSpace_finrank f, primitiveGoodEigenSpace_firstCoefficient_injective f⟩


open scoped MatrixGroups in
/-- Actual primitive Fourier coefficients have all coprime products and the full good/bad recurrence. -/
theorem primitive_full_coefficients_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) :
    (∀ n m, n.Coprime m → (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff (n * m) =
      (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n * (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff m) ∧
    (∀ p, Nat.Prime p → p ∣ N → ∀ r,
      (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff (p ^ r) =
        (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff p ^ r) ∧
    ∀ p, Nat.Prime p → ∀ r,
      (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff (p ^ (r + 2)) =
        (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff p *
          (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff (p ^ (r + 1)) -
        (if p.Coprime N then (p : ℂ) ^ (k - 1) else 0) *
          (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff (p ^ r) :=
  ⟨primitiveCuspForm_coefficient_mul_all f,
    fun _ hp hpN r => primitiveCuspForm_bad_prime_power f hp hpN r,
    fun _ hp r => primitiveCuspForm_primePower_recurrence f hp r⟩

open scoped MatrixGroups in
/-- For actual primitive forms, the literal quadratic self-twist condition at primes extends to every coprime index. -/
theorem primitive_self_twist_coefficients_source {N D : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (χ : DirichletCharacter ℂ D) (hq : χ.IsQuadratic) :
    (∀ p, Nat.Prime p → p.Coprime (N * D) →
      χ (p : ZMod D) * (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff p =
        (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff p) ↔
    ∀ n : ℕ, n.Coprime (N * D) →
      χ (n : ZMod D) * (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n =
        (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n :=
  primitiveCuspForm_selfTwist_iff f χ hq

/-- The actual nonzero primitive Gauss sum gives the exact finite positive-sign Fourier inversion. -/
theorem primitive_gauss_twist_source {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    (∑ a : ZMod D, χ a * ZMod.stdAddChar a) ≠ 0 ∧
    ∀ n : ZMod D, (∑ a : ZMod D, χ a * ZMod.stdAddChar a)⁻¹ *
      (∑ a : ZMod D, χ a * ZMod.stdAddChar (n * a)) = χ n :=
  ⟨primitive_character_gaussSum_ne_zero χ hχ, primitive_quadratic_gauss_inversion χ hχ hq⟩

open scoped MatrixGroups in
/-- A genuine cusp form at level Q gives a normalized genuine quadratic twist at the explicit level D²Q. -/
theorem genuine_quadratic_twist_source {Q D : ℕ} [NeZero Q] [NeZero D] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : (UpperHalfPlane.qExpansion 1 f).coeff 1 = 1)
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃ g : CuspForm ((CongruenceSubgroup.Gamma0 (D * (D * Q))).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k,
      (∀ n, (UpperHalfPlane.qExpansion 1 g).coeff n = χ (n : ZMod D) * (UpperHalfPlane.qExpansion 1 f).coeff n) ∧
      (UpperHalfPlane.qExpansion 1 g).coeff 1 = 1 ∧ g ≠ 0 :=
  ⟨cuspQuadraticTwist k χ hq f, cuspQuadraticTwist_coeff k χ hχ hq f,
    cuspQuadraticTwist_normalized k χ hχ hq f hf, cuspQuadraticTwist_ne_zero k χ hχ hq f hf⟩

open scoped MatrixGroups in
/-- The constructed twist satisfies the literal all-index classical eigenfunction formula and U_p vanishing. -/
theorem quadratic_twist_hecke_source {Q D : ℕ} [NeZero Q] [NeZero D] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    (∀ n, 0 < n → ∀ τ : UpperHalfPlane,
      classicalHeckeFunction (D * (D * Q)) k n (cuspQuadraticTwist k χ hq f.toCuspForm) τ =
        (χ (n : ZMod D) * (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n) *
          cuspQuadraticTwist k χ hq f.toCuspForm τ) ∧
    ∀ p, Nat.Prime p → p ∣ D → ∀ τ : UpperHalfPlane,
      classicalHeckeFunction (D * (D * Q)) k p (cuspQuadraticTwist k χ hq f.toCuspForm) τ = 0 := by
  constructor
  · intro n hn τ
    have he := DFunLike.congr_fun (cuspQuadraticTwist_eigenvector f χ hχ hq hn) τ
    change cuspHecke n (cuspQuadraticTwist k χ hq f.toCuspForm) τ = _ at he
    rwa [cuspHecke_apply] at he
  · intro p hp hpD τ
    have he := DFunLike.congr_fun (cuspQuadraticTwist_bad_prime_zero f.toCuspForm χ hχ hq hp hpD) τ
    change cuspHecke p (cuspQuadraticTwist k χ hq f.toCuspForm) τ = 0 at he
    rwa [cuspHecke_apply] at he


open scoped MatrixGroups ModularForm in
/-- The actual determinant-normalized Fricke matrix has the literal analytic action. -/
theorem fricke_action_source (N : ℕ) [NeZero N] (k : ℤ)
    (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    ((frickeMatrix N • τ : UpperHalfPlane) : ℂ) = -1 / ((N : ℂ) * τ) ∧
    (f ∣[k] frickeMatrix N) τ =
      (N : ℂ)⁻¹ * (τ : ℂ) ^ (-k) * f (frickeMatrix N • τ) :=
  ⟨frickeMatrix_smul N τ, fricke_slash_apply N k f τ⟩

open scoped MatrixGroups in
/-- Actual prime depletion deletes exactly the p-multiple Fourier coefficients and computes its first Fricke coefficient. -/
theorem prime_depletion_source {M p : ℕ} [NeZero M] [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (hpM : p.Coprime M) (eigenvalue : ℂ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 M).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : cuspHeckeLinear M k p f = eigenvalue • f) :
    (∀ n, (UpperHalfPlane.qExpansion 1 (cuspPrimeDepletion (p := p) k eigenvalue f)).coeff n =
      if p ∣ n then 0 else (UpperHalfPlane.qExpansion 1 f).coeff n) ∧
    (UpperHalfPlane.qExpansion 1
      (cuspFricke (p * (p * M)) k (cuspPrimeDepletion (p := p) k eigenvalue f))).coeff 1 =
      (p : ℂ) ^ (k - 3) * (UpperHalfPlane.qExpansion 1 (cuspFricke M k f)).coeff 1 :=
  ⟨cuspPrimeDepletion_coeff hp hpM eigenvalue f hf,
    cuspFricke_primeDepletion_coeff_one hp k eigenvalue f⟩

open scoped MatrixGroups ModularForm in
/-- The constructed level-one twist has the literal Gauss sum and Fricke symmetry on genuine cusp forms. -/
theorem twist_fricke_source {D : ℕ} [NeZero D] {k : ℤ}
    (χ : DirichletCharacter ℂ D) (hq : χ.IsQuadratic)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    (∀ τ : UpperHalfPlane, cuspQuadraticTwist k χ hq f τ =
      (∑ a : ZMod D, χ a * ZMod.stdAddChar a)⁻¹ *
        ∑ a : ZMod D, χ a * f (((a.val : ℝ) / D) +ᵥ τ)) ∧
    ((cuspQuadraticTwist k χ hq f : UpperHalfPlane → ℂ) ∣[k] frickeMatrix (D * (D * 1))) =
      (χ (-1) * (D : ℂ) ^ (k - 2)) • (cuspQuadraticTwist k χ hq f : UpperHalfPlane → ℂ) :=
  ⟨cuspQuadraticTwist_apply χ hq f,
    congrArg DFunLike.coe (cuspQuadraticTwist_fricke χ hq f)⟩

open scoped MatrixGroups in
/-- The finite prime construction produces a real cusp form with exactly the coprime coefficients and computed Fricke coefficient. -/
theorem finite_depletion_source (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {R : ℕ} [NeZero R] (hR : R = ∏ p ∈ S, p) {k : ℤ} (f : PrimitiveCuspForm 1 k) :
    ∃ g : CuspForm ((CongruenceSubgroup.Gamma0 (R * R)).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k,
      (∀ n, (UpperHalfPlane.qExpansion 1 g).coeff n =
        if n.Coprime R then (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n else 0) ∧
      (UpperHalfPlane.qExpansion 1 (cuspFricke (R * R) k g)).coeff 1 = (R : ℂ) ^ (k - 3) := by
  obtain ⟨g, hg, _, hw⟩ := exists_cuspFiniteDepletion S hS hR (L := R * R) rfl f
  exact ⟨g, hg, hw⟩

open scoped MatrixGroups in
/-- A normalized level-one Hecke eigenform yields the actual primitive non-CM object, with the self-twist conclusion unfolded. -/
theorem level_one_nonCM_source {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : (UpperHalfPlane.qExpansion 1 f).coeff 1 = 1)
    (he : ∀ n : ℕ, 0 < n → n.Coprime 1 → ∃ eigenvalue : ℂ,
      ∀ τ : UpperHalfPlane, classicalHeckeFunction 1 k n f τ = eigenvalue * f τ) :
    (∃ g : NonCMPrimitiveCuspForm 1 k, g.toPrimitiveCuspForm.toCuspForm = f) ∧
    ¬ ∃ (D : ℕ+) (χ : DirichletCharacter ℂ D),
      χ.IsPrimitive ∧ χ ≠ 1 ∧ χ.IsQuadratic ∧
      ∀ p : ℕ, Nat.Prime p → p.Coprime (1 * D) →
        χ (p : ZMod D) * (UpperHalfPlane.qExpansion 1 f).coeff p =
          (UpperHalfPlane.qExpansion 1 f).coeff p :=
  ⟨⟨nonCMPrimitiveCuspFormLevelOne f hf he, rfl⟩,
    primitiveCuspForm_levelOne_nonCM (primitiveCuspFormLevelOne f hf he)⟩


/-- Proposition 3.7 retains its printed nonzero, rather than unit, first coefficient. -/
theorem jessen_mass_nonzero_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    jessenMeasure hN ha Set.univ = ENNReal.ofReal (Real.log (lastIndex a N)) ∧
      (ENNReal.ofReal (1 / (2 * Real.pi)) • jessenMeasure hN ha) Set.univ =
        ENNReal.ofReal (Real.log (lastIndex a N) / (2 * Real.pi)) :=
  ⟨jessenMeasure_univ_nonzero hN ha, scaledJessenMeasure_univ_nonzero hN ha⟩

theorem jessen_probability_nonzero_source (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (ha : a 1 ≠ 0) :
    (1 < lastIndex a N → IsProbabilityMeasure
      ((ENNReal.ofReal (Real.log (lastIndex a N)))⁻¹ • jessenMeasure hN ha)) ∧
    (lastIndex a N = 1 → jessenMeasure hN ha = 0) :=
  ⟨normalizedJessenMeasure_isProbability_nonzero hN ha,
    jessenMeasure_zero_of_lastIndex_one_nonzero hN ha⟩

theorem coefficient_scaling_multiplicity_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (c : ℂ) (hc : c ≠ 0) (s : ℂ) (l u T : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, (c * a n) * (n : ℂ) ^ (-s)) =
      c * (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) ∧
    analyticOrderNatAt (fun z : ℂ => ∑ n ∈ Finset.Icc 1 N, (c * a n) * (n : ℂ) ^ (-z)) s =
      analyticOrderNatAt (fun z : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-z)) s ∧
    verticalZeroCount (fun n => c * a n) N hN (mul_ne_zero hc ha) l u T =
      verticalZeroCount a N hN ha l u T :=
  ⟨dirichletSum_scale a N c s, zeroMultiplicity_scale a N hc s,
    verticalZeroCount_scale hN ha hc l u T⟩

theorem jessen_tornehave_nonzero_source (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u : ℝ} (hlu : l < u) :
    Tendsto (fun T : ℝ => ((∑ s ∈ zerosInOpenRectangleFinset a N hN ha l u T,
      analyticOrderNatAt (fun v : ℂ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-v)) s) : ℝ) /
        (2 * T)) atTop (𝓝 ((derivWithin (jessenFunction a N) (Set.Iio u) u -
          derivWithin (jessenFunction a N) (Set.Ioi l) l) / (2 * Real.pi))) := by
  simpa only [verticalZeroCount, zeroMultiplicity, dirichletSum, Nat.cast_sum] using
    tendsto_zeroDensity_one_sided_derivatives_nonzero hN ha hlu

open scoped MatrixGroups in
/-- Actual q-expansion coefficients and the literal horizontal-period integral, with no formal series proxy. -/
theorem cusp_parseval_source {Q : ℕ} {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => ‖(UpperHalfPlane.qExpansion 1 f).coeff n‖ ^ 2 *
      Real.exp (-4 * Real.pi * n * y))
      (∫ x in (0 : ℝ)..1, ‖f ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) :=
  hasSum_cusp_horizontal_energy f hy

open scoped MatrixGroups in
/-- A genuine unconditional upper bound, without asserting a Rankin--Selberg asymptotic. -/
theorem cusp_square_energy_upper_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, ‖(UpperHalfPlane.qExpansion 1 f).coeff n‖ ^ 2) ≤ C * (N : ℝ) ^ k :=
  exists_cusp_coefficient_energy_upper f

open scoped MatrixGroups in
/-- The true square-coefficient Dirichlet series is absolutely convergent to the right of the weight. -/
theorem cusp_square_dirichlet_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 ≤ k) {s : ℝ} (hs : (k : ℝ) < s) :
    Summable (fun n : ℕ => ‖(UpperHalfPlane.qExpansion 1 f).coeff n‖ ^ 2 * (n : ℝ) ^ (-s)) :=
  summable_cusp_square_dirichlet f hk hs

open scoped MatrixGroups in
/-- The Mellin integral converges and equals the true square series with the exact Gamma factor. -/
theorem cusp_mellin_energy_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 ≤ k) {s : ℝ} (hs : (k : ℝ) < s) :
    IntegrableOn (fun y : ℝ => y ^ (s - 1) *
      (∫ x in (0 : ℝ)..1, ‖f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2))
      (Set.Ioi 0) ∧
    (∫ y : ℝ in Set.Ioi 0, y ^ (s - 1) *
      (∫ x in (0 : ℝ)..1, ‖f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2)) =
      ((4 * Real.pi) ^ (-s) * Real.Gamma s) *
        ∑' n : ℕ, ‖(UpperHalfPlane.qExpansion 1 f).coeff n‖ ^ 2 * (n : ℝ) ^ (-s) :=
  ⟨integrableOn_cusp_mellin_energy f hk hs, cusp_mellin_energy_identity f hk hs⟩

open scoped MatrixGroups in
/-- The complex Mellin formula consumes the literal horizontal integral and actual Fourier coefficients. -/
theorem cusp_complex_mellin_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 ≤ k) {s : ℂ} (hs : (k : ℝ) < s.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1) *
      ((∫ x in (0 : ℝ)..1, ‖f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2 : ℝ) : ℂ))
      (Set.Ioi 0) ∧
    (∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (s - 1) *
      ((∫ x in (0 : ℝ)..1, ‖f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2 : ℝ) : ℂ)) =
      ((4 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s) *
        ∑' n : ℕ, ((‖(UpperHalfPlane.qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s) :=
  ⟨integrableOn_cusp_complex_mellin_energy f hk hs, cusp_complex_mellin_energy_identity f hk hs⟩

open scoped MatrixGroups in
/-- Actual automorphically normalized coefficients give a holomorphic Rankin series and its convergent Mellin identity. -/
theorem cusp_rankin_series_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    AnalyticOnNhd ℂ (fun t : ℂ =>
      ∑' n : ℕ, ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-t))
      {t : ℂ | 1 < t.re} ∧
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s + (k : ℂ) - 2) *
      ((∫ x in (0 : ℝ)..1, ‖f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2 : ℝ) : ℂ))
      (Set.Ioi 0) ∧
    (∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (s + (k : ℂ) - 2) *
      ((∫ x in (0 : ℝ)..1, ‖f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2 : ℝ) : ℂ)) =
      ((4 * Real.pi : ℂ) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1)) *
        ∑' n : ℕ, ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
  have he : cuspRankinSeries f = (fun t : ℂ =>
      ∑' n : ℕ, ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-t)) :=
    funext (cuspRankinSeries_eq_tsum f)
  simpa only [he, cuspHorizontalEnergy] using
    And.intro (cuspRankinSeries_analyticOnNhd f hk)
      (And.intro (integrableOn_cuspRankin_mellin f hk hs) (cuspRankinSeries_mellin f hk hs))

open scoped MatrixGroups in
/-- The literal primitive-row Eisenstein series has absolute convergence, actual Γ₀ invariance and parameter holomorphy. -/
theorem gamma0_eisenstein_source (Q : ℕ) (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : {v : Fin 2 → ℤ | (v 0).gcd (v 1) = 1 ∧ (Q : ℤ) ∣ v 0} =>
      ‖((z.im / ‖(v.val 0 : ℂ) * z + v.val 1‖ ^ 2 : ℝ) : ℂ) ^ s‖) ∧
    (∀ A : SL(2, ℤ), A ∈ CongruenceSubgroup.Gamma0 Q →
      gamma0Eisenstein Q s (A • z) = gamma0Eisenstein Q s z) ∧
    AnalyticOnNhd ℂ (fun t : ℂ => (1 / 2 : ℂ) *
      ∑' v : {v : Fin 2 → ℤ | (v 0).gcd (v 1) = 1 ∧ (Q : ℤ) ∣ v 0},
        ((z.im / ‖(v.val 0 : ℂ) * z + v.val 1‖ ^ 2 : ℝ) : ℂ) ^ t)
      {t : ℂ | 1 < t.re} :=
  ⟨gamma0Eisenstein_summable_norm Q hs z,
    fun A hA => gamma0Eisenstein_invariant Q s z A hA, gamma0Eisenstein_analyticOnNhd Q z⟩

open scoped MatrixGroups in
/-- The literal half-open unit strip is the true projective translation fundamental domain. -/
theorem gamma0_translation_strip_source (Q : ℕ) :
    IsFundamentalDomain (gamma0ProjectiveTranslations Q)
      {z : UpperHalfPlane | 0 ≤ z.re ∧ z.re < 1} (volume : Measure UpperHalfPlane) :=
  isFundamentalDomain_gamma0Translations Q

/-- The two primitive row signs give exactly twice the literal projective-coset sum. -/
theorem eisenstein_row_coset_source (Q : ℕ) (σ : ℝ) (z : UpperHalfPlane) :
    (∑' v : {v : Fin 2 → ℤ | (v 0).gcd (v 1) = 1 ∧ (Q : ℤ) ∣ v 0},
      ENNReal.ofReal ((z.im / ‖(v.val 0 : ℂ) * z + v.val 1‖ ^ 2) ^ σ)) =
      2 * ∑' q : (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q,
        ENNReal.ofReal ((q.out⁻¹ • z).im ^ σ) :=
  eisenstein_primitive_row_sum_eq_two_coset Q σ z

open scoped MatrixGroups in
/-- The true primitive-row Eisenstein series unfolds against the actual squared cusp norm. -/
theorem eisenstein_petersson_unfold_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    {σ : ℝ} (hσ : 1 < σ) :
    (∫⁻ z in gamma0FundamentalDomain Q,
      ENNReal.ofReal (gamma0Eisenstein Q (σ : ℂ) z).re *
        ENNReal.ofReal (‖f z‖ ^ 2 * z.im ^ k)) =
      ∫⁻ z in {z : UpperHalfPlane | 0 ≤ z.re ∧ z.re < 1},
        ENNReal.ofReal (z.im ^ σ) * ENNReal.ofReal (‖f z‖ ^ 2 * z.im ^ k) := by
  simpa only [norm_petersson_self] using gamma0_eisenstein_petersson_unfold f hσ

open scoped MatrixGroups in
/-- Actual modular coefficients and the literal squared cusp norm satisfy the convergent Rankin unfolding formula. -/
theorem rankin_unfolding_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 ≤ k) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun z : UpperHalfPlane =>
      (gamma0Eisenstein Q (σ : ℂ) z).re * (‖f z‖ ^ 2 * z.im ^ k)) (gamma0FundamentalDomain Q) ∧
    (∫ z in gamma0FundamentalDomain Q,
      (gamma0Eisenstein Q (σ : ℂ) z).re * (‖f z‖ ^ 2 * z.im ^ k)) =
      ((4 * Real.pi) ^ (-(σ + (k : ℝ) - 1)) * Real.Gamma (σ + (k : ℝ) - 1)) *
        ∑' n : ℕ, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-σ) := by
  simpa only [norm_petersson_self] using
    And.intro (integrableOn_gamma0_eisenstein_petersson f hk hσ)
      (cusp_rankin_unfolding_integral f hk hσ)

/-- The literal determinant-one lattice Gaussian has the exact reciprocal-parameter transformation. -/
theorem lattice_theta_source (z : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    (∑' v : ℤ × ℤ, Real.exp (-Real.pi * t * (‖(v.1 : ℂ) * z + v.2‖ ^ 2 / z.im))) =
      t⁻¹ * ∑' v : ℤ × ℤ,
        Real.exp (-Real.pi * t⁻¹ * (‖(v.1 : ℂ) * z + v.2‖ ^ 2 / z.im)) := by
  simpa only [latticeTheta, latticeThetaTerm, latticeQuadratic_eq_norm] using latticeTheta_reciprocal z ht

/-- The literal upper-tail integral of nonzero Gaussian rows is entire. -/
theorem lattice_theta_tail_source (z : UpperHalfPlane) :
    Differentiable ℂ (fun s : ℂ => ∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (s - 1) *
      ((∑' v : {v : ℤ × ℤ // v ≠ 0},
        Real.exp (-Real.pi * t * (‖(v.val.1 : ℂ) * z + v.val.2‖ ^ 2 / z.im)) : ℝ) : ℂ)) := by
  have he : latticeThetaMellinTail z = (fun s : ℂ => ∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (s - 1) *
      ((∑' v : {v : ℤ × ℤ // v ≠ 0},
        Real.exp (-Real.pi * t * (‖(v.val.1 : ℂ) * z + v.val.2‖ ^ 2 / z.im)) : ℝ) : ℂ)) := by
    funext s
    simp only [latticeThetaMellinTail, latticeThetaMellinKernel, latticeThetaRemainder,
      latticeThetaTerm, latticeQuadratic_eq_norm]
  rw [← he]
  exact differentiable_latticeThetaMellinTail z

/-- The continuation equals the literal completed Epstein half-sum and has the genuine functional equation. -/
theorem lattice_epstein_continuation_source (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    latticeCompletedMellin z s = ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s) *
      ((∑' v : {v : ℤ × ℤ // v ≠ 0},
        1 / ((‖(v.val.1 : ℂ) * z + v.val.2‖ ^ 2 / z.im : ℝ) : ℂ) ^ s) / 2) ∧
    (∀ w : ℂ, w ≠ 0 → w ≠ 1 → DifferentiableAt ℂ (latticeCompletedMellin z) w) ∧
    (∀ w : ℂ, latticeCompletedMellin z (1 - w) = latticeCompletedMellin z w) := by
  refine ⟨?_, fun _ h0 h1 => differentiableAt_latticeCompletedMellin z h0 h1,
    latticeCompletedMellin_functional_equation z⟩
  simpa only [latticeEpsteinSeries, latticeQuadratic_eq_norm] using latticeCompletedMellin_eq_epstein z hs

/-- The actual half-lattice completion has the exact nonzero pole residues. -/
theorem lattice_epstein_residue_source (z : UpperHalfPlane) :
    Tendsto (fun s : ℂ => (s - 1) * latticeCompletedMellin z s) (𝓝[≠] 1) (𝓝 (1 / 2 : ℂ)) ∧
    Tendsto (fun s : ℂ => s * latticeCompletedMellin z s) (𝓝[≠] 0) (𝓝 (-1 / 2 : ℂ)) :=
  ⟨latticeCompletedMellin_residue_one z, latticeCompletedMellin_residue_zero z⟩

/-- The literal Epstein lattice half-sum has the exact zeta factor multiplying primitive rows. -/
theorem primitive_lattice_zeta_source (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    (∑' v : {v : ℤ × ℤ // v ≠ 0},
      1 / ((‖(v.val.1 : ℂ) * z + v.val.2‖ ^ 2 / z.im : ℝ) : ℂ) ^ s) / 2 =
      riemannZeta (2 * s) * ((1 / 2 : ℂ) *
        ∑' v : {v : Fin 2 → ℤ | (v 0).gcd (v 1) = 1 ∧ (1 : ℤ) ∣ v 0},
          ((z.im / ‖(v.val 0 : ℂ) * z + v.val 1‖ ^ 2 : ℝ) : ℂ) ^ s) := by
  simpa only [latticeEpsteinSeries, latticeQuadratic_eq_norm, gamma0Eisenstein,
    nonholomorphicEisensteinTerm, eisensteinRowHeight] using
      latticeEpsteinSeries_eq_zeta_eisenstein z hs

/-- The full-level continuation agrees with the literal primitive-row series and has residue 3/pi. -/
theorem level_one_eisenstein_continuation_source (z : UpperHalfPlane) :
    (∀ s : ℂ, 1 < s.re → levelOneEisensteinContinuation z s =
      (1 / 2 : ℂ) * ∑' v : {v : Fin 2 → ℤ | (v 0).gcd (v 1) = 1 ∧ (1 : ℤ) ∣ v 0},
        ((z.im / ‖(v.val 0 : ℂ) * z + v.val 1‖ ^ 2 : ℝ) : ℂ) ^ s) ∧
      Tendsto (fun s : ℂ => (s - 1) * levelOneEisensteinContinuation z s)
        (𝓝[≠] 1) (𝓝 (3 / (Real.pi : ℂ))) :=
  ⟨fun _ hs => levelOneEisensteinContinuation_eq z hs,
    levelOneEisensteinContinuation_residue_one z⟩

/-- At every positive level, the continuation matches the actual primitive rows and is holomorphic in the stated strip. -/
theorem gamma0_eisenstein_continuation_source (Q : ℕ) [NeZero Q] (z : UpperHalfPlane) :
    (∀ s : ℂ, 1 < s.re → gamma0EisensteinContinuation Q z s =
      (1 / 2 : ℂ) * ∑' v : {v : Fin 2 → ℤ | (v 0).gcd (v 1) = 1 ∧ (Q : ℤ) ∣ v 0},
        ((z.im / ‖(v.val 0 : ℂ) * z + v.val 1‖ ^ 2 : ℝ) : ℂ) ^ s) ∧
      ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
        DifferentiableAt ℂ (gamma0EisensteinContinuation Q z) s :=
  ⟨fun _ hs => gamma0EisensteinContinuation_eq Q z hs,
    fun _ hs hs1 => differentiableAt_gamma0EisensteinContinuation Q z hs hs1⟩

/-- The actual general-level residue is the literal positive arithmetic constant, independent of the point. -/
theorem gamma0_eisenstein_residue_source (Q : ℕ) [NeZero Q] (z : UpperHalfPlane) :
    0 < Real.pi * Q.totient /
      (2 * (Q : ℝ) ^ 2 * (DirichletCharacter.LFunctionTrivChar Q 2).re) ∧
    Tendsto (fun s : ℂ => (s - 1) * gamma0EisensteinContinuation Q z s) (𝓝[≠] 1)
      (𝓝 ((Real.pi : ℂ) * Q.totient /
        (2 * (Q : ℂ) ^ 2 * DirichletCharacter.LFunctionTrivChar Q 2))) :=
  ⟨gamma0EisensteinResidue_pos Q, gamma0EisensteinContinuation_residue_one Q z⟩

/-- The literal entire Mellin tail has a uniform complex-parameter bound by a convergent positive lattice value. -/
theorem lattice_mellin_majorant_source (z : UpperHalfPlane) {s : ℂ} {σ : ℝ}
    (hσ : 1 < σ) (hs : s.re ≤ σ) :
    ‖∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (s - 1) *
      ((∑' v : {v : ℤ × ℤ // v ≠ 0},
        Real.exp (-Real.pi * t * (‖(v.val.1 : ℂ) * z + v.val.2‖ ^ 2 / z.im)) : ℝ) : ℂ)‖ ≤
      2 * (latticeCompletedMellin z (σ : ℂ)).re := by
  simpa only [latticeThetaMellinTail, latticeThetaMellinKernel, latticeThetaRemainder,
    latticeThetaTerm, latticeQuadratic_eq_norm] using norm_latticeThetaMellinTail_le_completed z hσ hs

open scoped MatrixGroups in
/-- Every actual rescaled continued lattice kernel is integrable against the literal cusp density. -/
theorem lattice_cusp_integrability_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    IntegrableOn (fun z : UpperHalfPlane =>
      latticeCompletedMellin (rectangularLatticePoint a b ha hb z) s *
        (starRingEnd ℂ (f z) * f z * (z.im : ℂ) ^ k)) (gamma0FundamentalDomain Q) :=
  integrableOn_rectangular_lattice_completed_petersson f a b ha hb s

open scoped MatrixGroups in
/-- The true regularized integral is entire in its spectral parameter, with domination and differentiation proved. -/
theorem lattice_cusp_entire_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Differentiable ℂ (fun s : ℂ => ∫ z : UpperHalfPlane in gamma0FundamentalDomain Q,
      latticeCompletedMellinRegular (rectangularLatticePoint a b ha hb z) s *
        (starRingEnd ℂ (f z) * f z * (z.im : ℂ) ^ k)) :=
  differentiable_rectangularLatticeCuspRegular f a b ha hb

open scoped MatrixGroups in
/-- The actual integrated lattice residue is one half the literal cusp Petersson integral. -/
theorem lattice_cusp_residue_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun s : ℂ => (s - 1) * ∫ z : UpperHalfPlane in gamma0FundamentalDomain Q,
      latticeCompletedMellin (rectangularLatticePoint a b ha hb z) s *
        (starRingEnd ℂ (f z) * f z * (z.im : ℂ) ^ k)) (𝓝[≠] 1)
      (𝓝 ((∫ z : UpperHalfPlane in gamma0FundamentalDomain Q,
        starRingEnd ℂ (f z) * f z * (z.im : ℂ) ^ k) / 2)) := by
  have h := rectangularLatticeCuspCompleted_residue_one f a b ha hb
  rw [cuspPetersson_eq_gamma0Domain_integral Q] at h
  exact h

open scoped MatrixGroups in
/-- The continued primitive Eisenstein integral has the actual Petersson residue, with integrability proved upstream. -/
theorem gamma0_cusp_integral_residue_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    Tendsto (fun s : ℂ => (s - 1) * ∫ z : UpperHalfPlane in gamma0FundamentalDomain Q,
      gamma0EisensteinContinuation Q z s * (starRingEnd ℂ (f z) * f z * (z.im : ℂ) ^ k))
      (𝓝[≠] 1) (𝓝 ((gamma0EisensteinResidue Q : ℂ) *
        ∫ z : UpperHalfPlane in gamma0FundamentalDomain Q,
          starRingEnd ℂ (f z) * f z * (z.im : ℂ) ^ k)) := by
  have h := gamma0CuspEisensteinContinuation_residue_one f
  rw [cuspPetersson_eq_gamma0Domain_integral Q] at h
  exact h

open scoped MatrixGroups in
/-- The literal complex primitive-row integral equals the exact Gamma factor times the actual coefficient square series. -/
theorem rankin_complex_unfolding_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    (∫ z : UpperHalfPlane in gamma0FundamentalDomain Q,
      ((1 / 2 : ℂ) * ∑' v : {v : Fin 2 → ℤ | (v 0).gcd (v 1) = 1 ∧ (Q : ℤ) ∣ v 0},
        ((z.im / ‖(v.val 0 : ℂ) * z + v.val 1‖ ^ 2 : ℝ) : ℂ) ^ s) *
          (starRingEnd ℂ (f z) * f z * (z.im : ℂ) ^ k)) =
      ((4 * Real.pi : ℂ) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1)) *
        ∑' n : ℕ, ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
  have h := gamma0CuspEisensteinContinuation_eq_rankin f hk hs
  rw [gamma0CuspEisensteinContinuation_eq_integral f hs, cuspRankinSeries_eq_tsum] at h
  exact h

open scoped MatrixGroups in
/-- The constructed Rankin continuation agrees with the actual square series and is holomorphic across the stated strip. -/
theorem rankin_continuation_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) :
    (∀ s : ℂ, 1 < s.re → cuspRankinContinuation f s =
      ∑' n : ℕ, ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s)) ∧
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → DifferentiableAt ℂ (cuspRankinContinuation f) s := by
  constructor
  · intro s hs
    rw [cuspRankinContinuation_eq_series f hk.le hs, cuspRankinSeries_eq_tsum]
  · exact fun _ hs hs1 => differentiableAt_cuspRankinContinuation f hk hs hs1

open scoped MatrixGroups in
/-- For every nonzero positive-weight cusp form the actual Rankin residue is a proved positive Petersson constant. -/
theorem rankin_positive_residue_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) (hf : f ≠ 0) :
    0 < cuspRankinResidue f ∧
    cuspRankinResidue f =
      gamma0EisensteinResidue Q *
        (∫ z : UpperHalfPlane in gamma0FundamentalDomain Q,
          starRingEnd ℂ (f z) * f z * (z.im : ℂ) ^ k).re /
            ((4 * Real.pi) ^ (-(k : ℝ)) * Real.Gamma (k : ℝ)) ∧
    Tendsto (fun s : ℂ => (s - 1) * cuspRankinContinuation f s) (𝓝[≠] 1)
      (𝓝 (cuspRankinResidue f : ℂ)) := by
  refine ⟨cuspRankinResidue_pos f hk hf, ?_, cuspRankinContinuation_residue_real f hk⟩
  rw [cuspRankinResidue, cuspPetersson_eq_gamma0Domain_integral Q,
    cuspRankinFactor_one, Complex.ofReal_re]
  rfl

open scoped MatrixGroups in
/-- Every literal rescaled lattice-cusp integral obeys the exact spectral reflection. -/
theorem lattice_cusp_functional_equation_source {Q : ℕ} {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    (∫ z : UpperHalfPlane in gamma0FundamentalDomain Q,
      latticeCompletedMellin (rectangularLatticePoint a b ha hb z) (1 - s) *
        (starRingEnd ℂ (f z) * f z * (z.im : ℂ) ^ k)) =
    ∫ z : UpperHalfPlane in gamma0FundamentalDomain Q,
      latticeCompletedMellin (rectangularLatticePoint a b ha hb z) s *
        (starRingEnd ℂ (f z) * f z * (z.im : ℂ) ^ k) :=
  rectangularLatticeCuspCompleted_functional_equation f a b ha hb s

open scoped MatrixGroups in
/-- The genuine convolution has nonnegative real coefficients and the exact square-supported principal-character product. -/
theorem rankin_convolution_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    (∀ n : ℕ, 0 ≤ (rankinConvolutionCoefficients f n).re ∧
      (rankinConvolutionCoefficients f n).im = 0) ∧
    (∀ n : ℕ, principalSquareCoefficients Q (n ^ 2) = if Nat.Coprime n Q then 1 else 0) ∧
    LSeries (rankinConvolutionCoefficients f) s = DirichletCharacter.LFunctionTrivChar Q (2 * s) *
      ∑' n : ℕ, ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
  refine ⟨fun n => ⟨rankinConvolutionCoefficients_re_nonneg f n,
    rankinConvolutionCoefficients_im f n⟩, principalSquareCoefficients_sq Q, ?_⟩
  rw [rankinConvolution_LSeries f hk hs, cuspRankinSeries_eq_tsum]

open scoped MatrixGroups in
/-- The entire finite lattice completion consumes the true convolution series with both exact Gamma factors. -/
theorem completed_rankin_convolution_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Differentiable ℂ (gamma0CuspEntire f) ∧
    gamma0CuspEntire f s = s * (s - 1) *
      (((Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        ((4 * Real.pi : ℂ) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1))) *
          LSeries (rankinConvolutionCoefficients f) s) := by
  refine ⟨differentiable_gamma0CuspEntire f, ?_⟩
  rw [gamma0CuspEntire_eq_convolution f hk hs, cuspRankinFactor]

open scoped MatrixGroups in
/-- The actual entire general-level Rankin completion has a proved polynomial bound on each closed vertical strip. -/
theorem completed_rankin_strip_growth_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ≤ σ → 1 - s.re ≤ σ →
      ‖gamma0CuspEntire f s‖ ≤ C * (1 + ‖s‖) ^ 2 :=
  exists_gamma0CuspEntire_strip_bound f hσ

open scoped MatrixGroups in
/-- At full level the genuine completed convolution integral has a scalar reflection equation. -/
theorem level_one_completed_rankin_functional_equation_source {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (s : ℂ) : gamma0CompletedCusp f (1 - s) = gamma0CompletedCusp f s :=
  gamma0CompletedCusp_levelOne_functional_equation f s


open scoped MatrixGroups in
/-- The removed-pole function is analytic on the actual half-plane and matches the literal coefficient sum. -/
theorem rankin_regular_boundary_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) :
    DifferentiableOn ℂ (cuspRankinRegular f) {s : ℂ | 1 / 2 < s.re} ∧
    ContinuousOn (cuspRankinRegular f) {s : ℂ | 1 ≤ s.re} ∧
    ∀ s : ℂ, 1 < s.re → cuspRankinRegular f s =
      (∑' n : ℕ, ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s)) -
        (cuspRankinResidue f : ℂ) / (s - 1) := by
  refine ⟨differentiableOn_cuspRankinRegular f hk, continuousOn_cuspRankinRegular f hk, ?_⟩
  intro s hs
  rw [cuspRankinRegular_eq_series_sub_pole f hk hs, cuspRankinSeries_eq_tsum]

open scoped MatrixGroups in
/-- The genuine normalization and actual Parseval bound yield a uniform linear square sum. -/
theorem normalized_cusp_linear_energy_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N, ‖cuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (1 - (k : ℝ))) ≤ C * N := by
  simpa only [norm_sq_normalizedCuspCoefficients] using exists_normalized_cusp_square_upper f hk

open scoped MatrixGroups in
/-- The actual positive Rankin mean is proved at natural and real cutoffs with an o(x) remainder. -/
theorem rankin_mean_square_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) (hf : f ≠ 0) :
    0 < cuspRankinResidue f ∧
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2) / N)
      atTop (𝓝 (cuspRankinResidue f)) ∧
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖normalizedCuspCoefficients f n‖ ^ 2) / x)
      atTop (𝓝 (cuspRankinResidue f)) ∧
    (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖normalizedCuspCoefficients f n‖ ^ 2) - cuspRankinResidue f * x)
      =o[atTop] (fun x : ℝ => x) :=
  ⟨cuspRankinResidue_pos f hk hf, tendsto_cusp_square_mean f hk,
    tendsto_cusp_squareSummatory_div f hk, cusp_squareSummatory_sub_main_isLittleO f hk⟩

open UpperHalfPlane ModularForm CongruenceSubgroup in
open scoped MatrixGroups CongruenceSubgroup in
/-- The complete primitive-form concentration consumer has only the actual Sato–Tate input left explicit. -/
theorem primitive_concentration_with_proved_mean_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k)
    (hST : Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability)) :
    TendstoLocallyUniformly (normalizedJessen (normalizedCuspCoefficients f.toCuspForm))
      (fun σ => max (1 / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (normalizedCuspCoefficients_one f.toCuspForm f.normalized)) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    TendstoLocallyUniformly (normalizedJessen (cuspCoefficients f.toCuspForm))
      (fun σ => max ((k : ℝ) / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (a := cuspCoefficients f.toCuspForm) f.normalized) atTop
      (𝓝 (⟨Measure.dirac ((k : ℝ) / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex (cuspCoefficients f.toCuspForm) N ∧ ∀ l u : ℝ,
      Tendsto (fun T : ℝ => (2 * Real.pi / Real.log (lastIndex (cuspCoefficients f.toCuspForm) N)) *
        ((verticalZeroCount (cuspCoefficients f.toCuspForm) N hN (f.normalized.trans_ne one_ne_zero) l u T : ℝ) /
          (2 * T))) atTop
        (𝓝 (((jessenProbability (a := cuspCoefficients f.toCuspForm) f.normalized N : Measure ℝ) (Set.Ioo l u)).toReal))) :=
  primitive_concentration_of_sato_tate f hk hST


open scoped MatrixGroups in
/-- The actual normalized cusp squares are recovered from the genuine completed convolution by the square-supported Möbius inverse. -/
theorem rankin_moebius_inversion_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 ≤ k) :
    (∀ n : ℕ, moebiusSquareCoefficients Q (n ^ 2) =
      if Nat.Coprime n Q then (ArithmeticFunction.moebius n : ℂ) else 0) ∧
    ∀ n : ℕ, ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) =
      ∑ uv ∈ n.divisorsAntidiagonal, moebiusSquareCoefficients Q uv.1 *
        rankinConvolutionCoefficients f uv.2 :=
  ⟨moebiusSquareCoefficients_sq Q, normalized_cusp_square_eq_moebius_convolution f hk⟩

open scoped MatrixGroups in
/-- Both noncentral regimes of the literal weighted cusp energy are proved using the positive actual Rankin mean. -/
theorem cusp_noncentral_weighted_energy_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) (hf : f ≠ 0) :
    0 < cuspRankinResidue f ∧
    (∀ σ : ℝ, σ < 1 / 2 → Tendsto (fun N : ℕ =>
      ((∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) -
        cuspRankinResidue f * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ)) /
          (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0)) ∧
    (∀ σ : ℝ, 1 / 2 < σ → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      0 ≤ (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) ∧
      (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) ≤ B) :=
  ⟨cuspRankinResidue_pos f hk hf, fun _ hσ => cusp_weighted_energy_left f hk hσ,
    fun _ hσ => cusp_weighted_energy_right f hk hσ⟩

/-- The auxiliary analytic Tauberian theorem consumes the literal Laplace integral, not an assumed convergence conclusion. -/
theorem analytic_tauberian_actual_integral_source {f : ℝ → ℂ} {G : ℂ → ℂ} {B d : ℝ}
    (hfm : AEStronglyMeasurable f volume) (hf : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (hd : 0 < d) (hG : DifferentiableOn ℂ G {z : ℂ | -d ≤ z.re})
    (heq : ∀ z : ℂ, 0 < z.re → G z =
      ∫ t : ℝ in Set.Ioi 0, f t * Complex.exp (-z * t)) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t) atTop (𝓝 (G 0)) :=
  newman_tauberian_integral hfm hf hd hG heq

open scoped MatrixGroups in
/-- The literal central cusp weighted sum has a convergent error with the exact Rankin regular-part constant. -/
theorem cusp_central_weighted_energy_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 / (n : ℝ)) -
      cuspRankinResidue f * Real.log N) atTop (𝓝 ((cuspRankinRegular f 1).re)) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      |(∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 / (n : ℝ)) -
        cuspRankinResidue f * Real.log N| ≤ B := by
  have hh := And.intro (tendsto_cusp_weighted_energy_center_error f hk) (cusp_weighted_energy_center f hk)
  norm_num only [coefficientEnergy] at hh
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hh

open scoped MatrixGroups in
/-- Every regime of the source's literal weighted cusp energy is now proved, with its positive actual Petersson residue. -/
theorem cusp_all_weighted_energy_regimes_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) (hf : f ≠ 0) :
    0 < cuspRankinResidue f ∧
    (∀ σ : ℝ, σ < 1 / 2 → Tendsto (fun N : ℕ =>
      ((∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) -
        cuspRankinResidue f * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ)) /
          (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0)) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      |(∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 / (n : ℝ)) -
        cuspRankinResidue f * Real.log N| ≤ B) ∧
    (∀ σ : ℝ, 1 / 2 < σ → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      0 ≤ (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) ∧
      (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) ≤ B) :=
  ⟨cuspRankinResidue_pos f hk hf, fun _ hσ => cusp_weighted_energy_left f hk hσ,
    (cusp_central_weighted_energy_source f hk).2, fun _ hσ => cusp_weighted_energy_right f hk hσ⟩

open scoped MatrixGroups in
/-- The genuine Rankin convolution has its exact hyperbola sum and a proved positive leading mean. -/
theorem rankin_convolution_mean_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) (hf : f ≠ 0) :
    0 < rankinConvolutionResidue f ∧
    (∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, (rankinConvolutionCoefficients f n).re) =
      ∑ d ∈ Finset.Icc 1 N, (principalSquareCoefficients Q d).re *
        ∑ n ∈ Finset.Icc 1 (N / d), ‖normalizedCuspCoefficients f n‖ ^ 2) ∧
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (rankinConvolutionCoefficients f n).re) / N)
      atTop (𝓝 (principalSquareMass Q * cuspRankinResidue f)) ∧
    (principalSquareMass Q : ℂ) = DirichletCharacter.LFunctionTrivChar Q 2 :=
  ⟨rankinConvolutionResidue_pos f hk hf, rankinConvolution_summatory_eq f,
    tendsto_rankin_convolution_mean f hk, principalSquareMass_eq_LFunction Q⟩

open scoped MatrixGroups in
/-- The actual counting error is controlled by literal finite quadratic Riesz sums, with no sharp error estimate assumed. -/
theorem rankin_convolution_riesz_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (x : ℝ) {h : ℝ} (hh : 0 < h) :
    let R : ℝ → ℝ := fun t =>
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (rankinConvolutionCoefficients f n).re * (t - n) ^ 2 / 2) -
        rankinConvolutionResidue f * t ^ 3 / 6
    |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re) - rankinConvolutionResidue f * x| ≤
      rankinConvolutionResidue f * h +
      max |R (x + 2 * h) - 2 * R (x + h) + R x|
        |R x - 2 * R (x - h) + R (x - 2 * h)| / h ^ 2 := by
  dsimp only
  have hb := rankinConvolution_error_le_riesz f x hh
  have he : x - 2 * h + h = x - h := by ring
  simpa only [rankinConvolutionRieszError, rieszSecondError, rieszSecondDifference,
    rieszSecondSum_eq, sub_add_cancel, he] using hb

/-- The actual digamma derivative has a proved reciprocal asymptotic with explicit uniform error. -/
theorem trigamma_reciprocal_asymptotic_source {z : ℂ} (hz : 0 < z.re) (hy : 1 ≤ |z.im|) :
    ‖deriv Complex.digamma z - z⁻¹‖ ≤ 32 / |z.im| ^ 2 :=
  norm_deriv_digamma_sub_inv_le hz hy

/-- The literal reflected two-Gamma quotient has a proved phase equation, logarithmic frequency and reciprocal curvature. -/
theorem rankin_gamma_phase_source {k : ℤ} (hk : 0 < k) {t : ℝ}
    (ht : 128 ≤ t) (hkt : (k : ℝ) - 1 / 2 ≤ t) :
    ‖Complex.Gamma ((1 / 2 : ℂ) - (t : ℂ) * Complex.I) *
        Complex.Gamma (((k : ℝ) - 1 / 2 : ℝ) - (t : ℂ) * Complex.I) /
      (Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
        Complex.Gamma (((k : ℝ) - 1 / 2 : ℝ) + (t : ℂ) * Complex.I))‖ = 1 ∧
    HasDerivAt (rankinGammaPhase k)
      (Complex.I * (rankinGammaFrequency k t : ℂ) * rankinGammaPhase k t) t ∧
    |rankinGammaFrequency k t + 4 * Real.log t| ≤ (16 + 2 * (k : ℝ)) / t ∧
    -8 / t ≤ deriv (rankinGammaFrequency k) t ∧ deriv (rankinGammaFrequency k) t ≤ -1 / t := by
  refine ⟨?_, hasDerivAt_rankinGammaPhase hk t, ?_, rankinGammaFrequency_deriv_bounds hk ht hkt⟩
  · rw [← rankinGammaPhase_eq]
    exact norm_rankinGammaPhase hk t
  · simpa only [abs_of_nonneg (by linarith : 0 ≤ t)] using
      abs_rankinGammaFrequency_add_log_le hk (by rw [abs_of_nonneg (by linarith : 0 ≤ t)]; linarith : 1 ≤ |t|)


/-- The literal quadratic cutoff has its exact Mellin symbol and an absolutely convergent inverse on every positive line. -/
theorem riesz_quadratic_mellin_source {σ : ℝ} (hσ : 0 < σ) :
    (∀ s : ℂ, 0 < s.re → HasMellin
      (Set.indicator (Set.Ioc (0 : ℝ) 1) (fun x => (1 - (x : ℂ)) ^ 2 / 2))
      s (1 / (s * (s + 1) * (s + 2)))) ∧
    Complex.VerticalIntegrable (fun s : ℂ => 1 / (s * (s + 1) * (s + 2))) σ ∧
    (∀ x : ℝ, 0 < x → mellinInv σ (fun s : ℂ => 1 / (s * (s + 1) * (s + 2))) x =
      ((max (1 - x) 0 ^ 2 / 2 : ℝ) : ℂ)) := by
  refine ⟨fun s hs => hasMellin_rieszMellinCutoff hs, verticalIntegrable_rieszMellinSymbol hσ, ?_⟩
  intro x hx
  exact (mellinInv_rieszMellinSymbol hσ hx).trans (rieszMellinCutoff_eq hx)

open scoped MatrixGroups in
/-- The actual Rankin quadratic sum has its absolutely convergent literal Perron integral, with all coefficient convergence proved. -/
theorem rankin_convolution_perron_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 ≤ k) {σ x : ℝ} (hσ : 1 < σ) (hx : 0 < x) :
    MeasureTheory.Integrable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + t * Complex.I + 2) *
        LSeries (rankinConvolutionCoefficients f) (σ + t * Complex.I) /
        (((σ : ℂ) + t * Complex.I) * ((σ : ℂ) + t * Complex.I + 1) *
          ((σ : ℂ) + t * Complex.I + 2))) ∧
    ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re * (x - n) ^ 2 / 2 : ℝ) : ℂ) =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + t * Complex.I + 2) *
          LSeries (rankinConvolutionCoefficients f) (σ + t * Complex.I) /
          (((σ : ℂ) + t * Complex.I) * ((σ : ℂ) + t * Complex.I + 1) *
            ((σ : ℂ) + t * Complex.I + 2)) := by
  refine ⟨integrable_rankinConvolutionPerron f hk hσ hx, ?_⟩
  simpa only [rankinConvolutionRiesz_eq] using rankinConvolutionRiesz_eq_integral f hk hσ hx


/-- The literal critical-line reflected two-Gamma quotient has uniform dyadic cancellation for every Mellin frequency. -/
theorem rankin_gamma_oscillation_source {k : ℤ} (hk : 0 < k)
    {T a b : ℝ} (hT : 128 ≤ T) (hkT : (k : ℝ) - 1 / 2 ≤ T)
    (ha : T ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * T) (v : ℝ) :
    ‖∫ t in a..b, Complex.exp (Complex.I * ((v * t : ℝ) : ℂ)) *
      (Complex.Gamma ((1 / 2 : ℂ) - (t : ℂ) * Complex.I) *
        Complex.Gamma (((k : ℝ) - 1 / 2 : ℝ) - (t : ℂ) * Complex.I) /
        (Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
          Complex.Gamma (((k : ℝ) - 1 / 2 : ℝ) + (t : ℂ) * Complex.I)))‖ ≤ 8 * Real.sqrt T := by
  simpa only [rankinOscillatoryPhase, rankinGammaPhase_eq] using
    norm_rankinOscillatoryPhase_integral_le hk hT hkT ha hab hb v

/-- The literal normalized product of two unequal-shift Gamma ratios has the same uniform dyadic cancellation. -/
theorem shifted_gamma_oscillation_source {a b c d T l r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hT : 128 ≤ T) (haT : a ≤ T) (hbT : b ≤ T) (hcT : c ≤ T) (hdT : d ≤ T)
    (hl : T ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * T) (v : ℝ) :
    let G : ℝ → ℝ → ℝ → ℂ := fun u w t =>
      Complex.Gamma ((u : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) /
        Complex.Gamma ((w : ℂ) + (t : ℂ) * Complex.I)
    ‖∫ t in l..r, Complex.exp (Complex.I * ((v * t : ℝ) : ℂ)) *
      (G a b t / (‖G a b t‖ : ℂ)) * (G c d t / (‖G c d t‖ : ℂ))‖ ≤ 8 * Real.sqrt T := by
  exact norm_doubleGammaOscillatoryPhase_integral_le ha hb hc hd hT haT hbT hcT hdT hl hlr hr v


/-- The literal unequal-shift reflected Gamma ratio has its sharp power and true amplitude derivative bounds. -/
theorem gamma_ratio_amplitude_source {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 1 ≤ t) :
    ‖Complex.Gamma ((a : ℂ) - (t : ℂ) * Complex.I) /
      Complex.Gamma ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.exp ((4 + max a b) * |a - b|) * t ^ (a - b) ∧
    |deriv (fun u : ℝ => ‖Complex.Gamma ((a : ℂ) - (u : ℂ) * Complex.I) /
      Complex.Gamma ((b : ℂ) + (u : ℂ) * Complex.I)‖) t| ≤
      (33 * |a - b| / t) * ‖Complex.Gamma ((a : ℂ) - (t : ℂ) * Complex.I) /
        Complex.Gamma ((b : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hh := And.intro (norm_reflectedGammaRatio_le ha hb ht) (abs_deriv_norm_reflectedGammaRatio_le ha hb ht)
  simpa only [reflectedGammaRatio, gammaVerticalPoint, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hh

/-- The literal degree-four Riesz Gamma integrand has uniform dyadic cancellation and actual decay outside its stationary window. -/
theorem riesz_gamma_dyadic_source {k r x T l u : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hT : 128 ≤ T) (hkT : 21 + 2 * k ≤ T) (hl : T ≤ l) (hlu : l ≤ u) (hu : u ≤ 2 * T) :
    let β : ℝ := 3 / 8 - r / 4
    let F : ℝ → ℂ := fun t =>
      (x : ℂ) ^ ((β : ℂ) + (t : ℂ) * Complex.I) *
        (Complex.Gamma (1 - ((β : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.Gamma ((k : ℂ) - ((β : ℂ) + (t : ℂ) * Complex.I)) /
          (Complex.Gamma (((β : ℂ) + (t : ℂ) * Complex.I) + ((r + 1 : ℝ) : ℂ)) *
            Complex.Gamma (((β : ℂ) + (t : ℂ) * Complex.I) + ((k - 1 : ℝ) : ℂ))))
    ‖∫ t in l..u, F t‖ ≤ 8 * gammaRieszConstant k r * x ^ β ∧
      ((Real.log x - 4 * Real.log T ≤ -2 ∨ 2 ≤ Real.log x - 4 * Real.log (2 * T)) →
        ‖∫ t in l..u, F t‖ ≤ 2 * gammaRieszConstant k r * x ^ β / Real.sqrt T) := by
  exact ⟨norm_gammaRieszIntegrand_integral_le hk hr0 hr2 hx hT hkT hl hlu hu,
    fun hwindow => norm_gammaRieszIntegrand_integral_le_off_window hk hr0 hr2 hx hT hkT hl hlu hu hwindow⟩


/-- The literal symmetric improper Riesz Gamma integral converges and has a sharp uniform power bound. -/
theorem riesz_gamma_improper_kernel_source {k r : ℝ} (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      let β : ℝ := 3 / 8 - r / 4
      let F : ℝ → ℂ := fun t =>
        (x : ℂ) ^ ((β : ℂ) + (t : ℂ) * Complex.I) *
          (Complex.Gamma (1 - ((β : ℂ) + (t : ℂ) * Complex.I)) *
            Complex.Gamma ((k : ℂ) - ((β : ℂ) + (t : ℂ) * Complex.I)) /
            (Complex.Gamma (((β : ℂ) + (t : ℂ) * Complex.I) + ((r + 1 : ℝ) : ℂ)) *
              Complex.Gamma (((β : ℂ) + (t : ℂ) * Complex.I) + ((k - 1 : ℝ) : ℂ))))
      Tendsto (fun u : ℝ => (1 / (2 * Real.pi) : ℝ) • ∫ t in -u..u, F t) atTop
        (𝓝 (gammaRieszKernel k r x)) ∧ ‖gammaRieszKernel k r x‖ ≤ C * x ^ β := by
  obtain ⟨C, hC, hbound⟩ := exists_gammaRieszKernel_bound hk hr0 hr2
  exact ⟨C, hC, fun x hx => ⟨tendsto_gammaRieszKernel hk hr0 hr2 hx, hbound x hx⟩⟩

/-- The actual order-zero and order-two kernels have exactly the two powers required by sharp Rankin unsmoothing. -/
theorem riesz_kernel_order_zero_two_source {k : ℝ} (hk : 2 ≤ k) :
    ∃ C₀ C₂ : ℝ, 0 < C₀ ∧ 0 < C₂ ∧ ∀ x : ℝ, 0 < x →
      ‖gammaRieszKernel k 0 x‖ ≤ C₀ * x ^ (3 / 8 : ℝ) ∧
        ‖gammaRieszKernel k 2 x‖ ≤ C₂ * x ^ (-(1 / 8 : ℝ)) := by
  obtain ⟨C₀, hC₀, h0⟩ := exists_gammaRieszKernel_bound hk (r := 0) (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂, h2⟩ := exists_gammaRieszKernel_bound hk (r := 2) (by norm_num) (by norm_num)
  refine ⟨C₀, C₂, hC₀, hC₂, fun x hx => ?_⟩
  constructor
  · simpa using h0 x hx
  · convert h2 x hx using 1
    norm_num


/-- The literal normalized symmetric Riesz cutoff has an explicit error from the actual improper kernel. -/
theorem riesz_kernel_truncation_source {k r x T : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hT : max 128 (max (21 + 2 * k) (Real.exp ((Real.log x + 2) / 4))) ≤ T) :
    let β : ℝ := 3 / 8 - r / 4
    let F : ℝ → ℂ := fun t =>
      (x : ℂ) ^ ((β : ℂ) + (t : ℂ) * Complex.I) *
        (Complex.Gamma (1 - ((β : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.Gamma ((k : ℂ) - ((β : ℂ) + (t : ℂ) * Complex.I)) /
          (Complex.Gamma (((β : ℂ) + (t : ℂ) * Complex.I) + ((r + 1 : ℝ) : ℂ)) *
            Complex.Gamma (((β : ℂ) + (t : ℂ) * Complex.I) + ((k - 1 : ℝ) : ℂ))))
    ‖gammaRieszKernel k r x - (1 / (2 * Real.pi) : ℝ) • ∫ t in -T..T, F t‖ ≤
      4 * gammaRieszConstant k r * x ^ β / (Real.pi * Real.sqrt T) :=
  norm_gammaRieszKernel_sub_cutoff_le hk hr0 hr2 hx hT

/-- The literal finite-rectangle contour shift preserves the genuine kernel, uniformly on every compact positive interval. -/
theorem riesz_gamma_contour_shift_source {k r a b β : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (ha : 0 < a) (hab : a ≤ b)
    (hβ0 : 3 / 8 - r / 4 ≤ β) (hβ1 : β ≤ 3 / 8) :
    TendstoUniformlyOn
      (fun T x : ℝ => (1 / (2 * Real.pi) : ℝ) • ∫ t in -T..T,
        (x : ℂ) ^ ((β : ℂ) + (t : ℂ) * Complex.I) *
          (Complex.Gamma (1 - ((β : ℂ) + (t : ℂ) * Complex.I)) *
            Complex.Gamma ((k : ℂ) - ((β : ℂ) + (t : ℂ) * Complex.I)) /
            (Complex.Gamma (((β : ℂ) + (t : ℂ) * Complex.I) + ((r + 1 : ℝ) : ℂ)) *
              Complex.Gamma (((β : ℂ) + (t : ℂ) * Complex.I) + ((k - 1 : ℝ) : ℂ)))))
      (gammaRieszKernel k r) atTop (Set.Icc a b) :=
  tendstoUniformlyOn_gammaRieszVerticalCutoff hk hr0 hr2 ha hab hβ0 hβ1


/-- The true improper Riesz kernels satisfy both adjacent-order derivative identities, at every positive dilation and parameter. -/
theorem riesz_kernel_derivative_source {k c x : ℝ} (hk : 2 ≤ k) (hc : 0 < c) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * gammaRieszKernel k 1 (c * y))
      (gammaRieszKernel k 0 (c * x)) x ∧
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * gammaRieszKernel k 2 (c * y))
      ((x : ℂ) * gammaRieszKernel k 1 (c * x)) x :=
  ⟨hasDerivAt_gammaRieszKernel_one hk hc hx, hasDerivAt_gammaRieszKernel_two hk hc hx⟩

/-- The literal second difference of the actual order-two kernel has both sharp low- and high-frequency bounds, with constants depending only on k. -/
theorem riesz_kernel_difference_source {k : ℝ} (hk : 2 ≤ k) :
    ∃ C₀ C₂ : ℝ, 0 < C₀ ∧ 0 < C₂ ∧ ∀ c x h : ℝ, 0 < c → 0 < x → 0 ≤ h → h ≤ x →
      let D : ℂ := ((x + 2 * h : ℝ) : ℂ) ^ 2 * gammaRieszKernel k 2 (c * (x + 2 * h)) -
        2 * (((x + h : ℝ) : ℂ) ^ 2 * gammaRieszKernel k 2 (c * (x + h))) +
          (x : ℂ) ^ 2 * gammaRieszKernel k 2 (c * x)
      ‖D‖ ≤ C₀ * h ^ 2 * (c * x) ^ (3 / 8 : ℝ) ∧
        ‖D‖ ≤ C₂ * c ^ (-(1 / 8 : ℝ)) * x ^ (15 / 8 : ℝ) := by
  obtain ⟨C₀, hC₀, hl⟩ := exists_gammaRieszSecondDifference_low_bound hk
  obtain ⟨C₂, hC₂, hh⟩ := exists_gammaRieszSecondDifference_high_bound hk
  exact ⟨C₀, C₂, hC₀, hC₂, fun c x h hc hx h0 h1 => ⟨hl c x h hc hx h0 h1, hh c x h hc hx h0 h1⟩⟩


/-- The actual cusp Rankin coefficients satisfy both sharp dual power bounds, with no mean or summability premise supplied by the consumer. -/
theorem rankin_dual_power_sums_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (rankinConvolutionCoefficients f n).re * (n : ℝ) ^ (-(5 / 8 : ℝ))) ≤
          C * (N : ℝ) ^ (3 / 8 : ℝ) ∧
      Summable (fun n : ℕ => if N < n then
        (rankinConvolutionCoefficients f n).re * (n : ℝ) ^ (-(9 / 8 : ℝ)) else 0) ∧
      (∑' n : ℕ, if N < n then (rankinConvolutionCoefficients f n).re *
        (n : ℝ) ^ (-(9 / 8 : ℝ)) else 0) ≤ C * (N : ℝ) ^ (-(1 / 8 : ℝ)) :=
  exists_rankinConvolution_power_bounds f hk


/-- The literal Rankin Gamma dual series converges absolutely from the actual cusp coefficient mean. -/
theorem rankin_gamma_dual_series_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) (hk : 2 ≤ k) {A x : ℝ} (hA : 0 < A) (hx : 0 < x) :
    Summable (fun n : ℕ => ‖(rankinConvolutionCoefficients f n / (n : ℂ)) *
      ((x : ℂ) ^ 2 * gammaRieszKernel (k : ℝ) 2 (A * n * x))‖) :=
  summable_norm_rankinGammaDualTerm f hk hA hx

/-- The literal actual Rankin Gamma series has the exact three-fifths optimized second-difference bound; identification with the Riesz error is a separate obligation. -/
theorem rankin_gamma_dual_optimization_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 2 ≤ k) {A : ℝ} (hA : 0 < A) :
    let F : ℝ → ℂ := fun y => ∑' n : ℕ, (rankinConvolutionCoefficients f n / (n : ℂ)) *
      ((y : ℂ) ^ 2 * gammaRieszKernel (k : ℝ) 2 (A * n * y))
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      let h : ℝ := x ^ (3 / 5 : ℝ)
      ‖F (x + 2 * h) - 2 * F (x + h) + F x‖ / h ^ 2 ≤ C * x ^ (3 / 5 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_rankinGammaDualSeries_three_fifths_bound f hk hA
  refine ⟨C, hC, fun x hx => ?_⟩
  simpa only [rankinGammaDualSeries_eq] using hb x hx


/-- The actual general-level Rankin series has a global meromorphic continuation with its genuine positive residue. -/
theorem rankin_global_continuation_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) (hf : f ≠ 0) :
    Differentiable ℂ (rankinConvolutionEntireNumerator f) ∧
    (∀ s : ℂ, 1 < s.re → rankinConvolutionEntireNumerator f s / (s - 1) =
      LSeries (rankinConvolutionCoefficients f) s) ∧
    0 < rankinConvolutionResidue f ∧
    Tendsto (fun s : ℂ => (s - 1) * (rankinConvolutionEntireNumerator f s / (s - 1)))
      (𝓝[≠] 1) (𝓝 (rankinConvolutionResidue f : ℂ)) :=
  ⟨differentiable_rankinConvolutionEntireNumerator f,
    fun _ hs => rankinConvolutionGlobalContinuation_eq_series f hk.le hs,
    rankinConvolutionResidue_pos f hk hf, rankinConvolutionGlobalContinuation_residue_one f hk⟩

/-- The actual full-level reflected Perron factor is the literal two-Gamma symbol times the original convergent coefficient series. -/
theorem level_one_rankin_riesz_reflection_source {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 ≤ k) {s : ℂ} (hl : -1 < s.re) (hr : s.re < 0) :
    (rankinConvolutionEntireNumerator f s / (s - 1)) / (s * (s + 1) * (s + 2)) =
      (4 * Real.pi ^ 2 : ℂ) ^ (2 * s - 1) *
        (Complex.Gamma (1 - s) * Complex.Gamma ((k : ℂ) - s) /
          (Complex.Gamma (s + (2 + 1)) * Complex.Gamma (s + ((k : ℂ) - 1)))) *
        LSeries (rankinConvolutionCoefficients f) (1 - s) := by
  simpa only [gammaRieszSymbol, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_intCast] using rankinConvolution_riesz_reflection f hk hl hr

/-- Phragmen-Lindelof consumes the actual cusp completion and reflected series, yielding the exact seven-halves numerator bound throughout the strip. -/
theorem level_one_rankin_polynomial_strip_source {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 / 8 ≤ s.re → s.re ≤ 9 / 8 →
      ‖rankinConvolutionEntireNumerator f s‖ ≤ C * ‖s + 2‖ ^ (7 / 2 : ℝ) :=
  exists_rankinConvolutionEntireNumerator_polynomial_strip_bound f hk

/-- Both literal horizontal integrals of the actual continued Rankin Perron function vanish. -/
theorem level_one_rankin_perron_horizontal_source {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    let F : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 2) *
      (rankinConvolutionEntireNumerator f s / (s - 1)) / (s * (s + 1) * (s + 2))
    Tendsto (fun T : ℝ => HIntegral F (-1 / 8) (9 / 8) T) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => HIntegral F (-1 / 8) (9 / 8) (-T)) atTop (𝓝 0) :=
  tendsto_rankinPerron_horizontal_zero f hk hx


/-- The actual continued Perron rectangle at every positive level has both literal pole contributions. -/
theorem rankin_two_pole_contour_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) {x T : ℝ} (hx : 0 < x) (hT : 0 < T) :
    RectangleIntegral' (rankinPerronContinuation f x) ((-1 / 8 : ℂ) - T * Complex.I)
      ((9 / 8 : ℂ) + T * Complex.I) =
      (rankinConvolutionResidue f : ℂ) * (x : ℂ) ^ 3 / 6 -
        rankinConvolutionEntireNumerator f 0 * (x : ℂ) ^ 2 / 2 :=
  rankinPerron_rectangle_residues f hk hx hT

/-- The original finite full-level Riesz sum equals the actual convergent coefficient-weighted Gamma series with its exact conductor and both residues. -/
theorem level_one_rankin_riesz_dual_source {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re * (x - n) ^ 2 / 2 : ℝ) : ℂ) =
      (rankinConvolutionResidue f : ℂ) * (x : ℂ) ^ 3 / 6 -
        rankinConvolutionEntireNumerator f 0 * (x : ℂ) ^ 2 / 2 +
        ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * ∑' n : ℕ,
          (rankinConvolutionCoefficients f n / (n : ℂ)) *
            ((x : ℂ) ^ 2 * gammaRieszKernel (k : ℝ) 2 (((4 * Real.pi ^ 2) ^ 2) * n * x)) := by
  rw [← rankinConvolutionRiesz_eq, ← rankinGammaDualSeries_eq]
  exact rankinConvolutionRiesz_eq_dual f hk hx

/-- The genuine full-level convolution sum has the precise x^(3/5) error for all real cutoffs above one. -/
theorem level_one_rankin_summatory_source {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re) - rankinConvolutionResidue f * x| ≤
        C * x ^ (3 / 5 : ℝ) :=
  exists_level_one_rankinConvolution_three_fifths f hk

/-- The actual nonzero full-level cusp form satisfies the literal source Rankin--Selberg asymptotic, with its positive Petersson residue and exact uniform exponent. -/
theorem level_one_rankin_selberg_source {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 2 ≤ k) (hf : f ≠ 0) :
    0 < cuspRankinResidue f ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
        |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖normalizedCuspCoefficients f n‖ ^ 2) - cuspRankinResidue f * x| ≤
          C * x ^ (3 / 5 : ℝ)) ∧
      (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖normalizedCuspCoefficients f n‖ ^ 2) - cuspRankinResidue f * x)
        =O[Filter.atTop] (fun x : ℝ => x ^ (3 / 5 : ℝ)) :=
  ⟨(level_one_rankin_selberg f hk hf).1, exists_level_one_cusp_square_three_fifths f hk,
    level_one_cusp_square_three_fifths_remainder f hk⟩


section
open scoped MatrixGroups Pointwise

/-- Actual arbitrary-period cusp Fourier energy is the literal horizontal integral and coefficient-square series. -/
theorem cusp_period_parseval_source {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => ‖(UpperHalfPlane.qExpansion h f).coeff n‖ ^ 2 *
      Real.exp (-4 * Real.pi * n * y / h))
      (∫ x in (0 : ℝ)..1, ‖f ⟨((h * x : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) :=
  hasSum_cusp_period_horizontal_energy f hh hΓ hy

/-- Actual period-normalized coefficients have the exact absolutely convergent Mellin identity with the full width factor. -/
theorem cusp_period_mellin_source {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (hk : 0 < k)
    {s : ℂ} (hs : 1 < s.re) :
    let F := fun y : ℝ => (y : ℂ) ^ (s + (k : ℂ) - 2) *
      ((∫ x in (0 : ℝ)..1, ‖f (UpperHalfPlane.ofComplex (((h * x : ℝ) : ℂ) + y * Complex.I))‖ ^ 2 : ℝ) : ℂ)
    IntegrableOn F (Set.Ioi 0) ∧ (∫ y : ℝ in Set.Ioi 0, F y) =
      (((4 * Real.pi / h : ℝ) : ℂ) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1)) *
        LSeries (fun n => ((‖normalizedCuspPeriodCoefficients f h n‖ ^ 2 : ℝ) : ℂ)) s :=
  ⟨integrableOn_cuspPeriodRankin_mellin f hh hΓ hk hs, cuspPeriodRankinSeries_mellin f hh hΓ hk hs⟩

/-- The original Gamma0 domain transports to the actual mixed congruence group without a multiplicity change. -/
theorem rectangular_domain_source (a b : ℕ) [NeZero a] [NeZero b] :
    IsFundamentalDomain (realProjectiveIntegralSubgroup (rectangularCongruenceSubgroup a b))
      (levelRaiseMatrix a • gamma0FundamentalDomain (a * b)) (volume : Measure UpperHalfPlane) ∧
    IsFundamentalDomain (realProjectiveIntegralSubgroup (rectangularCongruenceSubgroup a b))
      (⋃ q : SL(2, ℤ) ⧸ rectangularCongruenceSubgroup a b,
        (q.out : SL(2, ℤ))⁻¹ • (ModularGroup.fdo : Set UpperHalfPlane)) (volume : Measure UpperHalfPlane) :=
  ⟨isFundamentalDomain_rectangular_translate a b, isFundamentalDomain_rectangular_coset a b⟩

/-- The original cusp form supplies actual nonnegative rescaled coefficients and their genuine linear mean and convergence. -/
theorem rectangular_dual_coefficients_source {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 (a * b)).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) :
    rectangularDualCoefficients f 0 = 0 ∧ (∀ n, 0 ≤ (rectangularDualCoefficients f n).re) ∧
      (∀ n, (rectangularDualCoefficients f n).im = 0) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
        (∑ n ∈ Finset.Icc 1 X, (rectangularDualCoefficients f n).re) ≤ C * X) ∧
      (∀ s : ℂ, 1 < s.re → LSeriesSummable (rectangularDualCoefficients f) s) :=
  ⟨(rectangularDualCoefficients_positive f).1, (rectangularDualCoefficients_positive f).2.1,
    (rectangularDualCoefficients_positive f).2.2, exists_rectangularDual_sum_upper f hk,
    fun _ hs => rectangularDual_lseriesSummable f hk hs⟩

/-- The true one-period trace consumes all common-period cusp expansions and their exact Mellin transform. -/
theorem cusp_trace_mellin_source {N : ℕ} [NeZero N] {H : Subgroup SL(2, ℤ)}
    [Fintype (SL(2, ℤ) ⧸ H)] (hH : CongruenceSubgroup.Gamma N ≤ H) {k : ℤ}
    (f : CuspForm (H.map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) (hk : 0 < k)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (s + (k : ℂ) - 2) *
      ((∫ x in (0 : ℝ)..1, ∑ q : SL(2, ℤ) ⧸ H,
        ‖cuspCosetFamily hH f q (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2 : ℝ) : ℂ)) =
      (((4 * Real.pi / N : ℝ) : ℂ) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1)) *
        LSeries (fun n => ((∑ q : SL(2, ℤ) ⧸ H,
          ‖normalizedCuspPeriodCoefficients (cuspCosetFamily hH f q) N n‖ ^ 2 : ℝ) : ℂ)) s :=
  cuspTrace_mellin_identity hH f hk hs

end


section
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The genuine finite subgroup tiling transports the absolutely integrable completed lattice density into the literal finite cusp trace. -/
theorem cusp_lattice_trace_integral_source {N : ℕ} [NeZero N] {H : Subgroup SL(2, ℤ)}
    [Fintype (SL(2, ℤ) ⧸ H)] (hH : Gamma N ≤ H) (hCenter : Subgroup.center SL(2, ℤ) ≤ H)
    {k : ℤ} (f : CuspForm (H.map (mapGL ℝ)) k) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun z : ℍ => latticeCompletedMellin z s * petersson k f f z) (integralSubgroupDomain H) ∧
      (∫ z : ℍ in integralSubgroupDomain H, latticeCompletedMellin z s * petersson k f f z) =
        ∫ z : ℍ in ModularGroup.fdo, latticeCompletedMellin z s *
          ∑ q : SL(2, ℤ) ⧸ H, petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z := by
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_le hH
  exact ⟨integrableOn_lattice_petersson_integralSubgroup hCenter f hs,
    lattice_cusp_integral_eq_trace hH hCenter f hs⟩

/-- The actual primitive Eisenstein trace unfolds with the precise common-period Mellin factor and literal cusp-square coefficients. -/
theorem cusp_trace_eisenstein_series_source {N : ℕ} [NeZero N] {H : Subgroup SL(2, ℤ)}
    [Fintype (SL(2, ℤ) ⧸ H)] (hH : Gamma N ≤ H) {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) (hk : 0 < k) {σ : ℝ} (hσ : 1 < σ) :
    (∫ z : ℍ in ModularGroup.fdo, gamma0Eisenstein 1 (σ : ℂ) z *
      ∑ q : SL(2, ℤ) ⧸ H, petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z) =
      (((4 * Real.pi / N : ℝ) : ℂ) ^ (-((σ : ℂ) + (k : ℂ) - 1)) *
        Complex.Gamma ((σ : ℂ) + (k : ℂ) - 1)) *
          LSeries (fun n => ((∑ q : SL(2, ℤ) ⧸ H,
            ‖normalizedCuspPeriodCoefficients (cuspCosetFamily hH f q) N n‖ ^ 2 : ℝ) : ℂ)) (σ : ℂ) :=
  cuspTrace_eisenstein_mellin hH f hk hσ

/-- The literal reflected rectangular cusp integral is its actual convergent dual coefficient series with the exact determinant, width and two Gamma factors. -/
theorem rectangular_reflected_dual_series_source {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ} (hs : s.re < 0) :
    LSeriesSummable (rectangularDualCoefficients f) (1 - s) ∧
      (∫ z : ℍ in gamma0FundamentalDomain (a * b),
        latticeCompletedMellin (rectangularLatticePoint (a * b) b (Nat.pos_of_neZero _) (Nat.pos_of_neZero _) z) s *
          petersson k f f z) =
        ((a : ℂ) ^ (k - 2) * ((Real.pi : ℂ) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
          (((4 * Real.pi / (a * b) : ℝ) : ℂ) ^ (-((1 - s) + (k : ℂ) - 1)) *
            Complex.Gamma ((1 - s) + (k : ℂ) - 1)))) *
              LSeries (rectangularDualCoefficients f) (1 - s) := by
  refine ⟨rectangularDual_lseriesSummable f hk (by simp only [Complex.sub_re, Complex.one_re]; linarith), ?_⟩
  simpa only [rectangularLatticeCuspCompleted, rectangularDualFactor, cuspTraceRankinFactor, Nat.cast_mul] using
    rectangularLatticeCuspCompleted_reflected_dual f hk hs

/-- The actual general-level completion is a finite Möbius sum of genuine convergent reflected cusp series; no scalar full-level reflection is assumed. -/
theorem general_level_reflected_dual_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ} (hs : s.re < 0) :
    (∀ d : Q.divisors, LSeriesSummable (divisorRectangularDualCoefficients f d) (1 - s)) ∧
      gamma0CompletedCusp f s = ∑ d : Q.divisors,
        (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s) *
          ((Q / d.val : ℕ) : ℂ) ^ (k - 2) *
            ((Real.pi : ℂ) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
              (((4 * Real.pi / Q : ℝ) : ℂ) ^ (-((1 - s) + (k : ℂ) - 1)) *
                Complex.Gamma ((1 - s) + (k : ℂ) - 1))) *
                  LSeries (divisorRectangularDualCoefficients f d) (1 - s) := by
  refine ⟨fun d => divisorRectangularDual_lseriesSummable f hk d
    (by simp only [Complex.sub_re, Complex.one_re]; linarith), ?_⟩
  rw [gamma0CompletedCusp_reflected_dual f hk hs]
  apply Finset.sum_congr rfl
  intro d _
  simp only [rectangularDualFactor, cuspTraceRankinFactor,
    Nat.div_mul_cancel (Nat.dvd_of_mem_divisors d.property)]
  ring

end


section
open CongruenceSubgroup Matrix.SpecialLinearGroup

/-- The general-level reflection uses actual divisor coefficient series, with exact positive conductors and signed amplitudes. -/
theorem general_rankin_riesz_reflection_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ}
    (hl : -1 < s.re) (hr : s.re < 0) :
    rankinConvolutionGlobalContinuation f s / (s * (s + 1) * (s + 2)) =
      ∑ d : Q.divisors,
        ((ArithmeticFunction.moebius d.val : ℂ) * ((Q / d.val : ℕ) : ℂ) ^ (k - 2) * (Q : ℂ) ^ k /
          (4 * Real.pi ^ 2 : ℂ)) *
        (((4 * Real.pi ^ 2) ^ 2 / ((Q : ℝ) ^ 2 * (d.val : ℝ)) : ℝ) : ℂ) ^ s *
          gammaRieszSymbol (k : ℝ) 2 s * LSeries (divisorRectangularDualCoefficients f d) (1 - s) :=
  general_rankinConvolution_riesz_reflection f hk hl hr

/-- The literal original finite Riesz sum equals both genuine pole terms and the actual finite family of coefficient-weighted Gamma transforms. -/
theorem general_rankin_riesz_dual_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re * (x - n) ^ 2 / 2 : ℝ) : ℂ) =
      (rankinConvolutionResidue f : ℂ) * (x : ℂ) ^ 3 / 6 -
        rankinConvolutionEntireNumerator f 0 * (x : ℂ) ^ 2 / 2 +
        ∑ d : Q.divisors, divisorRankinAmplitude Q d.val k * ∑' n : ℕ,
          (divisorRectangularDualCoefficients f d n / (n : ℂ)) *
            ((x : ℂ) ^ 2 * gammaRieszKernel (k : ℝ) 2 (divisorRankinConductor Q d.val * n * x)) := by
  rw [← rankinConvolutionRiesz_eq]
  simpa only [generalRankinGammaDualSeries, divisorGammaDualSeries_eq] using
    general_rankinConvolutionRiesz_eq_dual f hk hx

/-- Every genuine nonzero cusp form of weight at least two and positive level satisfies the exact source three-fifths square-sum asymptotic, with its actual positive Petersson residue. -/
theorem general_rankin_selberg_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) (hf : f ≠ 0) :
    0 < cuspRankinResidue f ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
        |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖normalizedCuspCoefficients f n‖ ^ 2) - cuspRankinResidue f * x| ≤
          C * x ^ (3 / 5 : ℝ)) ∧
      (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖normalizedCuspCoefficients f n‖ ^ 2) - cuspRankinResidue f * x)
        =O[Filter.atTop] (fun x : ℝ => x ^ (3 / 5 : ℝ)) :=
  ⟨(general_rankin_selberg f hk hf).1, exists_general_cusp_square_three_fifths f hk,
    general_cusp_square_three_fifths_remainder f hk⟩

/-- The actual positive-level normalized cusp squares satisfy all literal source weighted-energy regimes without an assumed Rankin--Selberg input. -/
theorem general_cusp_weighted_energy_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) (hf : f ≠ 0) :
    0 < cuspRankinResidue f ∧
      (∀ σ : ℝ, σ < 1 / 2 → Tendsto (fun N : ℕ =>
        ((∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) -
          cuspRankinResidue f * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ)) /
            (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0)) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
        |(∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 : ℝ))) -
          cuspRankinResidue f * Real.log N| ≤ B) ∧
      (∀ σ : ℝ, 1 / 2 < σ → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
        0 ≤ (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) ∧
          (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) ≤ B) :=
  general_cusp_weighted_rankin_selberg f hk hf

/-- The actual source energy error includes both the unweighted endpoint and the three-tenths logarithmic transition with genuine constants. -/
theorem general_cusp_weighted_energy_endpoints_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    (∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-2 * (0 : ℝ))) -
        cuspRankinResidue f * N| ≤ C * (N : ℝ) ^ (3 / 5 : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-2 * (3 / 10 : ℝ))) -
        weightedEnergyMain (cuspRankinResidue f) N (3 / 10)| ≤ C * (1 + (3 / 5) * Real.log N)) :=
  ⟨exists_general_cusp_weighted_energy_zero f hk, exists_general_cusp_weighted_energy_three_tenths f hk⟩


/-- The genuine coefficient law has the exact orthonormal symmetric-power characters, with no arithmetic input. -/
theorem sato_tate_character_orthogonality_source (m n : ℕ) :
    (∫ x, (Polynomial.Chebyshev.S ℝ (m : ℤ)).eval x *
      (Polynomial.Chebyshev.S ℝ (n : ℤ)).eval x ∂(satoTateProbability : Measure ℝ)) =
        if m = n then 1 else 0 :=
  integral_satoTate_character_pair m n

/-- Genuine primitive coefficients, rather than a separately supplied recurrence sequence, realize every symmetric-power character. -/
theorem primitive_normalized_prime_power_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) (r : ℕ) :
    normalizedCuspCoefficients f.toCuspForm (p ^ r) =
      (Polynomial.Chebyshev.S ℂ (r : ℤ)).eval (normalizedCuspCoefficients f.toCuspForm p) ∧
    (normalizedCuspCoefficients f.toCuspForm (p ^ r)).re =
      (Polynomial.Chebyshev.S ℝ (r : ℤ)).eval (normalizedCuspCoefficients f.toCuspForm p).re :=
  ⟨primitiveCuspForm_normalized_primePower_chebyshev f hp hpQ r,
    primitiveCuspForm_normalized_primePower_re f hp hpQ r⟩

/-- The actual arithmetic-input reduction derives both the weak Sato--Tate law and all isolated-prime H2 requirements, with the two remaining arithmetic premises displayed. -/
theorem primitive_prime_character_blocks_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (hav : ∀ r : ℕ, 0 < r → Tendsto (fun N : ℕ =>
      (∑ p ∈ Nat.primesLE N, (normalizedCuspCoefficients f.toCuspForm (p ^ r)).re) /
        Nat.primeCounting N) atTop (𝓝 0)) :
    Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability) ∧
    let B := selectedDyadicPrimes (fun p => ¬p ∣ Q ∧
      1 ≤ ‖normalizedCuspCoefficients f.toCuspForm p‖ ∧ ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    IsolatedPrimeBlocks B ∧ Tendsto (fun N => (B N).card) atTop atTop ∧
      PrimeCoefficientComparability (normalizedCuspCoefficients f.toCuspForm) B (1 / 2) ∧
        IsolatedEnergyAsymptotic (normalizedCuspCoefficients f.toCuspForm) B (1 / 2) := by
  have hST := primitive_satoTate_of_primePower_averages f hbound hav
  exact ⟨hST, sato_tate_selected_primes_H2 (Nat.pos_of_neZero Q)
    (fun p hp hpQ => primitiveCuspForm_normalizedCoefficient_im f p
      (hp.coprime_iff_not_dvd.mpr hpQ)) hST⟩

end


section

/-- The genuine primitive coefficient supplies the trace, determinant and exact purity/bound equivalence for its own constructed roots. -/
theorem primitive_satake_normalization_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) :
    primitiveSatakePlus f p + primitiveSatakeMinus f p = normalizedCuspCoefficients f.toCuspForm p ∧
    primitiveSatakePlus f p * primitiveSatakeMinus f p = 1 ∧
    ((‖primitiveSatakePlus f p‖ = 1 ∧ ‖primitiveSatakeMinus f p‖ = 1) ↔
      ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2) :=
  ⟨(primitiveSatake_trace_det f p).1, (primitiveSatake_trace_det f p).2,
    primitiveSatake_unit_iff_bound f hp hpQ⟩

/-- The actual normalized Fourier L-series has its absolutely convergent all-prime rational Euler product, without a Deligne premise. -/
theorem primitive_cusp_euler_product_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖normalizedCuspCoefficients f.toCuspForm n * (n : ℂ) ^ (-s)‖) ∧
    HasProd (fun p : Nat.Primes =>
      (1 - normalizedCuspCoefficients f.toCuspForm p * ((p : ℕ) : ℂ) ^ (-s) +
        if (p : ℕ) ∣ Q then 0 else (((p : ℕ) : ℂ) ^ (-s)) ^ 2)⁻¹)
      (LSeries (normalizedCuspCoefficients f.toCuspForm) s) ∧
    (∀ p : ℕ, Nat.Prime p →
      1 - normalizedCuspCoefficients f.toCuspForm p * (p : ℂ) ^ (-s) +
        (if p ∣ Q then 0 else ((p : ℂ) ^ (-s)) ^ 2) ≠ 0) :=
  ⟨summable_norm_cusp_dirichlet f.toCuspForm hk hs,
    primitive_cusp_lseries_rational_euler_hasProd f hk hs,
    fun _ hp => primitiveEulerDenominator_ne_zero f hk hp hs⟩

/-- The genuine local symmetric-power spectral product has precisely the original normalized prime-power coefficient as its first reciprocal Taylor coefficient. -/
theorem primitive_symmetric_euler_coefficient_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) (r : ℕ) :
    (primitiveSymmetricEulerPolynomial f p r).coeff 1 =
      -normalizedCuspCoefficients f.toCuspForm (p ^ r) ∧
    HasDerivAt (fun z : ℂ =>
      (∏ i ∈ Finset.range (r + 1),
        (1 - primitiveSatakePlus f p ^ i * primitiveSatakeMinus f p ^ (r - i) * z))⁻¹)
      (normalizedCuspCoefficients f.toCuspForm (p ^ r)) 0 := by
  refine ⟨primitiveSymmetricEulerPolynomial_coeff_one f hp hpQ r, ?_⟩
  simpa only [primitiveSymmetricEulerPolynomial, symmetricEulerPolynomial_eval] using
    primitiveSymmetricEulerPolynomial_inverse_hasDerivAt f hp hpQ r

/-- The genuine prime bound, when supplied explicitly, controls every actual prime-power Fourier coefficient by its exact symmetric-power dimension. -/
theorem primitive_prime_power_dimension_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q)
    (hb : ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2) :
    ∀ r : ℕ, ‖normalizedCuspCoefficients f.toCuspForm (p ^ r)‖ ≤ (r : ℝ) + 1 :=
  primitive_primePower_norm_le_of_prime_bound f hp hpQ hb

end


section

/-- The signed Tauberian deduction uses the actual von Mangoldt majorant and a displayed genuine L-series boundary extension. -/
theorem signed_prime_tauberian_source {a : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ n, |a n| ≤ C * ArithmeticFunction.vonMangoldt n) (G : ℂ → ℂ)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hseries : Set.EqOn G (LSeries (fun n => (a n : ℂ))) {s | 1 < s.re}) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / (N : ℝ)) atTop (𝓝 0) :=
  signed_wiener_vonMangoldt_cancellation hC ha G hG hseries

/-- The literal bounded prime-supported logarithmic Dirichlet series supplies ordinary prime cancellation after all Tauberian and PNT normalization steps. -/
theorem prime_boundary_cancellation_source {u : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ p, Nat.Prime p → |u p| ≤ C) (G : ℂ → ℂ)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hseries : Set.EqOn G
      (LSeries (fun n => ((if Nat.Prime n then u n * Real.log n else 0 : ℝ) : ℂ)))
      {s | 1 < s.re}) :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, u p) / Nat.primeCounting N) atTop (𝓝 0) :=
  prime_average_zero_of_boundary_continuation hC hu G hG hseries

/-- The actual primitive object consumes the two narrower arithmetic inputs, local boundedness and genuine prime-character boundary continuation, to derive both weak Sato--Tate and the full isolated-prime H2. -/
theorem primitive_character_boundary_blocks_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (hboundary : ∀ r : ℕ, 0 < r → ∃ G : ℂ → ℂ,
      ContinuousOn G {s | 1 ≤ s.re} ∧
      Set.EqOn G (LSeries (fun n =>
        ((if Nat.Prime n then (if n ∣ Q then 0 else
          (normalizedCuspCoefficients f.toCuspForm (n ^ r)).re) * Real.log n else 0 : ℝ) : ℂ)))
        {s | 1 < s.re}) :
    Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability) ∧
    let B := selectedDyadicPrimes (fun p => ¬p ∣ Q ∧
      1 ≤ ‖normalizedCuspCoefficients f.toCuspForm p‖ ∧ ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    IsolatedPrimeBlocks B ∧ Tendsto (fun N => (B N).card) atTop atTop ∧
      PrimeCoefficientComparability (normalizedCuspCoefficients f.toCuspForm) B (1 / 2) ∧
        IsolatedEnergyAsymptotic (normalizedCuspCoefficients f.toCuspForm) B (1 / 2) := by
  have hST := primitive_satoTate_of_character_boundary f hbound hboundary
  exact ⟨hST, sato_tate_selected_primes_H2 (Nat.pos_of_neZero Q)
    (fun p hp hpQ => primitiveCuspForm_normalizedCoefficient_im f p
      (hp.coprime_iff_not_dvd.mpr hpQ)) hST⟩

end


section

/-- The actual primitive roots supply the literal higher-prime-power remainder and its full holomorphy half-plane, conditional only on the displayed local bound. -/
theorem primitive_spectral_tail_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∑' p : Nat.Primes,
      (Real.log (p : ℕ) : ℂ) * ∑ i : Fin (r + 1),
        (primitiveSymmetricSpectralRoots f r p i * (((p : ℕ) : ℂ) ^ (-s))) ^ 2 /
          (1 - primitiveSymmetricSpectralRoots f r p i * (((p : ℕ) : ℂ) ^ (-s))))
      {s : ℂ | 1 / 2 < s.re} :=
  primitiveSymmetricSpectralTail_analyticOnNhd f hbound r

/-- The original prime-character L-series is identified with the actual sum of local Euler logarithmic derivatives, with the complete higher-power correction retained. -/
theorem primitive_spectral_log_series_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (∑' p : Nat.Primes,
      -logDeriv (fun t : ℂ => (∏ i : Fin (r + 1),
        (1 - primitiveSymmetricSpectralRoots f r p i * (((p : ℕ) : ℂ) ^ (-t))))⁻¹) s) =
      LSeries (fun n => ((if Nat.Prime n then (if n ∣ Q then 0 else
        (normalizedCuspCoefficients f.toCuspForm (n ^ r)).re) * Real.log n else 0 : ℝ) : ℂ)) s +
        primeSpectralTail (primitiveSymmetricSpectralRoots f r) s :=
  primitiveSymmetricLogSeries_eq f hbound r hs

/-- Actual primitive local Euler continuation data supplies weak Sato--Tate and the full isolated-prime H2 after the proved holomorphic higher-power correction, Tauberian theorem and PNT. -/
theorem primitive_symmetric_boundary_blocks_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (hboundary : ∀ r : ℕ, 0 < r → ∃ G : ℂ → ℂ,
      ContinuousOn G {s | 1 ≤ s.re} ∧ Set.EqOn G
        (fun s : ℂ => ∑' p : Nat.Primes,
          -logDeriv (primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f r) p) s)
        {s | 1 < s.re}) :
    Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability) ∧
    let B := selectedDyadicPrimes (fun p => ¬p ∣ Q ∧
      1 ≤ ‖normalizedCuspCoefficients f.toCuspForm p‖ ∧ ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    IsolatedPrimeBlocks B ∧ Tendsto (fun N => (B N).card) atTop atTop ∧
      PrimeCoefficientComparability (normalizedCuspCoefficients f.toCuspForm) B (1 / 2) ∧
        IsolatedEnergyAsymptotic (normalizedCuspCoefficients f.toCuspForm) B (1 / 2) := by
  have hST := primitive_satoTate_of_symmetric_log_boundary f hbound hboundary
  exact ⟨hST, sato_tate_selected_primes_H2 (Nat.pos_of_neZero Q)
    (fun p hp hpQ => primitiveCuspForm_normalizedCoefficient_im f p
      (hp.coprime_iff_not_dvd.mpr hpQ)) hST⟩

end


section

/-- The actual primitive symmetric-power L-function is the literal infinite spectral Euler product and is holomorphic and nonzero in its convergence half-plane under the displayed local bound. -/
theorem primitive_symmetric_global_euler_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) :
    AnalyticOnNhd ℂ (primitiveSymmetricLFunction f r) {s : ℂ | 1 < s.re} ∧
    (∀ s : ℂ, 1 < s.re → primitiveSymmetricLFunction f r s ≠ 0) ∧
    (∀ s : ℂ, primitiveSymmetricLFunction f r s =
      (∏' v : Nat.Primes × Fin (r + 1),
        (1 - primitiveSymmetricSpectralRoots f r v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹) :=
  ⟨primitiveSymmetricLFunction_analyticOnNhd f hbound r,
    fun _ hs => primitiveSymmetricLFunction_ne_zero f hbound r hs, fun _ => rfl⟩

/-- The actual global Euler logarithmic derivative has precisely the original prime-character L-series and the fully proved higher-prime-power correction. -/
theorem primitive_symmetric_global_log_derivative_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (primitiveSymmetricLFunction f r) s =
      LSeries (fun n => ((if Nat.Prime n then (if n ∣ Q then 0 else
        (normalizedCuspCoefficients f.toCuspForm (n ^ r)).re) * Real.log n else 0 : ℝ) : ℂ)) s +
        primeSpectralTail (primitiveSymmetricSpectralRoots f r) s := by
  rw [primitiveSymmetricLFunction_logDeriv f hbound r hs, primitiveSymmetricLogSeries_eq f hbound r hs]
  rfl

/-- The genuine primitive form's local bound and actual global symmetric-power nonvanishing continuation give both weak Sato--Tate and full H2 through the proved Euler, holomorphic remainder, Tauberian and PNT chain. -/
theorem primitive_symmetric_continuation_blocks_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (hcontinuation : ∀ r : ℕ, 0 < r → ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (primitiveSymmetricLFunction f r) {s | 1 < s.re}) :
    Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability) ∧
    let B := selectedDyadicPrimes (fun p => ¬p ∣ Q ∧
      1 ≤ ‖normalizedCuspCoefficients f.toCuspForm p‖ ∧ ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    IsolatedPrimeBlocks B ∧ Tendsto (fun N => (B N).card) atTop atTop ∧
      PrimeCoefficientComparability (normalizedCuspCoefficients f.toCuspForm) B (1 / 2) ∧
        IsolatedEnergyAsymptotic (normalizedCuspCoefficients f.toCuspForm) B (1 / 2) := by
  have hST := primitive_satoTate_of_symmetric_L_continuation f hbound hcontinuation
  exact ⟨hST, sato_tate_selected_primes_H2 (Nat.pos_of_neZero Q)
    (fun p hp hpQ => primitiveCuspForm_normalizedCoefficient_im f p
      (hp.coprime_iff_not_dvd.mpr hpQ)) hST⟩

end


section

/-- Without Deligne, the actual first symmetric-power Euler function is holomorphic, nonzero and exactly the original cusp L-series with precisely the finite ramified factors removed. -/
theorem primitive_first_cusp_euler_identity_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) :
    AnalyticOnNhd ℂ (primitiveSymmetricLFunction f 1) {s : ℂ | 1 < s.re} ∧
    ∀ s : ℂ, 1 < s.re →
      primitiveSymmetricLFunction f 1 s = LSeries (normalizedCuspCoefficients f.toCuspForm) s *
        ∏ p ∈ ramifiedPrimeSet Q,
          (1 - normalizedCuspCoefficients f.toCuspForm p * (((p : ℕ) : ℂ) ^ (-s)) +
            if (p : ℕ) ∣ Q then 0 else ((((p : ℕ) : ℂ) ^ (-s))) ^ 2) ∧
      primitiveSymmetricLFunction f 1 s ≠ 0 ∧ LSeries (normalizedCuspCoefficients f.toCuspForm) s ≠ 0 :=
  ⟨primitive_first_symmetric_analyticOnNhd f hk, fun _ hs =>
    ⟨primitive_first_symmetric_eq_cusp_lseries f hk hs,
      primitive_first_symmetric_ne_zero f hk hs, primitive_cusp_lseries_ne_zero f hk hs⟩⟩

/-- The actual ramified prime-power law and proved cusp energy bound give the square-root estimate and nonvanishing of every genuine finite correction across Re(s)=1. -/
theorem primitive_ramified_boundary_factors_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) :
    (∀ p : ℕ, Nat.Prime p → p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 ≤ (p : ℝ)) ∧
    ∀ s : ℂ, 1 / 2 < s.re →
      (∏ p ∈ ramifiedPrimeSet Q,
        (1 - normalizedCuspCoefficients f.toCuspForm p * (((p : ℕ) : ℂ) ^ (-s)) +
          if (p : ℕ) ∣ Q then 0 else ((((p : ℕ) : ℂ) ^ (-s))) ^ 2)) ≠ 0 :=
  ⟨fun _ hp hpQ => primitive_bad_coefficient_norm_sq_le f hk hp hpQ,
    fun _ hs => primitive_ramified_correction_ne_zero f hk hs⟩

/-- The real order-one incomplete spectral Euler product and the original coefficient L-series have equivalent nonvanishing continuation requirements, with no purity or continuation assumption in their definitions. -/
theorem primitive_first_continuation_normalization_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) :
    (∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (fun s => (∏' v : Nat.Primes × Fin 2,
        (1 - primitiveSymmetricSpectralRoots f 1 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹)
        {s | 1 < s.re}) ↔
    (∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (LSeries (normalizedCuspCoefficients f.toCuspForm)) {s | 1 < s.re}) :=
  primitive_first_nonvanishing_continuation_iff f hk

end


section

/-- The actual cusp values give a convergent entire Mellin integral with the precise modular S-transform functional equation. -/
theorem cusp_original_mellin_completion_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) :
    Differentiable ℂ (cuspCompletedLFunction f) ∧
    (∀ s : ℂ, HasMellin (fun y => f (UpperHalfPlane.ofComplex ((y : ℂ) * Complex.I))) s
      (cuspCompletedLFunction f s)) ∧
    (∀ s : ℂ, cuspCompletedLFunction f ((k : ℂ) - s) =
      Complex.I ^ k * cuspCompletedLFunction (CuspForm.translate f ModularGroup.S) s) :=
  ⟨cuspCompletedLFunction_differentiable f hk,
    cuspCompletedLFunction_hasMellin f hk, cuspCompletedLFunction_functional_equation f hk⟩

/-- The exact original Mellin integral and half-weight shift construct an entire continuation of the true normalized cusp coefficient L-series. -/
theorem normalized_cusp_entire_lseries_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) :
    Differentiable ℂ (normalizedCuspLFunction f) ∧
    ∀ s : ℂ, 1 < s.re →
      normalizedCuspLFunction f s = LSeries (normalizedCuspCoefficients f) s ∧
      cuspCompletedLFunction f (s + ((k : ℂ) - 1) / 2) =
        ((2 * Real.pi : ℝ) : ℂ) ^ (-(s + ((k : ℂ) - 1) / 2)) *
          Complex.Gamma (s + ((k : ℂ) - 1) / 2) * LSeries (normalizedCuspCoefficients f) s :=
  ⟨normalizedCuspLFunction_differentiable f hk, fun _ hs =>
    ⟨normalizedCuspLFunction_eq_series f hk.le hs,
      cuspCompletedLFunction_eq_normalized_series f hk.le hs⟩⟩

/-- The genuine first symmetric-power infinite Euler product has a proved entire continuation, nonzero on Re(s)>1; nonvanishing on the boundary is deliberately not asserted. -/
theorem primitive_first_entire_euler_continuation_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      Set.EqOn F (fun s => (∏' v : Nat.Primes × Fin 2,
        (1 - primitiveSymmetricSpectralRoots f 1 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹)
        {s | 1 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → F s ≠ 0 := by
  obtain ⟨F,hFa,hFe⟩ := primitive_first_symmetric_entire_continuation f hk
  refine ⟨F,hFa,hFe,fun s hs => ?_⟩
  rw [hFe hs]
  exact primitive_first_symmetric_ne_zero f hk.le hs

end


section

/-- The actual prime-power coefficient squares have exactly the symmetric-square denominator and numerator 1+p^(-s). -/
theorem primitive_square_local_euler_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q)
    {s : ℂ} (hs : 1 < s.re) :
    (primitiveSymmetricEulerPolynomial f p 2).eval ((p : ℂ) ^ (-s)) *
      (∑' r : ℕ, ((‖normalizedCuspCoefficients f.toCuspForm (p ^ r)‖ ^ 2 : ℝ) : ℂ) *
        ((p : ℂ) ^ (-s)) ^ r) = 1 + (p : ℂ) ^ (-s) :=
  primitive_good_square_euler_identity f hk hp hpQ hs

/-- The literal symmetric-square prime product and original square Dirichlet series satisfy the exact global identity with all actual bad-prime factors. -/
theorem primitive_second_rankin_global_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    (∏' v : Nat.Primes × Fin 3,
      (1 - primitiveSymmetricSpectralRoots f 2 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹ *
        DirichletCharacter.LFunctionTrivChar Q s =
    cuspRankinSeries f.toCuspForm s *
      (∏ p ∈ ramifiedPrimeSet Q,
        (1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s)))) *
          DirichletCharacter.LFunctionTrivChar Q (2 * s) :=
  primitive_second_rankin_global_identity f hk hs

/-- The actual second symmetric Euler product has proved continuation across Re(s)=1 and is nonzero in its convergence region and at the real boundary point one. -/
theorem primitive_second_holomorphic_euler_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      Set.EqOn F (fun s => (∏' v : Nat.Primes × Fin 3,
        (1 - primitiveSymmetricSpectralRoots f 2 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹)
        {s | 1 < s.re} ∧ F 1 ≠ 0 ∧
      ∀ s : ℂ, 1 < s.re → F s ≠ 0 := by
  refine ⟨primitiveSecondContinuation f, primitiveSecondContinuation_analyticOnNhd f (by omega),
    fun _ hs => primitiveSecondContinuation_eq_symmetric f (by omega) hs,
    primitiveSecondContinuation_one_ne_zero f hk, fun s hs => ?_⟩
  rw [primitiveSecondContinuation_eq_symmetric f (by omega) hs]
  exact primitive_second_symmetric_ne_zero f (by omega) hs

/-- The actual Rankin remainder gives the genuine pointwise coefficient bound and a constant-free bound at every ramified prime. -/
theorem primitive_rankin_pointwise_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    (∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n →
      ‖normalizedCuspCoefficients f.toCuspForm n‖ ^ 2 ≤ B * (n : ℝ) ^ (3 / 5 : ℝ)) ∧
    ∀ p : ℕ, Nat.Prime p → p ∣ Q →
      ‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 ≤ (p : ℝ) ^ (3 / 5 : ℝ) :=
  ⟨exists_normalized_cusp_coefficient_three_fifths f.toCuspForm hk,
    fun _ hp hpQ => primitive_bad_coefficient_norm_sq_le_three_fifths f hk hp hpQ⟩

/-- The actual symmetric-square value at one has the true Petersson residue and literal finite Euler corrections, and is proved nonzero. -/
theorem primitive_second_residue_value_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    primitiveSecondContinuation f 1 =
      (cuspRankinResidue f.toCuspForm : ℂ) *
        (∏ p ∈ ramifiedPrimeSet Q,
          (1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-(1 : ℂ))))) *
            DirichletCharacter.LFunctionTrivChar Q 2 /
              (∏ p ∈ Q.primeFactors, (1 - (p : ℂ)⁻¹)) ∧
    primitiveSecondContinuation f 1 ≠ 0 :=
  ⟨primitiveSecondContinuation_one f (by omega), primitiveSecondContinuation_one_ne_zero f hk⟩

end


section

/-- The true good-prime roots obey the proved three-fifths square bound; every genuine Rankin tensor power trace is real and nonnegative. -/
theorem primitive_rankin_spectral_positivity_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    (∀ p : ℕ, Nat.Prime p → ¬p ∣ Q →
      ‖primitiveSatakePlus f p‖ ^ 2 ≤ (p : ℝ) ^ (3 / 5 : ℝ) ∧
        ‖primitiveSatakeMinus f p‖ ^ 2 ≤ (p : ℝ) ^ (3 / 5 : ℝ)) ∧
    (∀ (p : Nat.Primes) (r : ℕ),
      (∑ i : Fin 4, primitiveRankinSpectralRoots f p i ^ r).im = 0 ∧
        0 ≤ (∑ i : Fin 4, primitiveRankinSpectralRoots f p i ^ r).re) :=
  ⟨fun _ hp hpQ => primitiveSatake_norm_sq_le_three_fifths f hk hp hpQ,
    primitiveRankinSpectral_trace_nonneg f⟩

/-- The original Rankin convolution is the true tensor Euler product and satisfies the actual three-four-one norm inequality. -/
theorem primitive_rankin_euler_inequality_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    (∀ s : ℂ, 1 < s.re →
      HasProd (fun p : Nat.Primes =>
        (∏ i : Fin 4, (1 - primitiveRankinSpectralRoots f p i * (((p : ℕ) : ℂ) ^ (-s))))⁻¹)
          (rankinConvolutionGlobalContinuation f.toCuspForm s)) ∧
    ∀ (x y : ℝ), 0 < x →
      1 ≤ ‖rankinConvolutionGlobalContinuation f.toCuspForm (1 + x) ^ 3 *
        rankinConvolutionGlobalContinuation f.toCuspForm (1 + x + Complex.I * y) ^ 4 *
          rankinConvolutionGlobalContinuation f.toCuspForm (1 + x + 2 * Complex.I * y)‖ :=
  ⟨fun _ hs => primitive_rankin_spectral_hasProd f (by omega) hs,
    fun _ y hx => primitive_rankin_global_three_four_one f hk hx y⟩

/-- The genuine Rankin convolution has no zero at any nonreal boundary point, and its entire numerator agrees with the original principal-factor Rankin numerator on the closed half-plane. -/
theorem primitive_rankin_boundary_nonvanishing_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    (∀ s : ℂ, s.re = 1 → s ≠ 1 → rankinConvolutionGlobalContinuation f.toCuspForm s ≠ 0) ∧
    ∀ s : ℂ, 1 ≤ s.re → rankinConvolutionEntireNumerator f.toCuspForm s =
      DirichletCharacter.LFunctionTrivChar Q (2 * s) * cuspRankinPoleNumerator f.toCuspForm s :=
  ⟨fun _ hs hs1 => primitive_rankin_ne_zero_on_boundary f hk hs hs1,
    fun _ hs => rankinConvolutionEntireNumerator_eq_pole_on_closed f (by omega) hs⟩

/-- The original order-two infinite symmetric Euler product has a proved holomorphic nonvanishing continuation on Re(s)≥1, with no prime-bound or continuation hypothesis. -/
theorem primitive_second_nonvanishing_euler_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (fun s => (∏' v : Nat.Primes × Fin 3,
        (1 - primitiveSymmetricSpectralRoots f 2 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹)
        {s | 1 < s.re} :=
  primitive_second_symmetric_nonvanishing_continuation f hk

end


section

/-- The actual Rankin convolution, true principal L-function and explicit first symmetric continuation satisfy the mixed Euler-product norm inequality. -/
theorem primitive_first_mixed_global_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (x y : ℝ) (hx : 0 < x) :
    1 ≤ ‖rankinConvolutionGlobalContinuation f.toCuspForm (1 + x) *
      DirichletCharacter.LFunctionTrivChar Q (1 + x) ^ 2 *
        primitiveFirstContinuation f (1 + x + Complex.I * y) ^ 4 *
          DirichletCharacter.LFunctionTrivChar Q (1 + x + 2 * Complex.I * y) ^ 2‖ :=
  primitive_mixed_global_inequality f hk hx y

/-- The literal first symmetric Euler product has an explicit entire continuation, nonzero on the closed half-plane except possibly at one, with its genuine Gamma-normalized trivial zero. -/
theorem primitive_first_nonreal_boundary_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    Differentiable ℂ (primitiveFirstContinuation f) ∧
      Set.EqOn (primitiveFirstContinuation f) (fun s => (∏' v : Nat.Primes × Fin 2,
        (1 - primitiveSymmetricSpectralRoots f 1 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹)
        {s | 1 < s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → s ≠ 1 → primitiveFirstContinuation f s ≠ 0) ∧
      primitiveFirstContinuation f (((1 - (k : ℝ)) / 2 : ℝ) : ℂ) = 0 :=
  ⟨primitiveFirstContinuation_differentiable f (by omega),
    fun _ hs => primitiveFirstContinuation_eq_symmetric f (by omega) hs,
    fun _ hs hs1 => primitiveFirstContinuation_ne_zero_of_ne_one f hk hs hs1,
    primitiveFirstContinuation_trivial_zero f⟩

/-- Under a hypothetical actual first-power zero at one, the genuine divided-difference Rankin product is entire, agrees with the original Euler product, and retains a real trivial zero. This is a conditional contradiction setup, not a proof of nonvanishing at one. -/
theorem primitive_first_hypothetical_zero_cancellation_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (hz : primitiveFirstContinuation f 1 = 0) :
    Differentiable ℂ (firstRankinPoleCancellation f) ∧
      (∀ s : ℂ, 1 < s.re → firstRankinPoleCancellation f s =
        DirichletCharacter.LFunctionTrivChar Q s * rankinConvolutionGlobalContinuation f.toCuspForm s *
          (∏ p ∈ ramifiedPrimeSet Q,
            (1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s)))) *
              primitiveSymmetricLFunction f 1 s ^ 2) ∧
      firstRankinPoleCancellation f (((1 - (k : ℝ)) / 2 : ℝ) : ℂ) = 0 :=
  ⟨firstRankinPoleCancellation_differentiable f (by omega),
    fun _ hs => firstRankinPoleCancellation_eq_product f (by omega) hz hs,
    firstRankinPoleCancellation_trivial_zero_of_zero_at_one f hk hz⟩

end


section
open scoped ComplexOrder Topology

/-- Nonnegative coefficients of the literal finite geometric products of the actual augmented tensor roots. -/
theorem primitive_augmented_formal_coefficient_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (r : ℕ) :
    0 ≤ PowerSeries.coeff r (∏ i : Fin 3 × Fin 3,
      PowerSeries.mk (fun n : ℕ =>
        (primitiveAugmentedRoots f p i.1 * primitiveAugmentedRoots f p i.2) ^ n)) :=
  primitiveAugmentedLocalCoeff_nonneg f p r

/-- Actual factorization-assembled nonnegative coefficients identify the genuine mixed Rankin L-series, including the exact finite bad correction. -/
theorem primitive_augmented_dirichlet_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    let a : ℕ → ℂ := fun n => if n = 0 then 0 else
      n.factorization.prod (primitiveAugmentedNatLocalCoeff f)
    (∀ n, 0 ≤ a n) ∧ a 1 = 1 ∧
      (∀ s : ℂ, 7 < s.re → LSeries a s =
        DirichletCharacter.LFunctionTrivChar Q s * rankinConvolutionGlobalContinuation f.toCuspForm s *
          (∏ p ∈ ramifiedPrimeSet Q,
            (1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s)))) *
              primitiveSymmetricLFunction f 1 s ^ 2) :=
  ⟨primitiveAugmentedCoefficient_nonneg f, primitiveAugmentedCoefficient_one f,
    fun _ hs => primitiveAugmentedCoefficient_LSeries f hk hs⟩

/-- The explicit original cusp function times its finite correction is entire and nonzero on every point of Re(s)≥1, and matches the literal infinite first symmetric Euler product. -/
theorem primitive_first_full_nonvanishing_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    let F : ℂ → ℂ := fun s => normalizedCuspLFunction f.toCuspForm s *
      ∏ p ∈ ramifiedPrimeSet Q, primitiveEulerDenominator f p s
    Differentiable ℂ F ∧ (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (fun s => (∏' v : Nat.Primes × Fin 2,
        (1 - primitiveSymmetricSpectralRoots f 1 v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹)
        {s | 1 < s.re} :=
  ⟨primitiveFirstContinuation_differentiable f (by omega),
    fun _ hs => primitiveFirstContinuation_ne_zero f hk hs,
    fun _ hs => primitiveFirstContinuation_eq_symmetric f (by omega) hs⟩

/-- The genuine empirical Sato–Tate reduction consumes actual good-prime purity and literal symmetric Euler continuations only from order three onward. -/
theorem primitive_sato_tate_higher_continuation_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (hcontinuation : ∀ r : ℕ, 3 ≤ r → ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (fun s => (∏' v : Nat.Primes × Fin (r + 1),
        (1 - primitiveSymmetricSpectralRoots f r v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹)
        {s | 1 < s.re}) :
    Filter.Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      Filter.atTop (𝓝 satoTateProbability) :=
  primitive_satoTate_of_higher_symmetric_L_continuation f hk hbound hcontinuation

end


section
open scoped ComplexOrder

/-- Literal nonnegative Dirichlet coefficients converge in every half-plane of genuine holomorphy. -/
theorem nonnegative_dirichlet_half_plane_source {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    {F : ℂ → ℂ} {σ₀ A : ℝ} (hF : DifferentiableOn ℂ F {s : ℂ | σ₀ < s.re})
    (hA : LSeries.abscissaOfAbsConv a ≤ A)
    (hmatch : Set.EqOn F (fun s => ∑' n : ℕ, if n = 0 then 0 else a n / (n : ℂ) ^ s)
      {s : ℂ | A < s.re}) :
    LSeries.abscissaOfAbsConv a ≤ σ₀ :=
  positive_dirichlet_abscissa_le_of_holomorphic ha hF hA hmatch

/-- The actual determinant-one roots satisfy the complete finite tensor Euler identity at every order. -/
theorem primitive_tensor_clebsch_gordan_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p r : ℕ) (z : ℂ) :
    (∏ i ∈ Finset.range (r + 1), ∏ j ∈ Finset.range (r + 1),
      (1 - (primitiveSatakePlus f p ^ i * primitiveSatakeMinus f p ^ (r - i)) *
        (primitiveSatakePlus f p ^ j * primitiveSatakeMinus f p ^ (r - j)) * z)) =
    ∏ t ∈ Finset.range (r + 1), ∏ i ∈ Finset.range (2 * t + 1),
      (1 - primitiveSatakePlus f p ^ i * primitiveSatakeMinus f p ^ (2 * t - i) * z) :=
  satake_tensor_product_decomposition (primitiveSatake_trace_det f p).2 (fun w => 1 - w * z) r

/-- Nonnegative coefficients of the actual higher tensor Euler series identify the genuine product of even powers. -/
theorem primitive_higher_tensor_dirichlet_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) :
    let a : ℕ → ℂ := fun n => if n = 0 then 0 else
      n.factorization.prod (spectralNatLocalCoeff (primitiveHigherTensorRoots f r))
    (∀ n, 0 ≤ a n) ∧ (∀ s : ℂ, ((2 * r + (r + 1) ^ 2 + 1 : ℕ) : ℝ) + 1 < s.re →
      LSeries a s = ∏ t ∈ Finset.range (r + 1),
        (∏' v : Nat.Primes × Fin (2 * t + 1),
          (1 - primitiveSymmetricSpectralRoots f (2 * t) v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹) :=
  ⟨primitiveHigherTensorCoefficient_nonneg f r,
    fun _ hs => primitiveHigherTensorCoefficient_LSeries f hk r hs⟩

/-- Convergence of literal geometric-product coefficients bounds every original spectral root. -/
theorem finite_euler_convergence_root_source {ι : Type*} (s : Finset ι) (w : ι → ℂ) (z : ℂ)
    (hs : Summable (fun n : ℕ => PowerSeries.coeff n
      (∏ i ∈ s, PowerSeries.mk (fun m : ℕ => w i ^ m)) * z ^ n))
    {i : ι} (hi : i ∈ s) : ‖w i * z‖ < 1 :=
  spectral_root_norm_lt_one_of_summable s w z hs hi

/-- The genuine good-prime Deligne bound follows from higher holomorphy, without assuming a local bound or near-boundary Euler matching. -/
theorem primitive_purity_from_higher_holomorphy_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (hcontinuation : ∀ r : ℕ, 3 ≤ r → ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s | 1 < s.re} ∧
      Set.EqOn F (fun s => (∏' v : Nat.Primes × Fin (r + 1),
        (1 - primitiveSymmetricSpectralRoots f r v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹)
        {s | (r : ℝ) + 1 < s.re})
    {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) :
    ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2 :=
  primitive_prime_bound_of_higher_symmetric_holomorphy f hk hcontinuation hp hpQ

/-- Actual weak Sato–Tate follows from literal higher Euler continuations alone; the theorem proves local purity internally. -/
theorem primitive_sato_tate_higher_continuation_alone_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (hcontinuation : ∀ r : ℕ, 3 ≤ r → ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (fun s => (∏' v : Nat.Primes × Fin (r + 1),
        (1 - primitiveSymmetricSpectralRoots f r v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹)
        {s | (r : ℝ) + 1 < s.re}) :
    Filter.Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      Filter.atTop (𝓝 satoTateProbability) :=
  primitive_satoTate_of_higher_continuation_alone f hk hcontinuation

end


section
open scoped ComplexOrder

/-- Actual augmented tensor coefficients remain nonnegative and identify the literal higher Euler product. -/
theorem primitive_higher_augmented_series_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) :
    let a : ℕ → ℂ := fun n => if n = 0 then 0 else
      n.factorization.prod (spectralNatLocalCoeff (primitiveHigherAugmentedTensorRoots f r))
    (∀ n, 0 ≤ a n) ∧ a 1 = 1 ∧ (∀ s : ℂ,
      ((2 * r + (r + 2) ^ 2 + 1 : ℕ) : ℝ) + 1 < s.re →
      LSeries a s = DirichletCharacter.LFunctionTrivChar Q s *
        (∏ t ∈ Finset.range (r + 1), primitiveSymmetricLFunction f (2 * t) s) *
          primitiveSymmetricLFunction f r s ^ 2) :=
  ⟨primitiveHigherAugmentedCoefficient_nonneg f r, primitiveHigherAugmentedCoefficient_one f r,
    fun _ hs => primitiveHigherAugmentedCoefficient_LSeries f hk r hs⟩

/-- The literal divided-difference product is entire and has the actual principal trivial zero. -/
theorem higher_actual_pole_cancellation_source (Q : ℕ) [NeZero Q]
    (H : ℕ → ℂ → ℂ) (hH : ∀ n, 0 < n → Differentiable ℂ (H n))
    {r : ℕ} (hr : 0 < r) :
    let G : ℂ → ℂ := fun s => DirichletCharacter.LFunctionTrivChar₁ Q s ^ 2 *
      (dslope (H r) 1 s) ^ 2 * ∏ t ∈ Finset.range r, H (2 * (t + 1)) s
    Differentiable ℂ G ∧ G (-2) = 0 :=
  ⟨higherSymmetricPoleCancellation_differentiable Q H hH hr,
    higherSymmetricPoleCancellation_neg_two Q H r⟩

/-- Entire continuations matched to the original infinite Euler products imply all actual boundary nonvanishing. -/
theorem primitive_higher_entire_nonvanishing_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (H : ℕ → ℂ → ℂ)
    (hH : ∀ n, 0 < n → Differentiable ℂ (H n))
    (hmatch : ∀ n, 0 < n → Set.EqOn (H n)
      (fun s => (∏' v : Nat.Primes × Fin (n + 1),
        (1 - primitiveSymmetricSpectralRoots f n v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹)
      {s | (n : ℝ) + 1 < s.re}) {r : ℕ} (hr : 0 < r) {s : ℂ} (hs : 1 ≤ s.re) : H r s ≠ 0 :=
  primitive_symmetric_nonvanishing_of_entire_continuation f hk H hH hmatch hr hs

/-- The actual weak prime empirical law follows from entire symmetric continuation, with no independent purity or nonvanishing premise. -/
theorem primitive_sato_tate_entire_continuation_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (H : ℕ → ℂ → ℂ)
    (hH : ∀ n, 0 < n → Differentiable ℂ (H n))
    (hmatch : ∀ n, 0 < n → Set.EqOn (H n)
      (fun s => (∏' v : Nat.Primes × Fin (n + 1),
        (1 - primitiveSymmetricSpectralRoots f n v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))⁻¹)
      {s | (n : ℝ) + 1 < s.re}) :
    Filter.Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      Filter.atTop (𝓝 satoTateProbability) :=
  primitive_satoTate_of_entire_symmetric_continuation f hk H hH hmatch

end


open scoped MatrixGroups ModularForm in
theorem real_group_original_pairing_source (k : ℤ)
    (f f' : UpperHalfPlane → ℂ) (g : SL(2, ℝ)) :
    starRingEnd ℂ ((f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)) UpperHalfPlane.I) *
      ((f' ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)) UpperHalfPlane.I) =
      starRingEnd ℂ (f (g • UpperHalfPlane.I)) * f' (g • UpperHalfPlane.I) *
        ((g • UpperHalfPlane.I).im : ℂ) ^ k := by
  exact realWeightLift_pairing k f f' g

open scoped MatrixGroups in
theorem real_group_compact_orbit_source (k : ℤ)
    (f : UpperHalfPlane → ℂ) (hf : f ≠ 0) :
    IsCompact (realCompactSubgroup : Set SL(2, ℝ)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range (fun h : realCompactSubgroup =>
        TannakaDuality.FiniteGroup.rightRegular (k := ℂ) h.val (realWeightLift k f)))) = 1 :=
  ⟨realCompactSubgroup_isCompact, realWeightLift_compact_finrank k hf⟩

open scoped MatrixGroups CongruenceSubgroup in
theorem real_group_whittaker_normalization_source {Q : ℕ} {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n) :
    (∫ x in (0 : ℝ)..1, fourier (-(n : ℤ)) (x : UnitAddCircle) *
      realWeightLift k f
        (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : UpperHalfPlane).toSL2R) =
      normalizedCuspCoefficients f n * (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
        (((((n : ℝ) * y) ^ ((k : ℝ) / 2) : ℝ) : ℂ) *
          (Real.exp (-2 * Real.pi * ((n : ℝ) * y)) : ℂ)) :=
  realWhittakerCoefficient_normalized f hy hn

open scoped MatrixGroups CongruenceSubgroup in
theorem real_group_cuspidal_frequencies_source {Q : ℕ} {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {y : ℝ} (hy : 0 < y) {n : ℤ} (hn : n ≤ 0) :
    (∫ x in (0 : ℝ)..1, fourier (-n) (x : UnitAddCircle) *
      realWeightLift k f
        (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : UpperHalfPlane).toSL2R) = 0 := by
  rcases lt_or_eq_of_le hn with h | h
  · exact realWhittakerCoefficient_neg f hy h
  · subst n
    exact realWhittakerCoefficient_zero f hy

open scoped MatrixGroups in
theorem real_group_primitive_hecke_source {Q p : ℕ} [NeZero Q] [NeZero p] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hp : Nat.Prime p) (g : SL(2, ℝ)) :
    (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      ((∑ b ∈ Finset.range p, realWeightLift k f.toCuspForm
        (realAffineMatrix ((b : ℝ) / p)
          (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_neZero p))) * g)) +
        if Nat.Coprime p Q then realWeightLift k f.toCuspForm
          (realAffineMatrix 0 (Nat.cast_pos.mpr (Nat.pos_of_neZero p)) * g) else 0) =
      normalizedCuspCoefficients f.toCuspForm p * realWeightLift k f.toCuspForm g :=
  primitive_realPrimeHecke_eigenvalue f hp g

open scoped MatrixGroups in
theorem real_group_iwasawa_source (k : ℤ) (f : UpperHalfPlane → ℂ) :
    Function.Bijective (fun g : SL(2, ℝ) =>
      (g • UpperHalfPlane.I, realIwasawaCompact g)) ∧
    ∀ g : SL(2, ℝ), realWeightLift k f g =
      f (g • UpperHalfPlane.I) * ((Real.sqrt (g • UpperHalfPlane.I).im : ℝ) : ℂ) ^ k *
        (realCompactWeight k (realIwasawaCompact g) : ℂ) :=
  ⟨realIwasawaHomeomorph.bijective, realWeightLift_iwasawa k f⟩


open scoped MatrixGroups in
theorem real_group_haar_source :
    (Measure.map realIwasawaHomeomorph.symm
      ((volume : Measure UpperHalfPlane).prod realCompactHaar)).IsHaarMeasure ∧
    ∀ g : SL(2, ℝ),
      MeasurePreserving (fun h : SL(2, ℝ) => g * h) realGroupMeasure realGroupMeasure ∧
      MeasurePreserving (fun h : SL(2, ℝ) => h * g) realGroupMeasure realGroupMeasure :=
  ⟨realGroupMeasure_isHaarMeasure,
    fun g => ⟨realGroupMeasure_left_invariant g, realGroupMeasure_right_invariant g⟩⟩

open scoped MatrixGroups ModularForm CongruenceSubgroup in
theorem real_group_petersson_integral_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f f' : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    cuspPetersson f f' = ∫ g : SL(2, ℝ) in {g | g • UpperHalfPlane.I ∈ gamma0FundamentalDomain Q},
      starRingEnd ℂ ((⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)) UpperHalfPlane.I) *
        ((⇑f' ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)) UpperHalfPlane.I) ∂realGroupMeasure :=
  cuspPetersson_eq_realGroup_integral f f'

open scoped MatrixGroups CongruenceSubgroup in
theorem real_group_generated_hecke_source {Q p : ℕ} [NeZero Q] [NeZero p] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hp : Nat.Prime p) {v : SL(2, ℝ) → ℂ}
    (hv : v ∈ Submodule.span ℂ (Set.range (fun h : SL(2, ℝ) =>
      fun g : SL(2, ℝ) => realWeightLift k f.toCuspForm (g * h)))) :
    (∀ γ : SL(2, ℝ), Matrix.SpecialLinearGroup.mapGL ℝ γ ∈
      (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) →
        ∀ g : SL(2, ℝ), v (γ * g) = v g) ∧
    ∀ g : SL(2, ℝ), realPrimeHecke Q p v g = normalizedCuspCoefficients f.toCuspForm p * v g := by
  refine ⟨fun γ hγ g => realLiftCyclic_left_invariant f.toCuspForm hv γ hγ g, fun g => ?_⟩
  exact congrFun (primitive_realPrimeHecke_cyclic_eigenvalue f hp hv) g

open scoped MatrixGroups CongruenceSubgroup in
theorem real_group_generated_L2_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {v : SL(2, ℝ) → ℂ}
    (hv : v ∈ Submodule.span ℂ (Set.range (fun h : SL(2, ℝ) =>
      fun g : SL(2, ℝ) => realWeightLift k f (g * h)))) :
    Continuous v ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ g : SL(2, ℝ), ‖v g‖ ≤ C) ∧
      MemLp v 2 (realGroupMeasure.restrict
        {g : SL(2, ℝ) | g • UpperHalfPlane.I ∈ gamma0FundamentalDomain Q}) :=
  ⟨realLiftCyclic_continuous f hv, realLiftCyclic_bounded f hv, realLiftCyclic_memLp_two f hv⟩


open scoped MatrixGroups in
theorem real_projective_haar_domain_source (Q : ℕ) [NeZero Q] :
    (Measure.map (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) realGroupMeasure).IsHaarMeasure ∧
    IsFundamentalDomain (projectiveGamma0 Q)
      {q : PSL(2, ℝ) | realProjectiveOrbit q ∈ gamma0FundamentalDomain Q}
      (Measure.map (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) realGroupMeasure) ∧
    realProjectiveMeasure {q | realProjectiveOrbit q ∈ gamma0FundamentalDomain Q} =
      volume (gamma0FundamentalDomain Q) :=
  ⟨realProjectiveMeasure_isHaarMeasure, realProjectiveGamma0Domain_isFundamental Q,
    realProjectiveGamma0Domain_volume Q⟩

open scoped MatrixGroups CongruenceSubgroup in
theorem real_projective_cyclic_L2_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : (realLiftCyclicRepresentation k f).toSubmodule) :
    (∀ g : SL(2, ℝ), realProjectiveCyclicVector f v (QuotientGroup.mk g) = v.val g) ∧
    MemLp (realProjectiveCyclicVector f v) 2
      (realProjectiveMeasure.restrict {q | realProjectiveOrbit q ∈ gamma0FundamentalDomain Q}) ∧
    Function.Injective (realProjectiveCyclicToL2 f) :=
  ⟨realProjectiveCyclicVector_mk f v, realProjectiveCyclicVector_memLp_two f v,
    realProjectiveCyclicToL2_injective f⟩

open scoped MatrixGroups CongruenceSubgroup ModularForm in
theorem real_projective_petersson_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f f' : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    (∀ g : SL(2, ℝ), realProjectiveCuspLift f (QuotientGroup.mk g) =
      (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)) UpperHalfPlane.I) ∧
    cuspPetersson f f' = ∫ q : PSL(2, ℝ) in
      {q | realProjectiveOrbit q ∈ gamma0FundamentalDomain Q},
      starRingEnd ℂ (realProjectiveCuspLift f q) * realProjectiveCuspLift f' q
        ∂realProjectiveMeasure :=
  ⟨fun _ => rfl, cuspPetersson_eq_projectiveGroup_integral f f'⟩

open scoped MatrixGroups CongruenceSubgroup in
theorem real_projective_unitary_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (a : PSL(2, ℝ)) (v w : (realLiftCyclicRepresentation k f).toSubmodule) :
    (∀ q : PSL(2, ℝ), realProjectiveCyclicVector f
      (realProjectiveCyclicRepresentation f a v) q = realProjectiveCyclicVector f v (q * a)) ∧
    inner ℂ (realProjectiveCyclicToL2 f (realProjectiveCyclicRepresentation f a v))
      (realProjectiveCyclicToL2 f (realProjectiveCyclicRepresentation f a w)) =
        inner ℂ (realProjectiveCyclicToL2 f v) (realProjectiveCyclicToL2 f w) :=
  ⟨fun q => realProjectiveCyclicRepresentation_apply f a q v,
    realProjectiveCyclicRepresentation_inner f a v w⟩


open scoped MatrixGroups CongruenceSubgroup in
theorem real_projective_hilbert_embedding_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    Function.Injective (realProjectiveHilbertEmbedding f) ∧
    DenseRange (realProjectiveHilbertEmbedding f) ∧
    ∀ (a : PSL(2, ℝ)) (v : (realLiftCyclicRepresentation k f).toSubmodule),
      realProjectiveHilbertRepresentation f a (realProjectiveHilbertEmbedding f v) =
        realProjectiveHilbertEmbedding f (realProjectiveCyclicRepresentation f a v) :=
  ⟨realProjectiveHilbertEmbedding_injective f, realProjectiveHilbertEmbedding_dense f,
    realProjectiveHilbertEmbedding_intertwines f⟩

open scoped MatrixGroups CongruenceSubgroup in
theorem real_projective_hilbert_unitary_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    (∀ v : RealProjectiveHilbert f,
      Continuous (fun a : PSL(2, ℝ) => realProjectiveHilbertRepresentation f a v)) ∧
    ∀ (a : PSL(2, ℝ)) (v w : RealProjectiveHilbert f),
      inner ℂ (realProjectiveHilbertRepresentation f a v)
        (realProjectiveHilbertRepresentation f a w) = inner ℂ v w :=
  ⟨realProjectiveHilbertRepresentation_stronglyContinuous f,
    realProjectiveHilbertRepresentation_inner f⟩


open scoped MatrixGroups CongruenceSubgroup in
theorem original_completed_quotient_L2_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    (∀ v : RealProjectiveHilbert f, ‖realProjectiveHilbertToL2 f v‖ = ‖v‖) ∧
    Set.range (realProjectiveHilbertToL2 f) = closure (Set.range (realProjectiveCyclicToL2 f)) ∧
    ∀ v : (realLiftCyclicRepresentation k f).toSubmodule,
      realProjectiveHilbertToL2 f (realProjectiveHilbertEmbedding f v) = realProjectiveCyclicToL2 f v :=
  ⟨realProjectiveHilbertToL2_norm f, realProjectiveHilbertToL2_range f,
    realProjectiveHilbertToL2_embedding f⟩

theorem original_cusp_period_average_source {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (t : ℝ) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      f ⟨((h * x + t : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩) = 0 :=
  cusp_period_horizontal_shift_integral_zero f hh hΓ t hy

open scoped MatrixGroups CongruenceSubgroup in
theorem original_cyclic_integral_cusp_average_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : (realLiftCyclicRepresentation k f).toSubmodule) :
    ∀ (σ : SL(2, ℤ)) (g : SL(2, ℝ)),
      (∫ x in (0 : ℝ)..1, v.val (integralToRealSL σ * realUpperUnipotent ((Q : ℝ) * x) * g)) = 0 :=
  realLiftCyclic_integral_cusp_period_zero f v.property

open scoped MatrixGroups CongruenceSubgroup in
theorem original_completed_cusp_generator_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hf : f ≠ 0) :
    realProjectiveHilbertGenerator f ≠ 0 ∧
    inner ℂ (realProjectiveHilbertGenerator f) (realProjectiveHilbertGenerator f) = cuspPetersson f f ∧
    (∀ a : realCompactSubgroup,
      realProjectiveHilbertRepresentation f (QuotientGroup.mk a.val) (realProjectiveHilbertGenerator f) =
        (realCompactWeight k a : ℂ) • realProjectiveHilbertGenerator f) ∧
    closure ((Submodule.span ℂ (Set.range (fun a : PSL(2, ℝ) =>
      realProjectiveHilbertRepresentation f a (realProjectiveHilbertGenerator f)))) :
        Set (RealProjectiveHilbert f)) = Set.univ :=
  ⟨realProjectiveHilbertGenerator_ne_zero f hf, realProjectiveHilbertGenerator_inner f,
    realProjectiveHilbertGenerator_compact_weight f, realProjectiveHilbertGenerator_cyclic f⟩


open scoped MatrixGroups ModularForm in
theorem positive_real_unitary_normalization_source (k : ℤ) (f : UpperHalfPlane → ℂ) (g : GL(2, ℝ)⁺) :
    realPositiveUnitaryLift k f g =
      (realPositiveDetRoot g : ℂ) ^ k * f (g.val • UpperHalfPlane.I) *
        UpperHalfPlane.denom g.val UpperHalfPlane.I ^ (-k) ∧
    realPositiveUnitaryLift k f g =
      (realPositiveDetRoot g : ℂ) ^ (2 - k) * (f ∣[k] g.val) UpperHalfPlane.I ∧
    Function.Injective (realPositiveUnitaryLift k) :=
  ⟨realPositiveUnitaryLift_apply k f g, realPositiveUnitaryLift_slash_correction k f g,
    realPositiveUnitaryLift_injective k⟩

open scoped MatrixGroups CongruenceSubgroup in
theorem original_positive_real_representation_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v : RealProjectiveHilbert f) :
    Continuous (fun g : GL(2, ℝ)⁺ => realPositiveHilbertRepresentation f g v) ∧
    (∀ (r : ℝ) (hr : r ≠ 0), realPositiveHilbertRepresentation f (realPositiveScalar r hr) v = v) ∧
    ∀ g : SL(2, ℝ), realPositiveHilbertRepresentation f (Matrix.SpecialLinearGroup.toGLPos g) v =
      realProjectiveHilbertRepresentation f (QuotientGroup.mk g) v :=
  ⟨realPositiveHilbertRepresentation_stronglyContinuous f v,
    fun r hr => realPositiveHilbertRepresentation_scalar f r hr v,
    fun g => realPositiveHilbertRepresentation_toGLPos f g v⟩

open scoped MatrixGroups in
theorem actual_simultaneous_padic_SL2_source {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp : Function.Injective p)
    (g : ∀ i, SL(2, ℤ_[p i])) (n : ι → ℕ) :
    ∃ γ : SL(2, ℤ), ∀ t : ι, ∀ i j : Fin 2,
      ‖g t i j - ((γ i j : ℤ) : ℤ_[p t])‖ ≤ (p t : ℝ) ^ (-(n t : ℤ)) :=
  integralSL2_finite_padic_approximation p hp g n

open scoped MatrixGroups in
theorem actual_integral_SL2_prime_product_source {ι : Type*}
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp : Function.Injective p) :
    DenseRange (fun γ : SL(2, ℤ) => fun i : ι =>
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℤ_[p i]) γ) :=
  integralSL2_dense_prime_product p hp


open scoped MatrixGroups

/-- The original integer determinant-one group is dense in the canonical compact local product. -/
theorem canonical_integer_matrix_density_source :
    DenseRange (fun γ : SL(2, ℤ) => fun v : IsDedekindDomain.HeightOneSpectrum ℤ =>
      Matrix.SpecialLinearGroup.map (Int.castRingHom (v.adicCompletionIntegers ℚ)) γ) :=
  integralSL2_dense_adic_integer_product

/-- Rational approximation concerns the pinned finite adele ring and its canonical diagonal. -/
theorem actual_rational_adele_density_source :
    DenseRange (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) :=
  rational_dense_finiteAdeles

/-- Actual rational matrices give the exact finite-level adelic factorization. -/
theorem actual_rational_SL2_strong_approximation_source
    (K : Subgroup SL(2, IsDedekindDomain.FiniteAdeleRing ℤ ℚ))
    (hK : IsOpen (K : Set SL(2, IsDedekindDomain.FiniteAdeleRing ℤ ℚ)))
    (g : SL(2, IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) :
    ∃ γ : SL(2, ℚ), ∃ k : K,
      g = Matrix.SpecialLinearGroup.map
        (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) γ * k.val :=
  rationalSL2_finiteAdeles_open_subgroup_factorization K hK g


/-- The rational intersection of the actual adelic level subgroup is precisely the original classical Gamma0. -/
theorem actual_adelic_level_intersection_source (N : ℕ) [NeZero N] (g : SL(2, ℚ)) :
    Matrix.SpecialLinearGroup.map (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) g ∈
      finiteAdeleGamma0 N ↔
    ∃ γ : CongruenceSubgroup.Gamma0 N,
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) γ.val = g :=
  rationalSL2_mem_finiteAdeleGamma0_iff N g

/-- The actual full adelic function recovers its entire original real-group cusp function. -/
theorem actual_adelic_cusp_recovery_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (g : SL(2, ℝ)) :
    canonicalAdelicCuspLift N k f (rationalAdelicSL2RealFiniteEquiv.symm (g, 1)) =
      realWeightLift k f g :=
  canonicalAdelicCuspLift_real_restriction N f g

/-- Both invariances refer to the actual canonical full adele group and its original rational diagonal. -/
theorem actual_adelic_cusp_invariance_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (γ : SL(2, ℚ)) (g : SL(2, NumberField.AdeleRing ℤ ℚ)) (u : finiteAdeleGamma0 N) :
    canonicalAdelicCuspLift N k f
      (Matrix.SpecialLinearGroup.map (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ)) γ * g) =
        canonicalAdelicCuspLift N k f g ∧
    canonicalAdelicCuspLift N k f (g * rationalAdelicSL2RealFiniteEquiv.symm (1, u.val)) =
      canonicalAdelicCuspLift N k f g :=
  ⟨canonicalAdelicCuspLift_rational_invariant N f γ g,
    canonicalAdelicCuspLift_level_invariant N f g u⟩

/-- The canonical full adelic cusp construction is continuous and retains the original cusp form injectively. -/
theorem actual_adelic_cusp_continuity_source (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    Continuous (canonicalAdelicCuspLift N k f) ∧
    Function.Injective (fun h : CuspForm
      ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k =>
        canonicalAdelicCuspLift N k h) :=
  ⟨canonicalAdelicCuspLift_continuous N f, canonicalAdelicCuspLift_injective N k⟩


/-- The determinant normalization uses a proved positive rational factor of the actual finite idele. -/
theorem finite_idele_determinant_factor_source
    (a : (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)ˣ) :
    ∃ q : ℚ, 0 < q ∧ ∃ u : finiteAdeleIntegerSubringˣ,
      (a : IsDedekindDomain.FiniteAdeleRing ℤ ℚ) =
        algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing ℤ ℚ) q * u.val.val :=
  finiteIdele_positive_rational_integral_unit a

/-- The genuine nonzero-level GL2 subgroup is open in the actual canonical finite adelic topology. -/
theorem actual_finite_GL2_level_source (N : ℕ) [NeZero N] :
    IsOpen (finiteAdeleGL2Gamma0 N :
      Set (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ))) :=
  finiteAdeleGL2Gamma0_isOpen N

/-- The actual original finite adelic invertible matrix has the proved positive rational and level factors. -/
theorem positive_rational_GL2_factor_source (N : ℕ) [NeZero N]
    (g : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) :
    ∃ γ : GL(2, ℚ)⁺, ∃ u : finiteAdeleGL2Gamma0 N,
      g = Matrix.GeneralLinearGroup.map
        (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) γ.val * u.val :=
  rationalGL2_finiteAdeles_gamma0_factorization N g

/-- The positive rational intersection is exactly the genuine embedded classical Gamma0 group. -/
theorem actual_positive_GL2_intersection_source (N : ℕ) [NeZero N] (g : GL(2, ℚ)⁺) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) g.val ∈
      finiteAdeleGL2Gamma0 N ↔
    ∃ γ : CongruenceSubgroup.Gamma0 N,
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)
        (Matrix.SpecialLinearGroup.toGL γ.val) = g.val :=
  positiveRationalGL2_mem_finiteAdeleGamma0_iff N g

/-- The actual full adelic function recovers its entire original real-group cusp function. -/
theorem actual_adelic_GL2_cusp_recovery_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (g : GL(2, ℝ)⁺) :
    canonicalAdelicGL2CuspLift N k f (rationalAdelicGL2RealFiniteEquiv.symm (g.val, 1)) =
      realPositiveUnitaryLift k f g :=
  canonicalAdelicGL2CuspLift_real_restriction N f g

/-- Both invariances refer to the actual canonical full adele group and its original rational diagonal. -/
theorem actual_adelic_GL2_cusp_invariance_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing ℤ ℚ)) (u : finiteAdeleGL2Gamma0 N) :
    canonicalAdelicGL2CuspLift N k f
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ)) γ * g) =
        canonicalAdelicGL2CuspLift N k f g ∧
    canonicalAdelicGL2CuspLift N k f (g * rationalAdelicGL2RealFiniteEquiv.symm (1, u.val)) =
      canonicalAdelicGL2CuspLift N k f g :=
  ⟨canonicalAdelicGL2CuspLift_rational_invariant N f γ g,
    canonicalAdelicGL2CuspLift_level_invariant N f g u⟩

/-- The canonical full adelic cusp construction is continuous and retains the original cusp form injectively. -/
theorem actual_adelic_GL2_cusp_continuity_source (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    Continuous (canonicalAdelicGL2CuspLift N k f) ∧
    Function.Injective (fun h : CuspForm
      ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k =>
        canonicalAdelicGL2CuspLift N k h) :=
  ⟨canonicalAdelicGL2CuspLift_continuous N f, canonicalAdelicGL2CuspLift_injective N k⟩


/-- The full general-linear lift extends the original canonical determinant-one cusp function exactly. -/
theorem actual_adelic_GL2_SL2_compatibility_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (g : SL(2, NumberField.AdeleRing ℤ ℚ)) :
    canonicalAdelicGL2CuspLift N k f (Matrix.SpecialLinearGroup.toGL g) =
      canonicalAdelicCuspLift N k f g :=
  canonicalAdelicGL2CuspLift_toGL N f g

/-- The original cusp form has an actual positive zero-average period after every positive rational cusp translate. -/
theorem actual_rational_GL2_cusp_period_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (γ : GL(2, ℚ)⁺) :
    ∃ h : ℝ, 0 < h ∧ ∀ g : GL(2, ℝ)⁺,
      (∫ x in (0 : ℝ)..1, realPositiveUnitaryLift k f
        (rationalPositiveGL2ToReal γ * Matrix.SpecialLinearGroup.toGLPos
          (realUpperUnipotent (h * x)) * g)) = 0 :=
  rationalPositiveGL2_unipotent_period_zero f γ

/-- The actual positive-real adelic lift has zero real unipotent averages at every original finite point. -/
theorem actual_finite_adelic_GL2_cusp_period_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (a : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) :
    ∃ h : ℝ, 0 < h ∧ ∀ g : GL(2, ℝ)⁺,
      (∫ x in (0 : ℝ)..1, positiveAdelicGL2CuspLift N k f
        (Matrix.SpecialLinearGroup.toGLPos (realUpperUnipotent (h * x)) * g) a) = 0 :=
  positiveAdelicGL2CuspLift_unipotent_period_zero N f a

/-- The original additive quotient is compact with discrete principal rationals and a genuinely dense real orbit. -/
theorem actual_additive_adele_quotient_source :
    CompactSpace RationalAdelicAdditiveQuotient ∧
    DiscreteTopology (NumberField.AdeleRing.principalSubgroup ℤ ℚ) ∧
    DenseRange rationalAdelicRealQuotientMap :=
  ⟨rationalAdelicAdditiveQuotient_compactSpace, rationalAdelePrincipal_discreteTopology,
    rationalAdelicRealQuotientMap_dense⟩

/-- The actual full additive quotient has a normalized Haar measure preserved by every genuine translation. -/
theorem actual_additive_adele_Haar_source (a : RationalAdelicAdditiveQuotient) :
    rationalAdelicAdditiveHaar Set.univ = 1 ∧
    MeasureTheory.Measure.map (fun x => a + x) rationalAdelicAdditiveHaar = rationalAdelicAdditiveHaar :=
  ⟨rationalAdelicAdditiveHaar_univ, rationalAdelicAdditiveHaar_translate a⟩

/-- The original actual unipotent function descends continuously to the genuine additive quotient, with its exact representative formula. -/
theorem actual_adelic_unipotent_quotient_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing ℤ ℚ))
    (x : NumberField.AdeleRing ℤ ℚ) :
    Continuous (adelicUnipotentQuotientFunction N f g) ∧
    adelicUnipotentQuotientFunction N f g (QuotientAddGroup.mk x) =
      canonicalAdelicGL2CuspLift N k f (Matrix.GeneralLinearGroup.upperRightHom x * g) :=
  ⟨adelicUnipotentQuotientFunction_continuous N f g,
    adelicUnipotentQuotientFunction_mk N f g x⟩

/-- The original classical cusp form has genuine zero unipotent Haar integral at every full canonical adelic GL2 point. -/
theorem actual_adelic_unipotent_cuspidality_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing ℤ ℚ)) :
    (∫ z : RationalAdelicAdditiveQuotient,
      adelicUnipotentQuotientFunction N f g z ∂rationalAdelicAdditiveHaar) = 0 :=
  canonicalAdelicGL2CuspLift_unipotent_cuspidal N f g

/-- The original canonical full adelic cusp function has its actual rational invariance and genuine trivial full idele scalar character. -/
theorem actual_adelic_central_character_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (u : (NumberField.AdeleRing ℤ ℚ)ˣ)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing ℤ ℚ)) :
    canonicalAdelicGL2CuspLift N k f
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ)) γ * g) =
        canonicalAdelicGL2CuspLift N k f g ∧
    canonicalAdelicGL2CuspLift N k f (Matrix.GeneralLinearGroup.scalar (Fin 2) u * g) =
      canonicalAdelicGL2CuspLift N k f g :=
  ⟨canonicalAdelicGL2CuspLift_rational_invariant N f γ g,
    canonicalAdelicGL2CuspLift_scalar_mul N f u g⟩

/-- The genuine original finite level group is compact and open in its actual locally compact general-linear group. -/
theorem actual_finite_adelic_compact_level_source (N : ℕ) [NeZero N] :
    LocallyCompactSpace
      (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) ∧
    IsCompact (finiteAdeleGL2Gamma0 N :
      Set (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ))) ∧
    IsOpen (finiteAdeleGL2Gamma0 N :
      Set (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ))) :=
  ⟨rationalFiniteAdelicGL2LocallyCompactSpace, finiteAdeleGL2Gamma0_compact_open N⟩

/-- Every vector of the actual original full adelic cyclic representation retains continuity, rational invariance and the trivial scalar character. -/
theorem actual_adelic_cyclic_invariance_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (u : (NumberField.AdeleRing ℤ ℚ)ˣ)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing ℤ ℚ)) :
    Continuous v.val ∧
    v.val (Matrix.GeneralLinearGroup.map (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ)) γ * g) = v.val g ∧
    v.val (Matrix.GeneralLinearGroup.scalar (Fin 2) u * g) = v.val g :=
  ⟨adelicLiftCyclic_continuous N f v.property,
    adelicLiftCyclic_rational_invariant N f v.property γ g,
    adelicLiftCyclic_scalar_invariant N f v.property u g⟩

/-- Every actual original adelic cyclic vector has zero genuine quotient Haar periods and a proved compact open finite stabilizer. -/
theorem actual_adelic_cyclic_cuspidal_smooth_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing ℤ ℚ)) :
    (∃ φ : C(RationalAdelicAdditiveQuotient, ℂ),
      (∀ x : NumberField.AdeleRing ℤ ℚ, φ (QuotientAddGroup.mk x) =
        v.val (Matrix.GeneralLinearGroup.upperRightHom x * g)) ∧
      (∫ z, φ z ∂rationalAdelicAdditiveHaar) = 0) ∧
    (∃ K : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)),
      IsCompact (K : Set (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ))) ∧
      IsOpen (K : Set (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ))) ∧
      ∀ h : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing ℤ ℚ), ∀ a ∈ K,
        v.val (h * rationalAdelicFiniteGL2Embedding a) = v.val h) :=
  ⟨adelicLiftCyclic_unipotent_cuspidal N f v.property g,
    adelicLiftCyclic_finite_smooth N f v.property⟩

/-- The actual canonical finite projective Haar measure has the original full-level normalization and genuine right invariance. -/
theorem actual_finite_projective_haar_source (g : RationalFiniteProjectiveGL2) :
    finiteProjectiveGL2Measure (finiteProjectiveGL2Level 1) = 1 ∧
    MeasurePreserving (fun h : RationalFiniteProjectiveGL2 => h * g)
      finiteProjectiveGL2Measure finiteProjectiveGL2Measure :=
  ⟨finiteProjectiveGL2Measure_level_one, finiteProjectiveGL2Measure_right_invariant g⟩

/-- The original product projective Haar measure is genuinely right invariant and its literal base region has exactly the existing real volume. -/
theorem actual_adelic_projective_haar_source (g : AdelicProjectiveGroup) :
    MeasurePreserving (fun h : AdelicProjectiveGroup => h * g)
      adelicProjectiveMeasure adelicProjectiveMeasure ∧
    adelicProjectiveMeasure adelicProjectiveBaseRegion =
      realProjectiveMeasure (realProjectiveGamma0Domain 1) ∧
    adelicProjectiveMeasure adelicProjectiveBaseRegion < ⊤ :=
  ⟨adelicProjectiveMeasure_right_invariant g,
    adelicProjectiveBaseRegion_volume, adelicProjectiveBaseRegion_volume_lt_top⟩

/-- The actual original cyclic vector has a continuous projective image with exactly its original representative values. -/
theorem actual_adelic_cyclic_projective_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (r : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (a : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) :
    Continuous (adelicCyclicProjectiveFunction N f v) ∧
    adelicCyclicProjectiveLinear N f v (QuotientGroup.mk r, Matrix.ProjGenLinGroup.mk a) =
      v.val (rationalAdelicGL2RealFiniteEquiv.symm (Matrix.SpecialLinearGroup.toGL r, a)) :=
  ⟨adelicCyclicProjectiveFunction_continuous N f v, rfl⟩

/-- The actual projective linear map is faithful and recovers every original positive-real adelic value. -/
theorem actual_adelic_cyclic_projective_recovery_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (r : Matrix.GLPos (Fin 2) ℝ)
    (a : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) :
    Function.Injective (adelicCyclicProjectiveLinear N f) ∧
    adelicCyclicProjectiveFunction N f v
      (QuotientGroup.mk (realPositiveNormalize r), Matrix.ProjGenLinGroup.mk a) =
      v.val (rationalAdelicGL2RealFiniteEquiv.symm (r.val, a)) :=
  ⟨adelicCyclicProjectiveLinear_injective N f,
    adelicCyclicProjectiveFunction_recover_positive N f v r a⟩

/-- The exact original generator of the actual adelic representation keeps the original real cusp-form lift in projective coordinates. -/
theorem actual_adelic_projective_generator_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (r : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    adelicCyclicProjectiveLinear N f (adelicCyclicGenerator N f) (QuotientGroup.mk r, 1) =
      realWeightLift k f r :=
  adelicCyclicProjectiveGenerator_real N f r

/-- Every actual original projective cyclic vector is invariant under the genuine rational arithmetic image. -/
theorem actual_adelic_projective_arithmetic_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (γ : adelicProjectiveArithmetic) (p : AdelicProjectiveGroup) :
    adelicCyclicProjectiveFunction N f v (γ.val * p) = adelicCyclicProjectiveFunction N f v p :=
  adelicCyclicProjectiveFunction_arithmetic_invariant N f v γ p

/-- The genuine arithmetic level intersection uses original integral Gamma0 matrices and a faithful diagonal embedding. -/
theorem actual_adelic_projective_level_intersection_source (N : ℕ) [NeZero N]
    (γ : adelicProjectiveArithmetic) :
    Function.Injective integralToAdelicProjective ∧
    (γ.val.2 ∈ finiteProjectiveGL2Level N ↔
      ∃ σ : CongruenceSubgroup.Gamma0 N,
        integralToAdelicProjective (QuotientGroup.mk σ.val) = γ.val) :=
  ⟨integralToAdelicProjective_injective, adelicProjectiveArithmetic_level_iff N γ⟩

/-- The literal original real domain times genuine finite level is an actual finite-volume arithmetic fundamental domain. -/
theorem actual_adelic_projective_fundamental_domain_source (N : ℕ) [NeZero N] :
    MeasureTheory.IsFundamentalDomain adelicProjectiveArithmetic (adelicProjectiveGamma0Domain N)
      adelicProjectiveMeasure ∧
    adelicProjectiveMeasure (adelicProjectiveGamma0Domain N) < ⊤ ∧
    0 < finiteProjectiveGL2Measure (finiteProjectiveGL2Level N) :=
  ⟨adelicProjectiveGamma0Domain_isFundamental N, adelicProjectiveGamma0Domain_volume_lt_top N,
    (finiteProjectiveGL2Level_volume N).1⟩

/-- Actual original full adelic cyclic vectors are faithfully realized in genuine L2, with precisely the original integral pairing. -/
theorem actual_adelic_projective_l2_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v w : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    Function.Injective (adelicProjectiveCyclicToL2 N f) ∧
    MeasureTheory.MemLp (adelicCyclicProjectiveFunction N f v) 2
      (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) ∧
    inner ℂ (adelicProjectiveCyclicToL2 N f v) (adelicProjectiveCyclicToL2 N f w) =
      adelicProjectiveCyclicPairing N f v w :=
  ⟨adelicProjectiveCyclicToL2_injective N f, adelicCyclicProjectiveFunction_memLp_two N f v,
    adelicProjectiveCyclicToL2_inner N f v w⟩

/-- Actual right projective translation preserves the genuine integral pairing of the original adelic cyclic vectors. -/
theorem actual_adelic_projective_pairing_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v w : (adelicLiftCyclicRepresentation N k f).toSubmodule) (a : AdelicProjectiveGroup) :
    (∫ p in adelicProjectiveGamma0Domain N,
      star (adelicCyclicProjectiveFunction N f v (p * a)) *
        adelicCyclicProjectiveFunction N f w (p * a) ∂adelicProjectiveMeasure) =
      adelicProjectiveCyclicPairing N f v w :=
  adelicProjectiveCyclicPairing_right N f v w a

/-- The original full adelic right reflection descends through the genuine Haar-preserving projective reflection. -/
theorem actual_adelic_reflection_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) (p : AdelicProjectiveGroup) :
    MeasureTheory.MeasurePreserving adelicProjectiveReflection adelicProjectiveMeasure adelicProjectiveMeasure ∧
    adelicCyclicProjectiveFunction N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation canonicalAdelicGL2Reflection v) p =
      adelicCyclicProjectiveFunction N f v (adelicProjectiveReflection p) :=
  ⟨adelicProjectiveReflection_measurePreserving, adelicCyclicProjectiveFunction_reflection_right N f v p⟩

/-- The actual rational reflection preserves the original arithmetic subgroup and transforms the original integration region into another genuine fundamental domain. -/
theorem actual_adelic_reflected_domain_source (N : ℕ) [NeZero N] (γ : adelicProjectiveArithmetic) :
    adelicProjectiveReflection γ.val ∈ adelicProjectiveArithmetic ∧
    MeasureTheory.IsFundamentalDomain adelicProjectiveArithmetic
      (adelicProjectiveReflection '' adelicProjectiveGamma0Domain N) adelicProjectiveMeasure :=
  ⟨adelicProjectiveReflection_mem_arithmetic γ, adelicProjectiveGamma0Domain_reflection N⟩

/-- Every matrix of the original full adelic group preserves the genuine inherited L2 inner product and norm of the actual original cyclic representation. -/
theorem actual_adelic_full_unitary_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v w : (adelicLiftCyclicRepresentation N k f).toSubmodule) (h : RationalAdelicGL2) :
    inner ℂ (adelicProjectiveCyclicToL2 N f ((adelicLiftCyclicRepresentation N k f).toRepresentation h v))
      (adelicProjectiveCyclicToL2 N f ((adelicLiftCyclicRepresentation N k f).toRepresentation h w)) =
      inner ℂ (adelicProjectiveCyclicToL2 N f v) (adelicProjectiveCyclicToL2 N f w) ∧
    ‖adelicProjectiveCyclicToL2 N f ((adelicLiftCyclicRepresentation N k f).toRepresentation h v)‖ =
      ‖adelicProjectiveCyclicToL2 N f v‖ :=
  ⟨adelicLiftCyclic_inner N f v w h, adelicLiftCyclic_norm N f v h⟩

/-- Every original full adelic cyclic orbit is continuous in its actual quotient L2 norm. -/
theorem actual_adelic_strong_continuity_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    Continuous (fun h : RationalAdelicGL2 => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation h v)) :=
  adelicLiftCyclic_stronglyContinuous N f v

/-- The original completed adelic action is strongly continuous and unitary on the genuine Hilbert completion. -/
theorem actual_adelic_hilbert_action_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (a : RationalAdelicGL2) (v w : AdelicCyclicHilbert f) :
    Continuous (fun h : RationalAdelicGL2 => adelicCyclicHilbertRepresentation f h v) ∧
    inner ℂ (adelicCyclicHilbertRepresentation f a v) (adelicCyclicHilbertRepresentation f a w) =
      inner ℂ v w :=
  ⟨adelicCyclicHilbertRepresentation_stronglyContinuous f v, adelicCyclicHilbertRepresentation_inner f a v w⟩

/-- The original adelic cyclic vectors embed faithfully and densely in precisely their original L2 closure. -/
theorem actual_adelic_hilbert_realization_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    Function.Injective (adelicCyclicHilbertEmbedding f) ∧
    DenseRange (adelicCyclicHilbertEmbedding f) ∧
    Set.range (adelicCyclicHilbertToL2 f) = closure (Set.range (adelicProjectiveCyclicToL2 N f)) ∧
    adelicCyclicHilbertToL2 f (adelicCyclicHilbertEmbedding f v) = adelicProjectiveCyclicToL2 N f v :=
  ⟨adelicCyclicHilbertEmbedding_injective f, adelicCyclicHilbertEmbedding_dense f,
    adelicCyclicHilbertToL2_range f, adelicCyclicHilbertToL2_embedding f v⟩

/-- The genuine completed original generator is nonzero, retains its exact Petersson factor and generates a dense actual adelic cyclic span. -/
theorem actual_adelic_hilbert_generator_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) (hf : f ≠ 0) :
    adelicCyclicHilbertGenerator f ≠ 0 ∧
    inner ℂ (adelicCyclicHilbertGenerator f) (adelicCyclicHilbertGenerator f) =
      cuspPetersson f f * (finiteProjectiveGL2Measure (finiteProjectiveGL2Level N)).toReal ∧
    closure ((Submodule.span ℂ (Set.range (fun a : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f a (adelicCyclicHilbertGenerator f)))) :
        Set (AdelicCyclicHilbert f)) = Set.univ :=
  ⟨adelicCyclicHilbertGenerator_ne_zero f hf, adelicCyclicHilbertGenerator_inner f,
    adelicCyclicHilbertGenerator_cyclic f⟩

/-- Actual completed vectors have trivial full scalar action, and the original generator retains its genuine finite level invariance. -/
theorem actual_adelic_hilbert_central_level_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (u : (NumberField.AdeleRing ℤ ℚ)ˣ) (v : AdelicCyclicHilbert f)
    (a : finiteAdeleGL2Gamma0 N) :
    adelicCyclicHilbertRepresentation f (Matrix.GeneralLinearGroup.scalar (Fin 2) u) v = v ∧
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val)
      (adelicCyclicHilbertGenerator f) = adelicCyclicHilbertGenerator f :=
  ⟨adelicCyclicHilbert_scalar_action f u v, adelicCyclicHilbertGenerator_finite_level f a⟩

/-- The actual completed original generator has precisely its original compact character. -/
theorem actual_adelic_hilbert_compact_weight_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (a : realCompactSubgroup) :
    adelicCyclicHilbertRepresentation f (adelicRealCompactEmbedding a) (adelicCyclicHilbertGenerator f) =
      (realCompactWeight k a : ℂ) • adelicCyclicHilbertGenerator f :=
  adelicCyclicHilbertGenerator_compact_weight f a

/-- The original canonical full adelic cusp function has the exact original real lift on every real right orbit. -/
theorem actual_adelic_real_orbit_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (g : RationalAdelicGL2) (h : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding h) =
      realWeightLift k f (canonicalAdelicRealBase N g * h) :=
  canonicalAdelicGL2CuspLift_real_orbit N k f g h

/-- The original algebraic adelic generator satisfies the actual pointwise holomorphic infinitesimal identity at every adelic point. -/
theorem actual_adelic_holomorphic_infinitesimal_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (g : RationalAdelicGL2) :
    deriv (fun t : ℝ => ((adelicLiftCyclicRepresentation N k f).toRepresentation
      (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicGenerator N f)).val g) 0 -
      Complex.I * deriv (fun t : ℝ => ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicGenerator N f)).val g) 0 =
          (k : ℂ) / 2 * (adelicCyclicGenerator N f).val g :=
  adelicCyclicGenerator_holomorphic_infinitesimal N f g

/-- The actual original cusp lift has its genuine mixed compact derivative and second-order right-curve eigenvalue. -/
theorem actual_real_second_order_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    realRightDerivative realUpperUnipotent
      (realRightDerivative realRotationCurve (realWeightLift k f)) g =
        (k : ℂ) * Complex.I * realRightDerivative realUpperUnipotent (realWeightLift k f) g ∧
    realCasimirOperator (realWeightLift k f) g =
      ((k : ℂ) / 2) * (1 - (k : ℂ) / 2) * realWeightLift k f g :=
  ⟨realWeightLift_unipotent_rotation k (ModularFormClass.holo f) g,
    realWeightLift_casimir k (ModularFormClass.holo f) g⟩

/-- The compact curve is a genuine rotation fixing i and its original right derivative has the exact weight and sign. -/
theorem actual_real_compact_derivative_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ) :
    realRotationCurve t • UpperHalfPlane.I = UpperHalfPlane.I ∧
    HasDerivAt (fun u : ℝ => realWeightLift k f (g * realRotationCurve u))
      ((k : ℂ) * Complex.I * realWeightLift k f g) 0 :=
  ⟨realRotationCurve_smul_I t, realWeightLift_right_rotation_hasDerivAt k f g⟩

/-- The literal original adelic cyclic generator has the exact second-order differential eigenvalue at every actual adelic point. -/
theorem actual_adelic_second_order_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (g : RationalAdelicGL2) :
    adelicCasimirOperator (adelicCyclicGenerator N f).val g =
      ((k : ℂ) / 2) * (1 - (k : ℂ) / 2) * (adelicCyclicGenerator N f).val g :=
  adelicCyclicGenerator_casimir N f g

open scoped ModularForm in
/-- All genuine holomorphic jets of every original real slash transform obey one uniform Cauchy bound. -/
theorem actual_original_holomorphic_jets_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ‖iteratedDeriv n (((f : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)) ∘
        UpperHalfPlane.ofComplex) Complex.I‖ ≤ (n.factorial : ℝ) * C / (1 / 2 : ℝ) ^ n :=
  realWeightLift_slash_jets_bounded f

/-- The actual original full adelic cusp function has a common uniform increment bound along both genuine real one-parameter orbits. -/
theorem actual_adelic_uniform_orbit_increments_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : RationalAdelicGL2, ∀ s t : ℝ,
      ‖canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (realUpperUnipotent s)) -
        canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (realUpperUnipotent t))‖ ≤
          C * |s - t| ∧
      ‖canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (realGeodesicCurve s)) -
        canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (realGeodesicCurve t))‖ ≤
          C * |s - t| :=
  canonicalAdelicGL2CuspLift_real_orbits_lipschitz N f

/-- The actual original cusp generator has both genuine arithmetic quotient L2 derivatives. -/
theorem actual_adelic_generator_L2_derivatives_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    DifferentiableAt ℝ (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicGenerator N f))) 0 ∧
    DifferentiableAt ℝ (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicGenerator N f))) 0 :=
  ⟨adelicCyclicGenerator_unipotent_L2_differentiableAt N f,
    adelicCyclicGenerator_geodesic_L2_differentiableAt N f⟩

/-- The actual original completed generator has both genuine Hilbert norm derivatives. -/
theorem actual_adelic_generator_Hilbert_derivatives_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    DifferentiableAt ℝ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicHilbertGenerator f)) 0 ∧
    DifferentiableAt ℝ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicHilbertGenerator f)) 0 :=
  ⟨adelicCyclicHilbertGenerator_unipotent_differentiableAt f,
    adelicCyclicHilbertGenerator_geodesic_differentiableAt f⟩

/-- The actual original completed generator's compact derivative has precisely its original weight. -/
theorem actual_adelic_generator_compact_Hilbert_derivative_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    HasDerivAt (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realRotationCurve t)) (adelicCyclicHilbertGenerator f))
      (((k : ℂ) * Complex.I) • adelicCyclicHilbertGenerator f) 0 :=
  adelicCyclicHilbertGenerator_rotation_hasDerivAt f

/-- The actual arithmetic quotient L2 derivatives retain the original holomorphic weight identity. -/
theorem actual_adelic_L2_holomorphic_identity_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    deriv (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicGenerator N f))) 0 -
    Complex.I • deriv (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicGenerator N f))) 0 =
    ((k : ℂ) / 2) • adelicProjectiveCyclicToL2 N f (adelicCyclicGenerator N f) :=
  adelicCyclicGenerator_L2_holomorphic_identity N f

/-- The actual original completed generator satisfies its holomorphic identity between genuine Hilbert derivatives. -/
theorem actual_adelic_Hilbert_holomorphic_identity_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicHilbertGenerator f)) 0 -
    Complex.I • deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicHilbertGenerator f)) 0 =
    ((k : ℂ) / 2) • adelicCyclicHilbertGenerator f :=
  adelicCyclicHilbertGenerator_holomorphic_identity f

open scoped ContDiff in
/-- The actual original completed generator is smooth to every order along its genuine unipotent subgroup. -/
theorem actual_adelic_Hilbert_unipotent_smoothness_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    ContDiff ℝ ∞ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicHilbertGenerator f)) :=
  adelicCyclicHilbertGenerator_unipotent_contDiff f

/-- Every genuine original geodesic derivative has a proved uniform bound over all full adelic points and all real parameters. -/
theorem actual_adelic_geodesic_jets_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ n : ℕ, ∀ g : RationalAdelicGL2, ∀ t : ℝ,
      ‖iteratedDeriv n (fun u : ℝ => canonicalAdelicGL2CuspLift N k f
        (g * adelicRealSL2Embedding (realGeodesicCurve u))) t‖ ≤ B n :=
  canonicalAdelicGL2CuspLift_geodesic_jets_bounded N f

open scoped ContDiff in
/-- The actual original completed generator is smooth along each of its three genuine real one-parameter directions. -/
theorem actual_adelic_Hilbert_three_orbits_smooth_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    ContDiff ℝ ∞ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicHilbertGenerator f)) ∧
    ContDiff ℝ ∞ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicHilbertGenerator f)) ∧
    ContDiff ℝ ∞ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realRotationCurve t)) (adelicCyclicHilbertGenerator f)) :=
  ⟨adelicCyclicHilbertGenerator_unipotent_contDiff f,
    adelicCyclicHilbertGenerator_geodesic_contDiff f,
    adelicCyclicHilbertGenerator_rotation_contDiff f⟩


/-- The original quotient holomorphic vector has exactly the original slash slice as its representative. -/
theorem actual_adelic_holomorphic_L2_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    DifferentiableOn ℂ (adelicHolomorphicL2Curve N f) (Metric.ball 0 (1 / 2 : ℝ)) ∧
    ⇑(adelicHolomorphicL2Curve N f z) =ᵐ[
      adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)]
      adelicProjectiveHolomorphicSlice N f z :=
  ⟨adelicHolomorphicL2Curve_differentiableOn N f, adelicHolomorphicL2Curve_ae_slice N f hz⟩

open scoped ContDiff in
/-- The original completed generator has genuine joint smoothness in all three actual Iwasawa parameters. -/
theorem actual_adelic_Hilbert_iwasawa_joint_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    ContDiffAt ℝ ∞ (fun w : (ℝ × ℝ) × ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding
        (realAffineMatrix w.1.1 (Real.exp_pos w.1.2) * realRotationCurve w.2))
      (adelicCyclicHilbertGenerator f)) 0 :=
  adelicCyclicHilbertGenerator_iwasawa_contDiffAt_zero f

open scoped ContDiff in
/-- Every smooth family of actual determinant-one real matrix entries gives a smooth orbit of the original completed generator. -/
theorem actual_adelic_Hilbert_real_families_source
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (h : E → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hh : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun w => h w i j)) :
    ContDiff ℝ ∞ (fun w => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (h w)) (adelicCyclicHilbertGenerator f)) :=
  adelicCyclicHilbertGenerator_real_contDiff f h hh


/-- The actual original Hilbert jets have precisely their original pointwise projective representatives. -/
theorem actual_adelic_Hilbert_jets_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) (n : ℕ) (t : ℝ) :
    (⇑(adelicCyclicHilbertToL2 f (iteratedDeriv n (fun u : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realUpperUnipotent u)) (adelicCyclicHilbertGenerator f)) t)) =ᵐ[
      adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)]
      fun p => iteratedDeriv n (fun u : ℝ => adelicProjectiveRealOrbit N f realUpperUnipotent u p) t) ∧
    (⇑(adelicCyclicHilbertToL2 f (iteratedDeriv n (fun u : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realGeodesicCurve u)) (adelicCyclicHilbertGenerator f)) t)) =ᵐ[
      adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)]
      fun p => iteratedDeriv n (fun u : ℝ => adelicProjectiveRealOrbit N f realGeodesicCurve u p) t) := by
  constructor
  · rw [adelicCyclicHilbertGenerator_unipotent_jet_toL2]
    exact adelicCyclicGenerator_unipotent_L2_jets_ae N f n t
  · rw [adelicCyclicHilbertGenerator_geodesic_jet_toL2]
    exact adelicCyclicGenerator_geodesic_L2_jets_ae N f n t

/-- The original completed representation has the exact second-order eigenvalue for literal successive Hilbert orbit derivatives. -/
theorem actual_adelic_Hilbert_second_order_operator_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    -(deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realGeodesicCurve t)) (deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicHilbertGenerator f)) 0)) 0) +
      (deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicHilbertGenerator f)) 0) -
      (deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realUpperUnipotent t)) (deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicHilbertGenerator f)) 0)) 0) +
      (deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realUpperUnipotent t)) (deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realRotationCurve t)) (adelicCyclicHilbertGenerator f)) 0)) 0) =
      (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • adelicCyclicHilbertGenerator f :=
  adelicCyclicHilbertGenerator_casimir f


open scoped ContDiff in
/-- The genuine smooth-space infinitesimal operator retains the literal original Hilbert orbit derivative. -/
theorem actual_adelic_smooth_infinitesimal_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (c : ℝ → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j)) (v : adelicRealSmoothSubmodule f) :
    (adelicSmoothInfinitesimal f c hc v).val = deriv (fun t : ℝ =>
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (c t)) v.val) 0 :=
  adelicSmoothInfinitesimal_apply f c hc v

/-- The actual original generator in the genuine smooth subspace has the exact original second-order eigenvalue. -/
theorem actual_adelic_smooth_generator_operator_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    (adelicSmoothGenerator f).val = adelicCyclicHilbertGenerator f ∧
    adelicSmoothCasimirOperator f (adelicSmoothGenerator f) =
      (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • adelicSmoothGenerator f :=
  ⟨rfl, adelicSmoothGenerator_casimir f⟩


/-- All three original smooth-space sl2 brackets are proved for the actual adelic cusp representation. -/
theorem actual_adelic_smooth_sl2_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    (adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff) * (adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff) - (adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff) * (adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff) = adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff ∧
    (adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff) * (adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff) - (adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff) * (adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff) = -(adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff) ∧
    (adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff) * (adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff) - (adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff) * (adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff) = (2 : ℂ) • (adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff) :=
  ⟨adelicSmoothInfinitesimal_geodesic_upper f, adelicSmoothInfinitesimal_geodesic_lower f,
    adelicSmoothInfinitesimal_upper_lower f⟩

/-- The original compact infinitesimal is exactly upper minus lower on the actual smooth space. -/
theorem actual_adelic_smooth_compact_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    adelicSmoothInfinitesimal f realRotationCurve realRotationCurve_entries_contDiff = (adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff) - (adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff) :=
  adelicSmoothInfinitesimal_compact f

/-- The literal original second-order operator commutes with all three actual infinitesimals and retains its original generator eigenvalue. -/
theorem actual_adelic_smooth_casimir_commutation_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    adelicSmoothCasimirOperator f * (adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff) = (adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff) * adelicSmoothCasimirOperator f ∧
    adelicSmoothCasimirOperator f * (adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff) = (adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff) * adelicSmoothCasimirOperator f ∧
    adelicSmoothCasimirOperator f * (adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff) = (adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff) * adelicSmoothCasimirOperator f ∧
    adelicSmoothCasimirOperator f (adelicSmoothGenerator f) =
      (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • adelicSmoothGenerator f :=
  ⟨(adelicSmoothCasimirOperator_commutes f).1.eq, (adelicSmoothCasimirOperator_commutes f).2.1.eq,
    (adelicSmoothCasimirOperator_commutes f).2.2.eq, adelicSmoothGenerator_casimir f⟩


open scoped ContDiff in
/-- The actual matrix Lie algebra action on every smooth real curve is its literal original Hilbert norm derivative. -/
theorem actual_adelic_matrix_Lie_action_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (c : ℝ → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j)) (hc0 : c 0 = 1)
    (v : adelicRealSmoothSubmodule f) :
    (adelicComplexSl2Action f (complexSl2OfRealTangent
      (deriv (fun t => c t 0 0) 0) (deriv (fun t => c t 1 0) 0) (deriv (fun t => c t 0 1) 0)) v).val =
      deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (c t)) v.val) 0 := by
  rw [adelicComplexSl2Action_curve f c hc hc0]
  exact adelicSmoothInfinitesimal_apply f c hc v

/-- The literal central element of the genuine full enveloping algebra acts by the exact original second-order Hilbert operator. -/
theorem actual_adelic_enveloping_casimir_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    complexSl2EnvelopingCasimir ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2) ∧
    adelicEnvelopingAction f complexSl2EnvelopingCasimir = adelicSmoothCasimirOperator f :=
  ⟨complexSl2EnvelopingCasimir_mem_center, adelicEnvelopingAction_casimir f⟩

/-- Every original enveloping-algebra translate of the genuine cusp generator has the precise central Casimir eigenvalue. -/
theorem actual_adelic_enveloping_casimir_orbit_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (z : UniversalEnvelopingAlgebra ℂ ComplexSl2) :
    adelicEnvelopingAction f complexSl2EnvelopingCasimir
      (adelicEnvelopingAction f z (adelicSmoothGenerator f)) =
      (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) •
        adelicEnvelopingAction f z (adelicSmoothGenerator f) := by
  exact (congrArg (fun T : Module.End ℂ (adelicRealSmoothSubmodule f) =>
    T (adelicEnvelopingAction f z (adelicSmoothGenerator f)))
    (adelicEnvelopingAction_casimir f)).trans (adelicEnvelopingAction_casimir_orbit f z)


/-- The original raising derivatives are independent and have the exact original compact weights and lowering coefficients. -/
theorem actual_adelic_raising_ladder_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (hk : 0 < k) :
    LinearIndependent ℂ (adelicRaisingJet f) ∧
    (∀ n : ℕ, ⁅compactSl2H, adelicRaisingJet f n⁆ = ((k : ℂ) + 2 * n) • adelicRaisingJet f n) ∧
    (∀ n : ℕ, ⁅compactSl2F, adelicRaisingJet f (n + 1)⁆ =
      (((n : ℂ) + 1) * (-(k : ℂ) - n)) • adelicRaisingJet f n) :=
  ⟨adelicRaisingJet_linearIndependent f hf hk, adelicRaisingJet_weight f hf,
    adelicRaisingJet_lower f hf⟩

/-- The literal original enveloping cyclic span is the irreducible original lowest-weight Lie module. -/
theorem actual_adelic_lowest_weight_irreducible_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (hk : 0 < k) :
    adelicRaisingSpan f = Submodule.span ℂ (Set.range (fun z : UniversalEnvelopingAlgebra ℂ ComplexSl2 =>
      adelicEnvelopingAction f z (adelicSmoothGenerator f))) ∧
    LieModule.IsIrreducible ℂ ComplexSl2 (adelicRaisingLieSubmodule f hf) :=
  ⟨adelicRaisingSpan_eq_enveloping f hf, adelicRaisingLieSubmodule_irreducible f hf hk⟩

/-- The full genuine center acts through the actual infinitesimal character on every original cyclic vector. -/
theorem actual_adelic_infinitesimal_character_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2))
    (v : adelicRealSmoothSubmodule f) (hv : v ∈ adelicRaisingSpan f) :
    adelicEnvelopingAction f z.val v = adelicInfinitesimalCharacter f hf z • v :=
  adelicInfinitesimalCharacter_span f hf z v hv

/-- The genuine infinitesimal character has the exact original normalized Casimir value. -/
theorem actual_adelic_infinitesimal_character_casimir_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) :
    adelicInfinitesimalCharacter f hf
      ⟨complexSl2EnvelopingCasimir, complexSl2EnvelopingCasimir_mem_center⟩ =
      ((k : ℂ) / 2) * (1 - (k : ℂ) / 2) :=
  adelicInfinitesimalCharacter_casimir f hf


open scoped ContDiff in
/-- Every original smooth real-curve derivative has the actual skew identity in the original Hilbert inner product. -/
theorem actual_adelic_unitary_infinitesimal_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (c : ℝ → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j)) (hc0 : c 0 = 1)
    (v w : adelicRealSmoothSubmodule f) :
    inner ℂ (adelicSmoothInfinitesimal f c hc v).val w.val +
      inner ℂ v.val (adelicSmoothInfinitesimal f c hc w).val = 0 :=
  adelicSmoothInfinitesimal_skew f c hc hc0 v w

/-- Every original raising derivative has its exact original Hilbert norm, including the original generator normalization. -/
theorem actual_adelic_raising_norm_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (n : ℕ) :
    ‖(adelicRaisingJet f n).val‖ ^ 2 =
      (n.factorial : ℝ) * (∏ j ∈ Finset.range n, ((k : ℝ) + j)) *
        ‖adelicCyclicHilbertGenerator f‖ ^ 2 :=
  adelicRaisingJet_norm_sq f hf n

/-- The genuine Hilbert basis of the original raising closure consists exactly of the original derivatives normalized in their original Hilbert norm. -/
theorem actual_adelic_raising_Hilbert_basis_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (hk : 0 < k) (n : ℕ) :
    (adelicRaisingHilbertBasis f hf hk n).val =
      ((‖(adelicRaisingJet f n).val‖⁻¹ : ℝ) : ℂ) • (adelicRaisingJet f n).val :=
  adelicRaisingHilbertBasis_apply f hf hk n

/-- Every genuine smooth compact-weight vector in the original closed span lies on its exact original raising line. -/
theorem actual_adelic_closed_weight_line_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (hk : 0 < k) (n : ℕ) (v : adelicRealSmoothSubmodule f)
    (hv : v.val ∈ adelicRaisingClosedSpan f)
    (hH : adelicComplexSl2Action f compactSl2H v = ((k : ℂ) + 2 * n) • v) :
    ∃ a : ℂ, v = a • adelicRaisingJet f n :=
  adelicRaisingClosedSpan_weight_line f hf hk n v hv hH


/-- Original bounded real intertwiners act by one scalar on the actual raising closure when their original generator image belongs to it. -/
theorem actual_adelic_closed_intertwiner_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (hk : 0 < k) (T : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f)
    (hT : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ v,
      T (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v) =
        adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) (T v))
    (hv : T (adelicCyclicHilbertGenerator f) ∈ adelicRaisingClosedSpan f) :
    ∃ a : ℂ, ∀ v ∈ adelicRaisingClosedSpan f, T v = a • v :=
  adelicIntertwiner_closedSpan_scalar f hf hk T hT hv

open scoped ContDiff in
/-- Every original all-order Hilbert orbit jet is the power of its original smooth infinitesimal. -/
theorem actual_adelic_all_order_orbit_jet_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (c : ℝ → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j))
    (hadd : ∀ s t, c (s + t) = c s * c t) (hc0 : c 0 = 1)
    (v : adelicRealSmoothSubmodule f) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (c t)) v.val) 0 =
        (((adelicSmoothInfinitesimal f c hc) ^ n) v).val :=
  adelicSmoothInfinitesimal_iteratedDeriv_zero f c hc hadd hc0 v n

/-- The actual normalized Hilbert orbit is holomorphic on the full upper half-plane and belongs to its original raising closure there. -/
theorem actual_adelic_global_holomorphic_orbit_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) :
    DifferentiableOn ℂ (adelicNormalizedAffineHilbertOrbit f) UpperHalfPlane.upperHalfPlaneSet ∧
      ∀ z : ℂ, 0 < z.im → adelicNormalizedAffineHilbertOrbit f z ∈ adelicRaisingClosedSpan f :=
  ⟨adelicNormalizedAffineHilbertOrbit_differentiableOn f,
    fun _ hz => adelicNormalizedAffineHilbertOrbit_mem_closedSpan f hf hz⟩

/-- The actual raising closure is exactly the original nonzero real cyclic Hilbert subspace and is invariant under the original real action. -/
theorem actual_adelic_real_cyclic_closure_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) :
    adelicRaisingClosedSpan f = adelicRealCyclicClosedSpan f ∧
      adelicRealCyclicClosedSpan f ≠ ⊥ ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ v ∈ adelicRaisingClosedSpan f,
        adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v ∈ adelicRaisingClosedSpan f :=
  ⟨adelicRaisingClosedSpan_eq_realCyclicClosedSpan f hf, adelicRealCyclicClosedSpan_ne_bot f hf,
    adelicRaisingClosedSpan_real_invariant f hf⟩

/-- The genuine original real cyclic Hilbert representation has no nonzero proper closed invariant subspace. -/
theorem actual_adelic_real_cyclic_irreducible_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (hk : 0 < k) (p : Submodule ℂ (AdelicCyclicHilbert f))
    (hp : IsClosed (p : Set (AdelicCyclicHilbert f))) (hle : p ≤ adelicRealCyclicClosedSpan f)
    (hinv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ v ∈ p,
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v ∈ p) :
    p = ⊥ ∨ p = adelicRealCyclicClosedSpan f :=
  adelicRealCyclicClosedSpan_irreducible f hf hk p hp hle hinv


/-- The original universal central polynomial has its proved reflection identity at every complex weight. -/
theorem actual_verma_full_center_reflection_source
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) (μ : ℂ) :
    Polynomial.aeval μ (vermaUniversalCentralPolynomial z) = vermaPolynomialCentralValue μ z ∧
      vermaPolynomialCentralValue μ z = vermaPolynomialCentralValue (-μ - 2) z :=
  ⟨vermaUniversalCentralPolynomial_aeval μ z, vermaPolynomialCentralValue_reflection μ z⟩

/-- Original polynomial monomials are the literal original cusp raising jets and the entire original enveloping action intertwines. -/
theorem actual_adelic_verma_intertwiner_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (n : ℕ) (z : UniversalEnvelopingAlgebra ℂ ComplexSl2) (p : Polynomial ℂ) :
    adelicVermaMap f (Polynomial.X ^ n) = adelicRaisingJet f n ∧
      adelicVermaMap f (vermaPolynomialEnvelopingAction (-(k : ℂ)) z p) =
        adelicEnvelopingAction f z (adelicVermaMap f p) :=
  ⟨adelicVermaMap_X_pow f n, adelicVermaMap_enveloping f hf z p⟩

/-- Every element of the genuine original cusp center character has the reflected polynomial parameter k-2. -/
theorem actual_adelic_reflected_character_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    adelicInfinitesimalCharacter f hf z =
      Polynomial.aeval ((k : ℂ) - 2) (vermaUniversalCentralPolynomial z) :=
  adelicInfinitesimalCharacter_polynomial f hf z

/-- The genuine finite-dimensional homogeneous representation retains actual matrix substitution and a nonzero original compact generator. -/
theorem actual_homogeneous_matrix_representation_source (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ)
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ n) :
    Module.Finite ℂ (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ n) ∧
      (homogeneousMatrixRepresentation n g p).val = matrixPolynomialAction g p.val ∧
      homogeneousCompactGenerator n ≠ 0 :=
  ⟨homogeneousPolynomial_finite n, homogeneousMatrixAction_apply n g p,
    homogeneousCompactGenerator_ne_zero n⟩

/-- The original cusp character acts exactly on the actual degree-(k-2) algebraic lowest vector for every genuine central element. -/
theorem actual_adelic_homogeneous_character_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (n : ℕ) (hk : k = (n : ℤ) + 2)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    homogeneousEnvelopingAction n z.val (homogeneousCompactGenerator n) =
      adelicInfinitesimalCharacter f hf z • homogeneousCompactGenerator n :=
  adelicInfinitesimalCharacter_homogeneous_generator f hf n hk z


/-- The exact original homogeneous degree-n representation has dimension n+1 and its literal raising vectors form a basis. -/
theorem actual_homogeneous_raising_basis_source (n : ℕ) (r : Fin (n + 1)) :
    Module.finrank ℂ (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ n) = n + 1 ∧
      homogeneousRaisingBasis n r = homogeneousRaisingJet n r.val :=
  ⟨homogeneousBinary_finrank n, homogeneousRaisingBasis_apply n r⟩

/-- Every original homogeneous vector has the full original cusp central character when its degree is exactly k-2. -/
theorem actual_adelic_full_homogeneous_character_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (n : ℕ) (hk : k = (n : ℤ) + 2)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2))
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ n) :
    homogeneousEnvelopingAction n z.val p = adelicInfinitesimalCharacter f hf z • p :=
  adelicInfinitesimalCharacter_homogeneous_scalar f hf n hk z p

/-- The actual polynomial matrix curve and its genuine pointwise derivative retain the original matrix substitution and derivation. -/
theorem actual_polynomial_matrix_tangent_source (a : Matrix (Fin 2) (Fin 2) ℂ)
    (p : MvPolynomial (Fin 2) ℂ) (x : Fin 2 → ℂ) (t : ℂ) :
    Polynomial.eval (MvPolynomial.C t) (matrixPolynomialCurve a p) =
      matrixPolynomialAction (1 + t • a) p ∧
    HasDerivAt (fun t : ℂ => MvPolynomial.eval x (matrixPolynomialAction (1 + t • a) p))
      (MvPolynomial.eval x (matrixPolynomialDerivation a p)) 0 :=
  ⟨matrixPolynomialCurve_eval a t p, matrixPolynomialOrbit_hasDerivAt a p x⟩

/-- The literal determinant twist of the genuine even-degree homogeneous representation has exactly trivial scalar-matrix action. -/
theorem actual_homogeneous_determinant_twist_source (m : ℕ) (u : ℂˣ)
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m)) :
    homogeneousDeterminantTwist (2 * m) (-(m : ℤ))
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u) p = p :=
  homogeneousDeterminantTwist_trivial_center m u p

/-- The original full GL₂ enveloping center projects into the actual SL₂ center through the genuine surjective trace map. -/
theorem actual_traceless_enveloping_center_source
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ))) :
    Function.Surjective tracelessEnvelopingProjection ∧
      tracelessEnvelopingProjection z.val ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2) :=
  ⟨tracelessEnvelopingProjection_surjective, tracelessEnvelopingProjection_mem_center z⟩


/-- The genuine twisted homogeneous group action has its exact original finite-dimensional norm derivative. -/
theorem actual_homogeneous_gl2_norm_derivative_source (m : ℕ)
    (a : Matrix (Fin 2) (Fin 2) ℂ) (p : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m)) :
    HasDerivAt (fun t : ℂ => homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) (complexIdentityGLCurve a t) p)
      (homogeneousNormalizedGL2Action m a p) 0 :=
  homogeneousNormalizedGL2Action_hasDerivAt m a p

/-- The original positive real general-linear action equals its genuine normalized special-linear action on every completed vector. -/
theorem actual_adelic_positive_normalization_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (g : GL(2, ℝ)⁺) (v : AdelicCyclicHilbert f) :
    adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g.val) v =
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realPositiveNormalize g)) v :=
  adelicCyclicHilbert_positive_normalize f g v

/-- The original full real general-linear curve has its actual original Hilbert norm derivative on every genuine smooth vector. -/
theorem actual_adelic_gl2_norm_derivative_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v : adelicRealSmoothSubmodule f) (c : ℝ → Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hc : c 0 = 1) (a : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => (c t).val i j) (a i j) 0) :
    HasDerivAt (fun t => adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding (c t)) v.val)
      (adelicComplexGL2Action f (a.map Complex.ofReal) v).val 0 :=
  adelicComplexGL2Action_hasDerivAt f v c hc a hd

/-- The entire original full GL₂ enveloping center has its genuine scalar action on the actual cusp cyclic Lie module. -/
theorem actual_adelic_gl2_central_action_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)))
    (v : adelicRealSmoothSubmodule f) (hv : v ∈ adelicRaisingSpan f) :
    adelicGL2EnvelopingAction f z.val v = adelicGL2InfinitesimalCharacter f hf z • v :=
  adelicGL2InfinitesimalCharacter_span f hf z v hv

/-- The full original cusp GL₂ infinitesimal character equals the actual full central scalar on every vector of its precise degree-(k-2) determinant twist. -/
theorem actual_adelic_full_gl2_algebraic_character_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (m : ℕ) (hk : k = (2 * m : ℕ) + 2)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)))
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m)) :
    homogeneousGL2EnvelopingAction m z.val p = adelicGL2InfinitesimalCharacter f hf z • p :=
  adelicGL2InfinitesimalCharacter_algebraic f hf m hk z p


/-- The actual rotation subgroup exhausts the original compact stabilizer. -/
theorem actual_adelic_compact_stabilizer_source (g : realCompactSubgroup) :
    ∃ t : ℝ, g.val = realRotationCurve t := realCompactSubgroup_eq_rotation g

/-- Every literal raising derivative has the exact original rotation character. -/
theorem actual_adelic_raising_rotation_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (n : ℕ) (t : ℝ) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realRotationCurve t))
      (adelicRaisingJet f n).val =
        Complex.exp ((t : ℂ) * (Complex.I * ((k : ℂ) + 2 * n))) • (adelicRaisingJet f n).val :=
  adelicRaisingJet_rotation f hf n t

/-- In the genuine original real cyclic Hilbert space, K-finiteness is exactly finite original raising expansion. -/
theorem actual_real_kfinite_identification_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (hk : 0 < k) (v : AdelicCyclicHilbert f) (hv : v ∈ adelicRealCyclicClosedSpan f) :
    FiniteDimensional ℂ (adelicCompactOrbitSpan f v) ↔
      v ∈ Submodule.span ℂ (Set.range (fun n : ℕ => (adelicRaisingJet f n).val)) :=
  adelicRealCyclic_KFinite_iff f hf hk v hv

/-- Every original real K-finite Hilbert vector is genuinely smooth, without an added smoothness premise. -/
theorem actual_real_kfinite_smooth_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (hk : 0 < k) (v : AdelicCyclicHilbert f) (hv : v ∈ adelicRealCyclicClosedSpan f)
    [FiniteDimensional ℂ (adelicCompactOrbitSpan f v)] : v ∈ adelicRealSmoothSubmodule f :=
  adelicRealKFinite_mem_smooth f hf hk v hv

/-- The entire actual GL₂ center has the same original scalar on every real K-finite cusp vector and every vector of the genuine algebraic determinant twist. -/
theorem actual_real_kfinite_full_character_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (m : ℕ) (hk : k = (2 * m : ℕ) + 2)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)))
    (v : adelicRealSmoothSubmodule f) (hv : v.val ∈ adelicRealCyclicClosedSpan f)
    [FiniteDimensional ℂ (adelicCompactOrbitSpan f v.val)]
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m)) :
    adelicGL2EnvelopingAction f z.val v = adelicGL2InfinitesimalCharacter f hf z • v ∧
      homogeneousGL2EnvelopingAction m z.val p = adelicGL2InfinitesimalCharacter f hf z • p :=
  adelicRealKFinite_algebraic_character f hf m hk z v hv p


/-- Every actual coefficient of the original determinant twist is an actual polynomial divided by a power of its nonzero determinant. -/
theorem actual_algebraic_coefficients_source (m : ℕ)
    (v : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m))
    (L : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m) →ₗ[ℂ] ℂ) :
    ∃ q : MvPolynomial (Fin 2 × Fin 2) ℂ, ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℂ,
      L (homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) g v) =
        MvPolynomial.eval (fun ij => g.val ij.1 ij.2) q / Matrix.det g.val ^ m :=
  homogeneousDeterminantTwist_regular_coefficient m v L

/-- Actual group invariance forces a subspace of the original determinant twist to be zero or the entire original space. -/
theorem actual_algebraic_irreducibility_source (m : ℕ)
    (p : Submodule ℂ (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m)))
    (hi : ∀ g v, v ∈ p → homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) g v ∈ p) :
    p = ⊥ ∨ p = ⊤ := homogeneousDeterminantTwist_irreducible m p hi

/-- The original nonzero pure-power vector has the exact highest weight under every original diagonal torus element. -/
theorem actual_algebraic_highest_weight_source (m : ℕ) (u v : ℂˣ) :
    homogeneousPurePower (2 * m) (0 : Fin 2) ≠ 0 ∧
    homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) (complexDiagonalGL u v)
      (homogeneousPurePower (2 * m) (0 : Fin 2)) =
      ((u : ℂ) ^ m * (v : ℂ) ^ (-(m : ℤ))) • homogeneousPurePower (2 * m) (0 : Fin 2) :=
  ⟨homogeneousPurePower_ne_zero _ _, homogeneousDeterminantTwist_highest_weight m u v⟩

/-- The original real K-finite cusp module has the same full central character as its actual irreducible algebraic model with the proved regular shifted highest weight. -/
theorem actual_regular_algebraic_model_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) (hf : f ≠ 0) (m : ℕ)
    (hk : k = (2 * m : ℕ) + 2)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)))
    (v : adelicRealSmoothSubmodule f) (hv : v.val ∈ adelicRealCyclicClosedSpan f)
    [FiniteDimensional ℂ (adelicCompactOrbitSpan f v.val)]
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m)) :
    (∀ w : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m),
      ∀ L : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m) →ₗ[ℂ] ℂ,
      ∃ q : MvPolynomial (Fin 2 × Fin 2) ℂ, ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℂ,
        L (homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) g w) =
          MvPolynomial.eval (fun ij => g.val ij.1 ij.2) q / Matrix.det g.val ^ m) ∧
    (∀ U : Submodule ℂ (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * m)),
      (∀ g w, w ∈ U → homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) g w ∈ U) →
        U = ⊥ ∨ U = ⊤) ∧
    homogeneousPurePower (2 * m) (0 : Fin 2) ≠ 0 ∧
    (-(m : ℤ) ≤ (m : ℤ) ∧ (m : ℤ) + 1 - (-(m : ℤ)) = 2 * m + 1 ∧
      0 < (m : ℤ) + 1 - (-(m : ℤ))) ∧
    (∀ u w : ℂˣ, homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) (complexDiagonalGL u w)
      (homogeneousPurePower (2 * m) (0 : Fin 2)) =
      ((u : ℂ) ^ m * (w : ℂ) ^ (-(m : ℤ))) • homogeneousPurePower (2 * m) (0 : Fin 2)) ∧
    adelicGL2EnvelopingAction f z.val v = adelicGL2InfinitesimalCharacter f hf z • v ∧
    homogeneousGL2EnvelopingAction m z.val p = adelicGL2InfinitesimalCharacter f hf z • p :=
  adelicRealKFinite_regular_algebraic_model f hf m hk z v hv p


/-- The original full lowest-weight subspace is defined by the genuine rotation character at every real angle. -/
theorem actual_lowest_rotation_space_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (v : AdelicCyclicHilbert f) : v ∈ adelicRotationWeightSpace f ↔ ∀ t : ℝ,
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realRotationCurve t)) v =
        Complex.exp ((t : ℂ) * (Complex.I * (k : ℂ))) • v :=
  mem_adelicRotationWeightSpace f v

/-- The actual positive lowest-weight projector annihilates the entire reflected original real component. -/
theorem actual_reflected_lowest_projection_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (hk : 0 < k) (v : AdelicCyclicHilbert f) (hv : v ∈ adelicRealCyclicClosedSpan f) :
    adelicRotationWeightProjection f
      (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection)) v) = 0 :=
  adelicRotationWeightProjection_reflectedReal f hf hk v hv

/-- Every original full adelic orbit vector projects to its actual finite-coordinate orbit line. -/
theorem actual_full_adelic_lowest_projection_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (hk : 0 < k) (g : RationalAdelicGL2) :
    ∃ c : ℂ, adelicRotationWeightProjection f
      (adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f)) =
      c • adelicCyclicHilbertRepresentation f
        (rationalAdelicFiniteGL2Embedding (rationalAdelicGL2RealFiniteEquiv g).2)
        (adelicCyclicHilbertGenerator f) :=
  adelicRotationWeightProjection_fullOrbit f hf hk g

/-- The entire full original lowest-weight space is precisely the closed span of the original finite-adelic cusp translates. -/
theorem actual_full_lowest_space_source (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hf : f ≠ 0) (hk : 0 < k) :
    adelicRotationWeightSpace f =
      (Submodule.span ℂ (Set.range
        (fun a : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ) =>
          adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
            (adelicCyclicHilbertGenerator f)))).topologicalClosure :=
  adelicRotationWeightSpace_eq_finiteClosure f hf hk


open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- Exact original-object consumer of `adelicLevelProjection_finiteSpan`. -/
theorem actual_fixed_level_projection_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : AdelicCyclicHilbert f) (hv : v ∈ adelicFiniteCyclicSpan f) :
    adelicLevelProjection f v ∈ adelicFiniteCyclicSpan f :=
  adelicLevelProjection_finiteSpan f v hv

/-- Exact original-object consumer of `adelicFixedLowest_algebraic_density`. -/
theorem actual_fixed_lowest_density_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k) :
    (adelicFiniteCyclicSpan f ⊓ adelicLevelFixedSpace f).topologicalClosure =
      adelicRotationWeightSpace f ⊓ adelicLevelFixedSpace f :=
  adelicFixedLowest_algebraic_density f hf hk

/-- Exact original-object consumer of `finiteAdelicClassicalTranslate_real_lift`. -/
theorem actual_finite_translate_classical_source (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (g : SL(2, ℝ)) :
    canonicalAdelicGL2CuspLift N k f (adelicRealSL2Embedding g * rationalAdelicFiniteGL2Embedding a) =
      realWeightLift k (finiteAdelicClassicalTranslate N k f a) g :=
  finiteAdelicClassicalTranslate_real_lift N k f a g

/-- Exact original-object consumer of `adelicAlgebraicFiniteSpan_classical_full`. -/
theorem actual_fixed_finite_classical_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : v ∈ adelicAlgebraicFiniteSpan f)
    (hlevel : adelicCyclicHilbertEmbedding f v ∈ adelicLevelFixedSpace f) :
    ∃! F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k,
      v.val = canonicalAdelicGL2CuspLift N k F :=
  adelicAlgebraicFiniteSpan_classical_full f v hv hlevel

/-- Exact original-object consumer of `adelicFixedLowest_finiteDimensional`. -/
theorem actual_fixed_lowest_finite_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k) :
    FiniteDimensional ℂ ↥(adelicRotationWeightSpace f ⊓ adelicLevelFixedSpace f :
      Submodule ℂ (AdelicCyclicHilbert f)) :=
  adelicFixedLowest_finiteDimensional f hf hk

/-- Exact original-object consumer of `adelicFixedLowest_classical_reconstruction`. -/
theorem actual_fixed_lowest_classical_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k)
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicRotationWeightSpace f)
    (hlevel : v ∈ adelicLevelFixedSpace f) :
    ∃ w ∈ adelicAlgebraicFiniteSpan f, adelicCyclicHilbertEmbedding f w = v ∧
      ∃! F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k,
        w.val = canonicalAdelicGL2CuspLift N k F :=
  adelicFixedLowest_classical_reconstruction f hf hk v hv hlevel


/-- Exact original-object consumer of `integralGamma0_finite_dense`. -/
theorem actual_finite_level_density_source (N : ℕ) [NeZero N]
    (g : SL(2, FiniteAdeleRing ℤ ℚ)) (hg : g ∈ finiteAdeleGamma0 N) :
    g ∈ closure (Set.range (fun γ : Gamma0 N =>
      Matrix.SpecialLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ)) γ.val)) :=
  integralGamma0_finite_dense N g hg

/-- Exact original-object consumer of `finiteAdelicHeckeUpperCoset_surjective`. -/
theorem actual_full_finite_Hecke_cosets_source (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) : Function.Surjective (finiteAdelicHeckeUpperCoset N p hpN) :=
  finiteAdelicHeckeUpperCoset_surjective N p hpN

/-- Exact original-object consumer of `adelicHilbertHeckeTrace_primitive_generator`. -/
theorem actual_full_adelic_Hecke_eigen_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (f : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    adelicHilbertHeckeTrace f.toCuspForm p hpN (adelicCyclicHilbertGenerator f.toCuspForm) =
      ((Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) * cuspCoefficients f.toCuspForm p) •
        adelicCyclicHilbertGenerator f.toCuspForm :=
  adelicHilbertHeckeTrace_primitive_generator f hpN

/-- Exact original-object consumer of `primitiveCuspForm_good_prime_eigensystem_scalar`. -/
theorem actual_classical_prime_multiplicity_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hg : ∀ p, p.Prime → p.Coprime N →
      cuspHeckeLinear N k p g = cuspCoefficients f.toCuspForm p • g) :
    g = cuspCoefficients g 1 • f.toCuspForm :=
  primitiveCuspForm_good_prime_eigensystem_scalar f g hg

/-- Exact original-object consumer of `adelicPrimitiveIntertwiner_scalar`. -/
theorem actual_full_adelic_scalar_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (hk : 0 < k)
    (A : AdelicCyclicHilbert f.toCuspForm →L[ℂ] AdelicCyclicHilbert f.toCuspForm)
    (hA : ∀ g v, A (adelicCyclicHilbertRepresentation f.toCuspForm g v) =
      adelicCyclicHilbertRepresentation f.toCuspForm g (A v)) :
    ∃ c : ℂ, ∀ v, A v = c • v :=
  adelicPrimitiveIntertwiner_scalar f hk A hA

/-- Exact original-object consumer of `adelicPrimitiveHilbert_irreducible`. -/
theorem actual_full_adelic_irreducible_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (hk : 0 < k)
    (p : Submodule ℂ (AdelicCyclicHilbert f.toCuspForm))
    (hclosed : IsClosed (p : Set (AdelicCyclicHilbert f.toCuspForm)))
    (hp : ∀ g v, v ∈ p → adelicCyclicHilbertRepresentation f.toCuspForm g v ∈ p) :
    p = ⊥ ∨ p = ⊤ :=
  adelicPrimitiveHilbert_irreducible f hk p hclosed hp

/-- The full actual adelic Hecke trace equals the canonical lift of the classical Hecke operator with its exact determinant factor. -/
theorem actual_full_adelic_Hecke_classical_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (p : ℕ) [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hF : v.val = canonicalAdelicGL2CuspLift N k F) :
    (adelicAlgebraicHeckeTrace f p hpN v).val = canonicalAdelicGL2CuspLift N k
      ((Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) • cuspHecke p F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  adelicAlgebraicHeckeTrace_classical_full f p hpN v F hF


/-- Exact original-object consumer of `adelicNormalizedHecke_real_component`. -/
theorem actual_normalized_Hecke_real_component_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (f : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (v : AdelicCyclicHilbert f.toCuspForm) (hv : v ∈ adelicRealCyclicClosedSpan f.toCuspForm) :
    adelicNormalizedHecke f.toCuspForm p hpN v = normalizedCuspCoefficients f.toCuspForm p • v :=
  adelicNormalizedHecke_real_component f hpN v hv

/-- Exact original-object consumer of `finiteAdelicLocalGL2Hom_injective`. -/
theorem actual_finite_place_embedding_source (v : HeightOneSpectrum ℤ) :
    Function.Injective (finiteAdelicLocalGL2Hom v) :=
  finiteAdelicLocalGL2Hom_injective v

/-- Exact original-object consumer of `finiteAdelicLocalGL2_continuous`. -/
theorem actual_finite_place_continuity_source (v : HeightOneSpectrum ℤ) :
    Continuous (finiteAdelicLocalGL2Hom v) :=
  finiteAdelicLocalGL2_continuous v

/-- Exact original-object consumer of `adelicPrimitive_good_prime_spherical`. -/
theorem actual_good_prime_spherical_source {N p : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (hp : p.Prime) (hpN : p.Coprime N) :
    adelicCyclicHilbertGenerator f.toCuspForm ≠ 0 ∧
      ∀ g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p hp).adicCompletionIntegers ℚ),
        adelicCyclicLocalRepresentation f.toCuspForm (rationalPrimePlace p hp)
          (GeneralLinearGroup.map ((rationalPrimePlace p hp).adicCompletionIntegers ℚ).subtype g)
          (adelicCyclicHilbertGenerator f.toCuspForm) = adelicCyclicHilbertGenerator f.toCuspForm :=
  adelicPrimitive_good_prime_spherical f hp hpN

/-- Actual original bounded finite-adelic Hecke trace with its full p+1 unitary bound. -/
theorem actual_bounded_Hecke_trace_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (p : ℕ) [NeZero p] (hpN : p.Coprime N)
    (v : AdelicCyclicHilbert f) :
    ‖adelicBoundedHeckeTrace f p hpN v‖ ≤ (p + 1 : ℝ) * ‖v‖ :=
  adelicBoundedHeckeTrace_norm_le f p hpN v

/-- Exact equality of the original adelic Hecke operator with the actual local-place sum on every original level-fixed vector. -/
theorem actual_Hecke_localization_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLevelFixedSpace f) :
    adelicNormalizedHecke f p hpN x = adelicLocalNormalizedHecke f p hp hpN x :=
  adelicNormalizedHecke_eq_local f p hp hpN x hx

/-- The genuine localized Hecke sum has precisely the original primitive Fourier coefficient as its eigenvalue. -/
theorem actual_local_Hecke_eigenvalue_source {N p : ℕ} [NeZero N] [NeZero p] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hp : p.Prime) (hpN : p.Coprime N) :
    adelicLocalNormalizedHecke F.toCuspForm p hp hpN (adelicCyclicHilbertGenerator F.toCuspForm) =
      normalizedCuspCoefficients F.toCuspForm p • adelicCyclicHilbertGenerator F.toCuspForm :=
  adelicLocalNormalizedHecke_primitive_generator F hp hpN


/-- Exact original-object consumer of `finiteAdelicLevelAt_surjective`. -/
theorem actual_local_level_surjection_source (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ) :
    Function.Surjective (finiteAdelicLevelAt N v) :=
  finiteAdelicLevelAt_surjective N v

/-- Exact original-object consumer of `finitePlaceHeckeCosets_card`. -/
theorem actual_intrinsic_local_Hecke_cosets_source (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) :
    Nat.card (finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)) ⧸
      finitePlaceHeckeUpper N p (Fact.out : p.Prime)) = p + 1 :=
  finitePlaceHeckeCosets_card N p hpN

/-- Exact original-object consumer of `finitePlaceGL2Gamma0_good_eq_one`. -/
theorem actual_good_prime_full_integral_group_source (N p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) :
    finitePlaceGL2Gamma0 N (rationalPrimePlace p hp) = finitePlaceGL2Gamma0 1 (rationalPrimePlace p hp) :=
  finitePlaceGL2Gamma0_good_eq_one N p hp hpN

/-- Exact original-object consumer of `finitePlaceIntegralMatrix_map`. -/
theorem actual_integral_local_matrix_source (v : HeightOneSpectrum ℤ) (g : finitePlaceGL2Gamma0 1 v) :
    GeneralLinearGroup.map (v.adicCompletionIntegers ℚ).subtype (finitePlaceIntegralMatrix v g) = g.val :=
  finitePlaceIntegralMatrix_map v g

/-- Exact original-object consumer of `adelicLocalNormalizedHecke_local_fixed`. -/
theorem actual_intrinsic_local_Hecke_preservation_source {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert f)
    (hx : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)),
      adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g.val x = x)
    (g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g.val
      (adelicLocalNormalizedHecke f p (Fact.out : p.Prime) hpN x) =
        adelicLocalNormalizedHecke f p (Fact.out : p.Prime) hpN x :=
  adelicLocalNormalizedHecke_local_fixed f hpN x hx g

/-- Exact original-object consumer of `adelicCyclicLocal_scalar_action`. -/
theorem actual_local_central_character_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : HeightOneSpectrum ℤ)
    (u : (v.adicCompletion ℚ)ˣ) (x : AdelicCyclicHilbert f) :
    adelicCyclicLocalRepresentation f v (GeneralLinearGroup.scalar (Fin 2) u) x = x :=
  adelicCyclicLocal_scalar_action f v u x


/-- Exact original-object consumer of `adelicLocalNormalizedHecke_symmetric`. -/
theorem actual_local_Hecke_symmetry_source {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hpN : p.Coprime N)
    (x y : AdelicCyclicHilbert f)
    (hx : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)),
      adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g.val x = x)
    (hy : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)),
      adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g.val y = y) :
    inner ℂ (adelicLocalNormalizedHecke f p (Fact.out : p.Prime) hpN x) y =
      inner ℂ x (adelicLocalNormalizedHecke f p (Fact.out : p.Prime) hpN y) :=
  adelicLocalNormalizedHecke_symmetric f hpN x y hx hy

/-- Exact original-object consumer of `adelicLocalBoundedHeckeTrace_norm_le`. -/
theorem actual_local_Hecke_bound_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N) (x : AdelicCyclicHilbert f) :
    ‖adelicLocalBoundedHeckeTrace f p hpN x‖ ≤ (p + 1 : ℝ) * ‖x‖ :=
  adelicLocalBoundedHeckeTrace_norm_le f p hpN x

/-- Exact original-object consumer of `adelicLocalFixedSpace_isClosed`. -/
theorem actual_local_fixed_space_closed_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : HeightOneSpectrum ℤ) :
    IsClosed (adelicLocalFixedSpace f v : Set (AdelicCyclicHilbert f)) :=
  adelicLocalFixedSpace_isClosed f v

/-- Exact original-object consumer of `adelicCyclicHilbertGenerator_mem_localFixed`. -/
theorem actual_local_fixed_generator_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : HeightOneSpectrum ℤ) :
    adelicCyclicHilbertGenerator f ∈ adelicLocalFixedSpace f v :=
  adelicCyclicHilbertGenerator_mem_localFixed f v

/-- Exact original-object consumer of `adelicLocalSphericalHecke_selfAdjoint`. -/
theorem actual_local_Hecke_self_adjoint_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N) :
    IsSelfAdjoint (adelicLocalSphericalHecke f p hpN) :=
  adelicLocalSphericalHecke_selfAdjoint f p hpN

/-- Exact original-object consumer of `adelicLocalSphericalHecke_primitive_generator`. -/
theorem actual_local_spherical_eigenvector_source {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N) :
    adelicLocalSphericalHecke F.toCuspForm p hpN
        (adelicLocalFixedGenerator F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
      normalizedCuspCoefficients F.toCuspForm p •
        adelicLocalFixedGenerator F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) :=
  adelicLocalSphericalHecke_primitive_generator F p hpN


/-- Exact original-object consumer of `rationalPrimePlaceInteger_unit_power`. -/
theorem actual_local_uniformizer_source (p : ℕ) (hp : p.Prime)
    (x : (rationalPrimePlace p hp).adicCompletionIntegers ℚ) (hx : x ≠ 0) :
    ∃ u : ((rationalPrimePlace p hp).adicCompletionIntegers ℚ)ˣ, ∃ n : ℕ,
      x = (u : (rationalPrimePlace p hp).adicCompletionIntegers ℚ) *
        (p : (rationalPrimePlace p hp).adicCompletionIntegers ℚ) ^ n :=
  rationalPrimePlaceInteger_unit_power p hp x hx

/-- Exact original-object consumer of `finitePlaceGL2_integral_pivot`. -/
theorem actual_local_integral_pivot_source (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    ∃ u : (v.adicCompletion ℚ)ˣ, ∃ l r : finitePlaceGL2Gamma0 1 v,
      (GeneralLinearGroup.scalar (Fin 2) u⁻¹ * (l.val * g * r.val)).val 0 0 = 1 ∧
      ∀ i j : Fin 2, (GeneralLinearGroup.scalar (Fin 2) u⁻¹ * (l.val * g * r.val)).val i j ∈
        v.adicCompletionIntegers ℚ :=
  finitePlaceGL2_integral_pivot v g

/-- Exact original-object consumer of `finitePlaceGL2_integral_diagonal`. -/
theorem actual_local_integral_diagonal_source (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    ∃ u t : (v.adicCompletion ℚ)ˣ, ∃ l r : finitePlaceGL2Gamma0 1 v,
      (t : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ ∧
      g = GeneralLinearGroup.scalar (Fin 2) u * l.val * gl2UnitDiagonalPair 1 t * r.val :=
  finitePlaceGL2_integral_diagonal v g

/-- Exact original-object consumer of `finitePlace_integral_diagonal_hecke_power`. -/
theorem actual_local_diagonal_Hecke_power_source (p : ℕ) [NeZero p] (hp : p.Prime)
    (t : ((rationalPrimePlace p hp).adicCompletion ℚ)ˣ)
    (ht : (t : (rationalPrimePlace p hp).adicCompletion ℚ) ∈ (rationalPrimePlace p hp).adicCompletionIntegers ℚ) :
    ∃ u : ((rationalPrimePlace p hp).adicCompletionIntegers ℚ)ˣ, ∃ n : ℕ,
      gl2UnitDiagonalPair 1 t =
        GeneralLinearGroup.map ((rationalPrimePlace p hp).adicCompletionIntegers ℚ).subtype
          (gl2UnitDiagonalPair 1 u) *
        (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp)) (finiteAdelicHeckeDiagonal p)) ^ n :=
  finitePlace_integral_diagonal_hecke_power p hp t ht

/-- Exact original-object consumer of `finitePlaceGL2_cartan`. -/
theorem actual_local_Cartan_source (p : ℕ) [NeZero p] (hp : p.Prime)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p hp).adicCompletion ℚ)) :
    ∃ u : ((rationalPrimePlace p hp).adicCompletion ℚ)ˣ, ∃ n : ℕ,
      ∃ l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p hp),
        g = GeneralLinearGroup.scalar (Fin 2) u * l.val *
          (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp)) (finiteAdelicHeckeDiagonal p)) ^ n * r.val :=
  finitePlaceGL2_cartan p hp g

/-- Exact original-object consumer of `adelicCyclicLocal_matrixCoefficient_cartan`. -/
theorem actual_local_Cartan_coefficient_source {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hpN : p.Coprime N)
    (x y : AdelicCyclicHilbert f)
    (hx : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)),
      adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g.val x = x)
    (hy : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)),
      adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g.val y = y)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    ∃ n : ℕ, inner ℂ x (adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g y) =
      inner ℂ x (adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime))
        ((GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
          (finiteAdelicHeckeDiagonal p)) ^ n) y) :=
  adelicCyclicLocal_matrixCoefficient_cartan f hpN x y hx hy g


/-- Exact original-object consumer of `finitePlaceGL2_unit_entry_hecke_power`. -/
theorem actual_local_exact_double_coset_source (p : ℕ) [NeZero p] (hp : p.Prime)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p hp).adicCompletion ℚ))
    (hint : ∀ i j, g.val i j ∈ (rationalPrimePlace p hp).adicCompletionIntegers ℚ)
    (i j : Fin 2) (a b : ((rationalPrimePlace p hp).adicCompletionIntegers ℚ)ˣ)
    (ha : g.val i j = (a.val : (rationalPrimePlace p hp).adicCompletion ℚ))
    (m : ℕ)
    (hdet : GeneralLinearGroup.det g =
      Units.map ((rationalPrimePlace p hp).adicCompletionIntegers ℚ).subtype.toMonoidHom b *
        (finitePlacePrimeUnit p (rationalPrimePlace p hp)) ^ m) :
    ∃ l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p hp),
      g = l.val * (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
        (finiteAdelicHeckeDiagonal p)) ^ m * r.val :=
  finitePlaceGL2_unit_entry_hecke_power p hp g hint i j a b ha m hdet

/-- Exact original-object consumer of `finitePlaceHeckeRadial_some_forward`. -/
theorem actual_local_radial_forward_source (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) (n : ℕ) (a : ZMod p) (ha : a ≠ 0) :
    ∃ l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)),
      finitePlaceHeckeRadialMatrix N p hpN (rationalPrimePlace p (Fact.out : p.Prime)) n (some a) =
        l.val * (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
          (finiteAdelicHeckeDiagonal p)) ^ (n + 1) * r.val :=
  finitePlaceHeckeRadial_some_forward N p hpN n a ha

/-- Exact original-object consumer of `adelicLocalHeckeTrace_primitive_generator`. -/
theorem actual_local_radial_trace_eigen_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    @finitePlaceHeckeTrace (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance N p
      inferInstance inferInstance inferInstance hpN
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicCyclicHilbertGenerator F.toCuspForm) =
    ((Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p) •
      adelicCyclicHilbertGenerator F.toCuspForm :=
  adelicLocalHeckeTrace_primitive_generator F hpN

/-- Exact original-object consumer of `adelicCyclicLocal_primitive_radial_recurrence`. -/
theorem actual_local_radial_recurrence_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    let φ := @finitePlaceRadialCoefficient (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance p inferInstance inferInstance
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      x (adelicCyclicHilbertGenerator F.toCuspForm)
    let μ := (Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p
    μ * φ 0 = ((p : ℂ) + 1) * φ 1 ∧
      ∀ n, μ * φ (n + 1) = φ n + (p : ℂ) * φ (n + 2) :=
  adelicCyclicLocal_primitive_radial_recurrence F hpN x hx

/-- Exact original-object consumer of `adelicCyclicLocal_orbit_orthogonal_zero`. -/
theorem actual_local_orbit_orthogonal_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (horth : inner ℂ x (adelicCyclicHilbertGenerator F.toCuspForm) = 0)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    inner ℂ x (adelicCyclicLocalRepresentation F.toCuspForm
      (rationalPrimePlace p (Fact.out : p.Prime)) g (adelicCyclicHilbertGenerator F.toCuspForm)) = 0 :=
  adelicCyclicLocal_orbit_orthogonal_zero F hpN x hx horth g

/-- Exact original-object consumer of `adelicLocalCyclic_fixed_eq_generator_line`. -/
theorem actual_local_cyclic_fixed_line_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊓
      adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) =
        Submodule.span ℂ {adelicCyclicHilbertGenerator F.toCuspForm} :=
  adelicLocalCyclic_fixed_eq_generator_line F hpN

/-- Exact original-object consumer of `adelicLocalCyclic_intertwiner_scalar`. -/
theorem actual_local_cyclic_Schur_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (T : AdelicCyclicHilbert F.toCuspForm →L[ℂ] AdelicCyclicHilbert F.toCuspForm)
    (hT : ∀ g x, T (adelicCyclicLocalRepresentation F.toCuspForm
      (rationalPrimePlace p (Fact.out : p.Prime)) g x) =
        adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g (T x))
    (hcyclic : T (adelicCyclicHilbertGenerator F.toCuspForm) ∈
      adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    ∃ c : ℂ, ∀ x ∈ adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)),
      T x = c • x :=
  adelicLocalCyclic_intertwiner_scalar F hpN T hT hcyclic

/-- Exact original-object consumer of `adelicLocalCyclicClosedSpan_irreducible`. -/
theorem actual_local_cyclic_irreducible_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (S : Submodule ℂ (AdelicCyclicHilbert F.toCuspForm))
    (hclosed : IsClosed (S : Set (AdelicCyclicHilbert F.toCuspForm)))
    (hle : S ≤ adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (hinv : ∀ g x, x ∈ S → adelicCyclicLocalRepresentation F.toCuspForm
      (rationalPrimePlace p (Fact.out : p.Prime)) g x ∈ S) :
    S = ⊥ ∨ S = adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) :=
  adelicLocalCyclicClosedSpan_irreducible F hpN S hclosed hle hinv


/-- Exact original-object consumer of genuine local compactness and openness. -/
theorem actual_local_level_topology_source (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ) :
    IsCompact (finitePlaceGL2Gamma0 N v : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) ∧
      IsOpen (finitePlaceGL2Gamma0 N v : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) :=
  ⟨finitePlaceGL2Gamma0_isCompact N v, finitePlaceGL2Gamma0_isOpen N v⟩

/-- Exact original-object consumer of `adelicLocalCyclicCore_smooth`. -/
theorem actual_local_smooth_core_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : HeightOneSpectrum ℤ)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalCyclicCore f v) :
    ∃ H : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)),
      IsOpen (H : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) ∧
        ∀ g ∈ H, adelicCyclicLocalRepresentation f v g x = x :=
  adelicLocalCyclicCore_smooth f v x hx

/-- Exact original-object consumer of `adelicLocalFixedProjection_mem_invariantCore`. -/
theorem actual_local_core_projection_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : HeightOneSpectrum ℤ)
    (W : Submodule ℂ (AdelicCyclicHilbert f)) (hW : W ≤ adelicLocalCyclicCore f v)
    (hinv : ∀ g x, x ∈ W → adelicCyclicLocalRepresentation f v g x ∈ W)
    (x : AdelicCyclicHilbert f) (hx : x ∈ W) : adelicLocalFixedProjection f v x ∈ W :=
  adelicLocalFixedProjection_mem_invariantCore f v W hW hinv x hx

/-- Exact original-object consumer of `adelicLocalCyclicCore_irreducible`. -/
theorem actual_local_algebraic_irreducible_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (W : Submodule ℂ (AdelicCyclicHilbert F.toCuspForm))
    (hW : W ≤ adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (hinv : ∀ g x, x ∈ W → adelicCyclicLocalRepresentation F.toCuspForm
      (rationalPrimePlace p (Fact.out : p.Prime)) g x ∈ W) :
    W = ⊥ ∨ W = adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) :=
  adelicLocalCyclicCore_irreducible F hpN W hW hinv

/-- Exact original-object consumer of `adelicLocalSmoothRepresentation_smooth`. -/
theorem actual_local_smooth_representation_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : HeightOneSpectrum ℤ) (x : adelicLocalCyclicCore f v) :
    ∃ H : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)),
      IsOpen (H : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) ∧
        ∀ g ∈ H, adelicLocalSmoothRepresentation f v g x = x :=
  adelicLocalSmoothRepresentation_smooth f v x

/-- Exact original-object consumer of `adelicLocalSmoothRepresentation_irreducible`. -/
theorem actual_local_smooth_irreducible_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    (adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).IsIrreducible :=
  adelicLocalSmoothRepresentation_irreducible F hpN


/-- Exact original-object consumer of `finiteAdelicSublevelIntegerGroup_finiteIndex`. -/
theorem actual_sublevel_integer_finite_source (N : ℕ) [NeZero N]
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) [L.FiniteIndex] :
    (finiteAdelicSublevelIntegerGroup N L).FiniteIndex :=
  finiteAdelicSublevelIntegerGroup_finiteIndex N L

/-- Exact original-object consumer of `adelicSublevelClassicalFamily_injective`. -/
theorem actual_sublevel_classical_family_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (L : Subgroup (finiteAdeleGL2Gamma0 N)) :
    Function.Injective (adelicSublevelClassicalFamily f L) :=
  adelicSublevelClassicalFamily_injective f L

/-- Exact original-object consumer of `adelicSublevelFixedLowest_finiteDimensional`. -/
theorem actual_sublevel_lowest_finite_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k)
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) (hL : IsOpen (L : Set (finiteAdeleGL2Gamma0 N))) :
    FiniteDimensional ℂ ↥(adelicRotationWeightSpace f ⊓ adelicSublevelFixedSpace f L :
      Submodule ℂ (AdelicCyclicHilbert f)) :=
  adelicSublevelFixedLowest_finiteDimensional f hf hk L hL

/-- Exact original-object consumer of `adelicLocalCyclic_level_action`. -/
theorem actual_local_sublevel_action_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : HeightOneSpectrum ℤ) (a : finiteAdeleGL2Gamma0 N)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalCyclicClosedSpan f v) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val) x =
      adelicCyclicLocalRepresentation f v (GeneralLinearGroup.map (finiteAdelePlace v) a.val) x :=
  adelicLocalCyclic_level_action f v a x hx

/-- Exact original-object consumer of `adelicLocalCyclic_open_fixed_finiteDimensional`. -/
theorem actual_local_open_fixed_finite_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k)
    (v : HeightOneSpectrum ℤ) (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))) :
    FiniteDimensional ℂ ↥(adelicLocalCyclicClosedSpan f v ⊓ adelicLocalSubgroupFixedSpace f v J :
      Submodule ℂ (AdelicCyclicHilbert f)) :=
  adelicLocalCyclic_open_fixed_finiteDimensional f hf hk v J hJ

/-- Exact original-object consumer of `adelicLocalCyclic_smooth_iff_core`. -/
theorem actual_local_smooth_completion_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k)
    (v : HeightOneSpectrum ℤ) (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalCyclicClosedSpan f v) :
    (∃ J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)),
      IsOpen (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) ∧
        ∀ g ∈ J, adelicCyclicLocalRepresentation f v g x = x) ↔ x ∈ adelicLocalCyclicCore f v :=
  adelicLocalCyclic_smooth_iff_core f hf hk v x hx

/-- Exact original-object consumer of `adelicLocalSmoothRepresentation_admissible`. -/
theorem actual_local_smooth_admissible_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k)
    (v : HeightOneSpectrum ℤ) (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))) :
    FiniteDimensional ℂ (Representation.invariants ((adelicLocalSmoothRepresentation f v).comp J.subtype)) :=
  adelicLocalSmoothRepresentation_admissible f hf hk v J hJ

/-- Exact original-object consumer of `adelicLocalCyclicRepresentation_admissible`. -/
theorem actual_local_cyclic_admissible_source {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k)
    (v : HeightOneSpectrum ℤ) (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))) :
    FiniteDimensional ℂ (Representation.invariants ((adelicLocalCyclicRepresentation f v).comp J.subtype)) :=
  adelicLocalCyclicRepresentation_admissible f hf hk v J hJ

/-- Exact primitive source consumer combining genuine good-prime smooth irreducibility and proved admissibility of the original local representation. -/
theorem actual_primitive_local_admissible_irreducible_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (hpN : p.Coprime N) :
    (adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).IsIrreducible ∧
      ∀ J : Subgroup (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)),
        IsOpen (J : Set (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))) →
          FiniteDimensional ℂ (Representation.invariants
            ((adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).comp J.subtype)) :=
  ⟨adelicLocalSmoothRepresentation_irreducible F hpN,
    fun J hJ => adelicLocalSmoothRepresentation_admissible F.toCuspForm (primitiveCuspForm_ne_zero F) hk _ J hJ⟩


open scoped TensorProduct

/-- Exact original-object consumer of `adelicLocalCyclicProjection_fixed_scalar`. -/
theorem actual_local_cyclic_projection_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    ∃ c : ℂ, adelicLocalCyclicProjection F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) x =
      c • adelicCyclicHilbertGenerator F.toCuspForm :=
  adelicLocalCyclicProjection_fixed_scalar F hpN x hx

/-- Exact original-object consumer of `adelicCyclicLocal_away_mixed_gram`. -/
theorem actual_local_away_gram_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g₁ g₂ : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (a₁ a₂ : finiteAdelicAwayGroup (rationalPrimePlace p (Fact.out : p.Prime))) :
    inner ℂ
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₁
        (adelicCyclicAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₁
          (adelicCyclicHilbertGenerator F.toCuspForm)))
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₂
        (adelicCyclicAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₂
          (adelicCyclicHilbertGenerator F.toCuspForm))) *
      inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm) (adelicCyclicHilbertGenerator F.toCuspForm) =
    inner ℂ
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₁
        (adelicCyclicHilbertGenerator F.toCuspForm))
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₂
        (adelicCyclicHilbertGenerator F.toCuspForm)) *
    inner ℂ
      (adelicCyclicAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₁
        (adelicCyclicHilbertGenerator F.toCuspForm))
      (adelicCyclicAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₂
        (adelicCyclicHilbertGenerator F.toCuspForm)) :=
  adelicCyclicLocal_away_mixed_gram F hpN g₁ g₂ a₁ a₂

/-- Exact original-object consumer of `finiteAdelicLocalAwayEquiv_apply`. -/
theorem actual_finite_local_away_product_source  (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (a : finiteAdelicAwayGroup v) :
    finiteAdelicLocalAwayEquiv v (g, a) = finiteAdelicLocalGL2 v g * a.val :=
  finiteAdelicLocalAwayEquiv_apply v g a

/-- Exact original-object consumer of `adelicLocalAwayTensorIsometry_range`. -/
theorem actual_local_away_tensor_range_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    (adelicLocalAwayTensorIsometry F hpN).toLinearMap.range = adelicFiniteCyclicSpan F.toCuspForm :=
  adelicLocalAwayTensorIsometry_range F hpN

/-- Exact original-object consumer of `adelicLocalAwayTensorIsometry_intertwines`. -/
theorem actual_local_away_tensor_action_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (b : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      finiteAdelicAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (x : adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalAwayTensorIsometry F hpN
      (adelicLocalAwayTensorRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b x) =
      adelicLocalAwayJointRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b
        (adelicLocalAwayTensorIsometry F hpN x) :=
  adelicLocalAwayTensorIsometry_intertwines F hpN b x

/-- Exact original-object consumer of `adelicLocalAwayHilbertTensorIsometry_range`. -/
theorem actual_local_away_completed_range_source {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) (hk : 0 < k) :
    (adelicLocalAwayHilbertTensorIsometry F hpN).toLinearMap.range =
      adelicRotationWeightSpace F.toCuspForm :=
  adelicLocalAwayHilbertTensorIsometry_range F hpN hk

/-- Exact original-object consumer of `adelicLocalAwayHilbertTensorIsometry_intertwines`. -/
theorem actual_local_away_completed_action_source {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (b : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      finiteAdelicAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (x : AdelicLocalAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalAwayHilbertTensorIsometry F hpN (adelicLocalAwayHilbertTensorRepresentation F hpN b x) =
      adelicLocalAwayJointRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b
        (adelicLocalAwayHilbertTensorIsometry F hpN x) :=
  adelicLocalAwayHilbertTensorIsometry_intertwines F hpN b x

/-- Exact original-object consumer of `adelicLocalAwayHilbertTensorEquiv_apply`. -/
theorem actual_local_away_completed_equiv_source {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) (hk : 0 < k)
    (x : AdelicLocalAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    (adelicLocalAwayHilbertTensorEquiv F hpN hk x).val = adelicLocalAwayHilbertTensorIsometry F hpN x :=
  adelicLocalAwayHilbertTensorEquiv_apply F hpN hk x

/-- The actual completed local-away tensor equivalence reaches every original lowest-weight Hilbert vector. -/
theorem actual_local_away_completed_onto_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) (hk : 0 < k) :
    Function.Surjective (adelicLocalAwayHilbertTensorEquiv F hpN hk) :=
  (adelicLocalAwayHilbertTensorEquiv F hpN hk).surjective


/-- Exact original-object consumer of `adelicLocalFullAwayEquiv_coordinates`. -/
theorem actual_full_local_coordinates_source  (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (a : AdelicFullAwayGroup v) :
    rationalAdelicGL2RealFiniteEquiv (adelicLocalFullAwayEquiv v (g, a)) =
      (a.1, finiteAdelicLocalGL2 v g * a.2.val) :=
  adelicLocalFullAwayEquiv_coordinates v g a

/-- Exact original-object consumer of `adelicCyclicLocal_fullAway_mixed_gram`. -/
theorem actual_full_local_gram_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g₁ g₂ : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (a₁ a₂ : AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime))) :
    inner ℂ
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₁
        (adelicCyclicFullAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₁
          (adelicCyclicHilbertGenerator F.toCuspForm)))
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₂
        (adelicCyclicFullAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₂
          (adelicCyclicHilbertGenerator F.toCuspForm))) *
      inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm) (adelicCyclicHilbertGenerator F.toCuspForm) =
    inner ℂ
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₁
        (adelicCyclicHilbertGenerator F.toCuspForm))
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₂
        (adelicCyclicHilbertGenerator F.toCuspForm)) *
    inner ℂ
      (adelicCyclicFullAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₁
        (adelicCyclicHilbertGenerator F.toCuspForm))
      (adelicCyclicFullAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₂
        (adelicCyclicHilbertGenerator F.toCuspForm)) :=
  adelicCyclicLocal_fullAway_mixed_gram F hpN g₁ g₂ a₁ a₂

/-- Exact original-object consumer of `adelicLocalFullAwayTensorIsometry_range`. -/
theorem actual_full_local_tensor_range_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    (adelicLocalFullAwayTensorIsometry F hpN).toLinearMap.range =
      Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
        adelicCyclicHilbertRepresentation F.toCuspForm g (adelicCyclicHilbertGenerator F.toCuspForm))) :=
  adelicLocalFullAwayTensorIsometry_range F hpN

/-- Exact original-object consumer of `adelicLocalFullAwayTensorIsometry_intertwines`. -/
theorem actual_full_local_tensor_action_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (b : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (x : adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalFullAwayTensorIsometry F hpN
      (adelicLocalFullAwayTensorRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b x) =
      adelicLocalFullAwayJointRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b
        (adelicLocalFullAwayTensorIsometry F hpN x) :=
  adelicLocalFullAwayTensorIsometry_intertwines F hpN b x

/-- Exact original-object consumer of `adelicLocalFullAwayHilbertTensorIsometry_range`. -/
theorem actual_full_local_completed_range_source {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    (adelicLocalFullAwayHilbertTensorIsometry F hpN).toLinearMap.range =
      ⊤ :=
  adelicLocalFullAwayHilbertTensorIsometry_range F hpN

/-- Exact original-object consumer of `adelicLocalFullAwayHilbertTensorIsometry_intertwines`. -/
theorem actual_full_local_completed_action_source {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (b : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (x : AdelicLocalFullAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalFullAwayHilbertTensorIsometry F hpN (adelicLocalFullAwayHilbertTensorRepresentation F hpN b x) =
      adelicLocalFullAwayJointRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b
        (adelicLocalFullAwayHilbertTensorIsometry F hpN x) :=
  adelicLocalFullAwayHilbertTensorIsometry_intertwines F hpN b x

/-- Exact original-object consumer of `adelicLocalFullAwayHilbertTensorRepresentation_stronglyContinuous`. -/
theorem actual_full_local_completed_continuity_source {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicLocalFullAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    Continuous (fun b => adelicLocalFullAwayHilbertTensorRepresentation F hpN b x) :=
  adelicLocalFullAwayHilbertTensorRepresentation_stronglyContinuous F hpN x

/-- The genuine full local-complement Hilbert tensor equivalence reaches every vector of the original full adelic Hilbert representation. -/
theorem actual_full_local_completed_onto_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    Function.Surjective (adelicLocalFullAwayHilbertTensorEquiv F hpN) :=
  (adelicLocalFullAwayHilbertTensorEquiv F hpN).surjective


/-- Exact original-object consumer of `adelicFullAwayEmbedding_of_place_one`. -/
theorem actual_full_place_complement_source  (v : HeightOneSpectrum ℤ)
    (a : RationalAdelicGL2) (ha : adelicPlaceGL2Hom v a = 1) :
    ∃ b : AdelicFullAwayGroup v, adelicFullAwayEmbedding v b = a :=
  adelicFullAwayEmbedding_of_place_one v a ha

/-- Exact original-object consumer of `adelicNormalizedCuspCoefficient_local_mul`. -/
theorem actual_normalized_local_product_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (a : RationalAdelicGL2) (ha : adelicPlaceGL2Hom (rationalPrimePlace p (Fact.out : p.Prime)) a = 1) :
    adelicNormalizedCuspCoefficient F.toCuspForm
      (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (rationalPrimePlace p (Fact.out : p.Prime)) g) * a) =
      adelicNormalizedCuspCoefficient F.toCuspForm
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (rationalPrimePlace p (Fact.out : p.Prime)) g)) *
      adelicNormalizedCuspCoefficient F.toCuspForm a :=
  adelicNormalizedCuspCoefficient_local_mul F hpN g a ha

/-- Exact original-object consumer of `adelicNormalizedCuspCoefficient_distinct_place_product`. -/
theorem actual_normalized_distinct_product_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (l : List AdelicPlaceMatrix)
    (hgood : ∀ a ∈ l, IsGoodAdelicPlace N a.1)
    (hdistinct : l.Pairwise (fun a b => a.1 ≠ b.1)) :
    adelicNormalizedCuspCoefficient F.toCuspForm (l.map adelicPlaceMatrixEmbedding).prod =
      (l.map (fun a => adelicNormalizedCuspCoefficient F.toCuspForm (adelicPlaceMatrixEmbedding a))).prod :=
  adelicNormalizedCuspCoefficient_distinct_place_product F l hgood hdistinct

/-- Exact original-object consumer of `adelicLocalFullAwayEquiv_symm_continuous`. -/
theorem actual_full_factor_inverse_continuity_source  (v : HeightOneSpectrum ℤ) :
    Continuous (adelicLocalFullAwayEquiv v).symm :=
  adelicLocalFullAwayEquiv_symm_continuous v

/-- Exact original-object consumer of `adelicPlaceGL2Hom_finitePlaceProduct`. -/
theorem actual_finite_place_evaluation_source {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v) (i : I)
    (g : ∀ j, GeneralLinearGroup (Fin 2) ((v j).adicCompletion ℚ)) :
    adelicPlaceGL2Hom (v i) (adelicFinitePlaceProduct v hv g) = g i :=
  adelicPlaceGL2Hom_finitePlaceProduct v hv i g

/-- Exact original-object consumer of `adelicFinitePlaceProduct_injective`. -/
theorem actual_finite_place_product_faithful_source {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v) : Function.Injective (adelicFinitePlaceProduct v hv) :=
  adelicFinitePlaceProduct_injective v hv

/-- Exact original-object consumer of `adelicFinitePlaceProduct_mul_removal`. -/
theorem actual_finite_place_remainder_source {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v) (a : RationalAdelicGL2) :
    adelicFinitePlaceProduct v hv (fun i => adelicPlaceGL2Hom (v i) a) * adelicFinitePlaceRemoval v hv a = a :=
  adelicFinitePlaceProduct_mul_removal v hv a

/-- The actual finite-local-family and full-complement coordinate map is a genuine bijection onto original full adelic GL2. -/
theorem actual_finite_family_group_factor_source {I : Type*} [Fintype I]
    (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v) :
    Function.Bijective (adelicFiniteFamilyEquiv v hv) :=
  (adelicFiniteFamilyEquiv v hv).bijective


/-- Exact original-object consumer of `adelicNormalizedCuspCoefficient_distinct_place_product_mul`. -/
theorem actual_normalized_full_complement_product_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (l : List AdelicPlaceMatrix)
    (hgood : ∀ x ∈ l, IsGoodAdelicPlace N x.1)
    (hdistinct : l.Pairwise (fun x y => x.1 ≠ y.1))
    (a : RationalAdelicGL2) (ha : ∀ x ∈ l, adelicPlaceGL2Hom x.1 a = 1) :
    adelicNormalizedCuspCoefficient F.toCuspForm ((l.map adelicPlaceMatrixEmbedding).prod * a) =
      (l.map (fun x => adelicNormalizedCuspCoefficient F.toCuspForm (adelicPlaceMatrixEmbedding x))).prod *
        adelicNormalizedCuspCoefficient F.toCuspForm a :=
  adelicNormalizedCuspCoefficient_distinct_place_product_mul F l hgood hdistinct a ha

/-- Exact original-object consumer of `adelicCyclicUnitReference_norm`. -/
theorem actual_cusp_unit_reference_norm_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) : ‖adelicCyclicUnitReference f‖ = 1 :=
  adelicCyclicUnitReference_norm f hf

/-- Exact original-object consumer of `adelicCyclicUnitReference_coefficient`. -/
theorem actual_unit_reference_coefficient_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : RationalAdelicGL2) :
    inner ℂ (adelicCyclicUnitReference f)
      (adelicCyclicHilbertRepresentation f a (adelicCyclicUnitReference f)) =
        adelicNormalizedCuspCoefficient f a :=
  adelicCyclicUnitReference_coefficient f a

/-- Exact original-object consumer of `adelicLocalFullAwayTensorIsometry_unit_reference`. -/
theorem actual_tensor_unit_reference_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    adelicLocalFullAwayTensorIsometry F hpN
      (adelicLocalUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗ₜ[ℂ]
        adelicFullAwayUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
      adelicCyclicUnitReference F.toCuspForm :=
  adelicLocalFullAwayTensorIsometry_unit_reference F hpN

/-- Exact original-object consumer of `adelicLocalFullAwayTensorIsometry_right_reference`. -/
theorem actual_tensor_local_reference_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime] (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalFullAwayTensorIsometry F hpN
      (x ⊗ₜ[ℂ] adelicFullAwayUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
        x.val :=
  adelicLocalFullAwayTensorIsometry_right_reference F hpN x

/-- Exact original-object consumer of `adelicLocalFullAwayTensorIsometry_left_reference`. -/
theorem actual_tensor_complement_reference_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime] (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalFullAwayTensorIsometry F hpN
      (adelicLocalUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗ₜ[ℂ] x) =
        x.val :=
  adelicLocalFullAwayTensorIsometry_left_reference F hpN x

/-- Exact original-object consumer of `adelicLocalFullAwayHilbertTensorIsometry_right_reference`. -/
theorem actual_completed_tensor_local_reference_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime] (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : UniformSpace.Completion (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) :
    adelicLocalFullAwayHilbertTensorIsometry F hpN
      (adelicLocalReferenceCompletionInclusion F.toCuspForm (primitiveCuspForm_ne_zero F)
        (rationalPrimePlace p (Fact.out : p.Prime)) x) =
      @linearIsometryCompletion
        (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
        (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance inferInstance
        (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).subtypeₗᵢ x :=
  adelicLocalFullAwayHilbertTensorIsometry_right_reference F hpN x

/-- Exact original-object consumer of `adelicLocalFullAwayHilbertTensorIsometry_left_reference`. -/
theorem actual_completed_tensor_complement_reference_source {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime] (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : UniformSpace.Completion (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) :
    adelicLocalFullAwayHilbertTensorIsometry F hpN
      (adelicFullAwayReferenceCompletionInclusion F.toCuspForm (primitiveCuspForm_ne_zero F)
        (rationalPrimePlace p (Fact.out : p.Prime)) x) =
      @linearIsometryCompletion
        (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
        (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance inferInstance
        (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).subtypeₗᵢ x :=
  adelicLocalFullAwayHilbertTensorIsometry_left_reference F hpN x


/-- Exact original-object consumer of `adelicNormalizedCuspCoefficient_finiteFamilyEquiv`. -/
theorem actual_finite_tuple_coefficient_source {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v) {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicNormalizedCuspCoefficient F.toCuspForm (adelicFiniteFamilyEquiv v hv b) =
      (∏ i, adelicNormalizedCuspCoefficient F.toCuspForm
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (b.1 i)))) *
      adelicNormalizedCuspCoefficient F.toCuspForm b.2.val :=
  adelicNormalizedCuspCoefficient_finiteFamilyEquiv v hv F hgood b

/-- Exact original-object consumer of `adelicCyclicUnitReference_finiteFamily_gram`. -/
theorem actual_finite_tuple_gram_source {N : ℕ} [NeZero N] {k : ℤ} {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v) (F : PrimitiveCuspForm N k)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b₁ b₂ : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    inner ℂ
      (adelicCyclicHilbertRepresentation F.toCuspForm (adelicFiniteFamilyEquiv v hv b₁)
        (adelicCyclicUnitReference F.toCuspForm))
      (adelicCyclicHilbertRepresentation F.toCuspForm (adelicFiniteFamilyEquiv v hv b₂)
        (adelicCyclicUnitReference F.toCuspForm)) =
      (∏ i, inner ℂ
        (adelicCyclicHilbertRepresentation F.toCuspForm
          (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (b₁.1 i)))
          (adelicCyclicUnitReference F.toCuspForm))
        (adelicCyclicHilbertRepresentation F.toCuspForm
          (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (b₂.1 i)))
          (adelicCyclicUnitReference F.toCuspForm))) *
      inner ℂ
        (adelicCyclicHilbertRepresentation F.toCuspForm b₁.2.val (adelicCyclicUnitReference F.toCuspForm))
        (adelicCyclicHilbertRepresentation F.toCuspForm b₂.2.val (adelicCyclicUnitReference F.toCuspForm)) :=
  adelicCyclicUnitReference_finiteFamily_gram v hv F hgood b₁ b₂

/-- Exact original-object consumer of `adelicFiniteFamilyEquiv_symm_continuous`. -/
theorem actual_finite_family_inverse_topology_source {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v) : Continuous (adelicFiniteFamilyEquiv v hv).symm :=
  adelicFiniteFamilyEquiv_symm_continuous v hv

/-- Exact original-object consumer of `adelicLocalUnitOrbit_span`. -/
theorem actual_original_unit_local_orbit_span_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (v : HeightOneSpectrum ℤ) :
    Submodule.span ℂ (Set.range (adelicLocalUnitOrbit f v)) = ⊤ :=
  adelicLocalUnitOrbit_span f hf v

/-- Exact original-object consumer of `adelicFiniteLocalTensorFamily_span`. -/
theorem actual_finite_local_tensor_orbit_span_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (hf : f ≠ 0) :
    Submodule.span ℂ (Set.range (adelicFiniteLocalTensorFamily f v)) = ⊤ :=
  adelicFiniteLocalTensorFamily_span f v hf

/-- Exact original-object consumer of `adelicFiniteFullTensorFamily_gram`. -/
theorem actual_finite_hilbert_tensor_gram_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (a b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    inner ℂ (adelicFiniteFullTensorFamily F.toCuspForm v a) (adelicFiniteFullTensorFamily F.toCuspForm v b) =
      inner ℂ (adelicFiniteFullMixedFamily F.toCuspForm v hv a) (adelicFiniteFullMixedFamily F.toCuspForm v hv b) :=
  adelicFiniteFullTensorFamily_gram F v hv hgood a b

/-- Exact original-object consumer of `adelicFiniteFullTensorIsometry_family`. -/
theorem actual_finite_hilbert_tensor_family_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFullTensorIsometry F v hv hgood (adelicFiniteFullTensorFamily F.toCuspForm v a) =
      adelicFiniteFullMixedFamily F.toCuspForm v hv a :=
  adelicFiniteFullTensorIsometry_family F v hv hgood a

/-- Exact original-object consumer of `adelicFiniteFullTensorIsometry_range`. -/
theorem actual_finite_hilbert_tensor_range_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    (adelicFiniteFullTensorIsometry F v hv hgood).toLinearMap.range =
      Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
        adelicCyclicHilbertRepresentation F.toCuspForm g (adelicCyclicHilbertGenerator F.toCuspForm))) :=
  adelicFiniteFullTensorIsometry_range F v hv hgood

/-- Exact original-object consumer of `adelicFiniteFullHilbertTensorIsometry_family`. -/
theorem actual_completed_finite_tensor_family_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFullHilbertTensorIsometry F v hv hgood
      (adelicFiniteFullTensorFamily F.toCuspForm v a : AdelicFiniteFullHilbertTensor F.toCuspForm v) =
      adelicFiniteFullMixedFamily F.toCuspForm v hv a :=
  adelicFiniteFullHilbertTensorIsometry_family F v hv hgood a

/-- Exact original-object consumer of `adelicFiniteFullHilbertTensorIsometry_range`. -/
theorem actual_completed_finite_tensor_range_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    (adelicFiniteFullHilbertTensorIsometry F v hv hgood).toLinearMap.range = ⊤ :=
  adelicFiniteFullHilbertTensorIsometry_range F v hv hgood


/-- Exact original-object consumer of `adelicFiniteFullTensorIsometry_intertwines`. -/
theorem actual_finite_tensor_intertwining_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (F : PrimitiveCuspForm N k) (hv : Function.Injective v)  (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
    (x : AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v) :
    adelicFiniteFullTensorIsometry F v hv hgood (adelicFiniteFullTensorRepresentation F.toCuspForm v b x) =
      adelicFiniteFullJointRepresentation F.toCuspForm v hv b (adelicFiniteFullTensorIsometry F v hv hgood x)  :=
  adelicFiniteFullTensorIsometry_intertwines v F hv hgood b x

/-- Exact original-object consumer of `adelicFiniteFullTensorRepresentation_norm`. -/
theorem actual_finite_tensor_norm_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ)  (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
    (x : AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v) :
    ‖adelicFiniteFullTensorRepresentation F.toCuspForm v b x‖ = ‖x‖  :=
  adelicFiniteFullTensorRepresentation_norm F v hv hgood b x

/-- Exact original-object consumer of `adelicFiniteFullHilbertTensorIsometry_intertwines`. -/
theorem actual_completed_finite_tensor_intertwining_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ)  (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
    (x : AdelicFiniteFullHilbertTensor F.toCuspForm v) :
    adelicFiniteFullHilbertTensorIsometry F v hv hgood
      (adelicFiniteFullHilbertTensorRepresentation F v hv hgood b x) =
      adelicFiniteFullJointRepresentation F.toCuspForm v hv b
        (adelicFiniteFullHilbertTensorIsometry F v hv hgood x)  :=
  adelicFiniteFullHilbertTensorIsometry_intertwines F v hv hgood b x

/-- Exact original-object consumer of `adelicFiniteFullHilbertTensorRepresentation_stronglyContinuous`. -/
theorem actual_completed_finite_tensor_continuity_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ)  (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (x : AdelicFiniteFullHilbertTensor F.toCuspForm v) :
    Continuous (fun b => adelicFiniteFullHilbertTensorRepresentation F v hv hgood b x)  :=
  adelicFiniteFullHilbertTensorRepresentation_stronglyContinuous F v hv hgood x

/-- Exact original-object consumer of `adelicFiniteFamilyEquiv_reindex`. -/
theorem actual_finite_adelic_permutation_source {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (e : Equiv.Perm (Fin n))  (hv : Function.Injective v)
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ))
    (a : adelicFiniteFamilyAwayGroup (fun i => v (e i))) :
    adelicFiniteFamilyEquiv (fun i => v (e i)) (hv.comp e.injective) ((fun i => g (e i)), a) =
      adelicFiniteFamilyEquiv v hv (g, adelicFiniteFamilyAwayReindex v e a)  :=
  adelicFiniteFamilyEquiv_reindex v e hv g a

/-- Exact original-object consumer of `adelicFiniteFamilyAwayCore_reindex`. -/
theorem actual_finite_complement_core_permutation_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin n → HeightOneSpectrum ℤ) (e : Equiv.Perm (Fin n))  :
    adelicFiniteFamilyAwayCore f (fun i => v (e i)) = adelicFiniteFamilyAwayCore f v  :=
  adelicFiniteFamilyAwayCore_reindex f v e

/-- Exact original-object consumer of `adelicFiniteFullTensorIsometry_reindex`. -/
theorem actual_finite_tensor_permutation_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (e : Equiv.Perm (Fin n)) (F : PrimitiveCuspForm N k)  (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (x : AdelicFiniteLocalTensor F.toCuspForm (fun i => v (e i)) ⊗[ℂ]
      adelicFiniteFamilyAwayCore F.toCuspForm (fun i => v (e i))) :
    adelicFiniteFullTensorIsometry F v hv hgood (adelicFiniteFullTensorReindex F.toCuspForm v e x) =
      adelicFiniteFullTensorIsometry F (fun i => v (e i)) (hv.comp e.injective) (fun i => hgood (e i)) x  :=
  adelicFiniteFullTensorIsometry_reindex v e F hv hgood x

/-- Exact original-object consumer of `adelicFiniteFullHilbertTensorIsometry_reindex`. -/
theorem actual_completed_finite_tensor_permutation_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (e : Equiv.Perm (Fin n)) (F : PrimitiveCuspForm N k)  (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (x : AdelicFiniteFullHilbertTensor F.toCuspForm (fun i => v (e i))) :
    adelicFiniteFullHilbertTensorIsometry F v hv hgood (adelicFiniteFullHilbertTensorReindex F.toCuspForm v e x) =
      adelicFiniteFullHilbertTensorIsometry F (fun i => v (e i)) (hv.comp e.injective) (fun i => hgood (e i)) x  :=
  adelicFiniteFullHilbertTensorIsometry_reindex v e F hv hgood x


/-- Exact original-object consumer of `adelicFinitePlaceProduct_snoc_one`. -/
theorem actual_finite_reference_coordinate_source  {n : ℕ} (v : Fin (n + 1) → HeightOneSpectrum ℤ)
    (hv : Function.Injective v)
    (g : ∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v i.castSucc).adicCompletion ℚ)) :
    adelicFinitePlaceProduct v hv (Fin.snoc g 1) =
      adelicFinitePlaceProduct (fun i : Fin n => v i.castSucc) (hv.comp (Fin.castSucc_injective n)) g  :=
  adelicFinitePlaceProduct_snoc_one v hv g

/-- Exact original-object consumer of `adelicFiniteLocalReferenceExtension_family`. -/
theorem actual_finite_reference_local_orbit_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (v : Fin (n + 1) → HeightOneSpectrum ℤ) 
    (g : ∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v i.castSucc).adicCompletion ℚ)) :
    adelicFiniteLocalReferenceExtension f hf v
      (adelicFiniteLocalTensorFamily f (fun i : Fin n => v i.castSucc) g) =
      adelicFiniteLocalTensorFamily f v (Fin.snoc g 1)  :=
  adelicFiniteLocalReferenceExtension_family f hf v g

/-- Exact original-object consumer of `adelicFiniteFamilyAwayCoreInitIsometry_orbit`. -/
theorem actual_finite_reference_complement_orbit_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin (n + 1) → HeightOneSpectrum ℤ)  (a : adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFamilyAwayCoreInitIsometry f v (adelicFiniteFamilyAwayOrbit f v a) =
      adelicFiniteFamilyAwayOrbit f (fun i : Fin n => v i.castSucc) (adelicFiniteFamilyAwayInitHom v a)  :=
  adelicFiniteFamilyAwayCoreInitIsometry_orbit f v a

/-- Exact original-object consumer of `adelicFiniteReferenceFamily_span`. -/
theorem actual_finite_reference_common_span_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin (n + 1) → HeightOneSpectrum ℤ)  (hf : f ≠ 0) :
    Submodule.span ℂ (Set.range (adelicFiniteReferenceFamily f v)) = ⊤  :=
  adelicFiniteReferenceFamily_span f v hf

/-- Exact original-object consumer of `adelicFiniteTensorIsometry_reference_extension`. -/
theorem actual_finite_reference_realization_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (v : Fin (n + 1) → HeightOneSpectrum ℤ) (F : PrimitiveCuspForm N k)  (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (x : AdelicFiniteReferenceDomain F.toCuspForm v) :
    adelicFiniteFullTensorIsometry F (fun i : Fin n => v i.castSucc)
      (hv.comp (Fin.castSucc_injective n)) (fun i => hgood i.castSucc)
      (adelicFiniteReferenceToShorter F.toCuspForm v x) =
      adelicFiniteFullTensorIsometry F v hv hgood
        (adelicFiniteReferenceToLonger F.toCuspForm v (primitiveCuspForm_ne_zero F) x)  :=
  adelicFiniteTensorIsometry_reference_extension v F hv hgood x

/-- Exact original-object consumer of `adelicFiniteHilbertTensorIsometry_reference_extension`. -/
theorem actual_completed_finite_reference_realization_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (v : Fin (n + 1) → HeightOneSpectrum ℤ) (F : PrimitiveCuspForm N k)  (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (x : AdelicFiniteReferenceHilbertDomain F.toCuspForm v) :
    adelicFiniteFullHilbertTensorIsometry F (fun i : Fin n => v i.castSucc)
      (hv.comp (Fin.castSucc_injective n)) (fun i => hgood i.castSucc)
      (adelicFiniteReferenceHilbertToShorter F.toCuspForm v x) =
      adelicFiniteFullHilbertTensorIsometry F v hv hgood
        (adelicFiniteReferenceHilbertToLonger F.toCuspForm v (primitiveCuspForm_ne_zero F) x)  :=
  adelicFiniteHilbertTensorIsometry_reference_extension v F hv hgood x

/-- Exact original-object consumer of `finiteAdeleGL2Gamma0_exists_exceptional_finset`. -/
theorem actual_finite_adelic_level_exceptions_source  (N : ℕ)
    (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      GeneralLinearGroup.map (finiteAdelePlace v) g ∈ finitePlaceGL2Gamma0 N v  :=
  finiteAdeleGL2Gamma0_exists_exceptional_finset N g


/-- Exact original-object consumer of `adelicFinitePlaceProduct_addCases`. -/
theorem actual_finite_block_coordinate_source {n m : ℕ} (v : Fin (n + m) → HeightOneSpectrum ℤ)  (hv : Function.Injective v)
    (g : ∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v (Fin.castAdd m i)).adicCompletion ℚ))
    (h : ∀ j : Fin m, GeneralLinearGroup (Fin 2) ((v (Fin.natAdd n j)).adicCompletion ℚ)) :
    adelicFinitePlaceProduct v hv (Fin.addCases g h) =
      adelicFinitePlaceProduct (fun i : Fin n => v (Fin.castAdd m i)) (adelicPlaceFamily_left_injective v hv) g *
      adelicFinitePlaceProduct (fun j : Fin m => v (Fin.natAdd n j)) (adelicPlaceFamily_right_injective v hv) h  :=
  adelicFinitePlaceProduct_addCases v hv g h

/-- Exact original-object consumer of `adelicFiniteTensorAssociation_original_orbit`. -/
theorem actual_finite_block_original_orbit_source {N : ℕ} [NeZero N] {k : ℤ} {n m : ℕ} (v : Fin (n + m) → HeightOneSpectrum ℤ) (F : PrimitiveCuspForm N k)  (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (g : ∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v (Fin.castAdd m i)).adicCompletion ℚ))
    (h : ∀ j : Fin m, GeneralLinearGroup (Fin 2) ((v (Fin.natAdd n j)).adicCompletion ℚ))
    (a : adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFullTensorIsometry F v hv hgood
      (adelicFiniteTensorAssociation F.toCuspForm v (adelicFiniteBlockedFamily F.toCuspForm v g h a)) =
      adelicCyclicHilbertRepresentation F.toCuspForm
        (adelicFinitePlaceProduct (fun i : Fin n => v (Fin.castAdd m i)) (adelicPlaceFamily_left_injective v hv) g *
          adelicFinitePlaceProduct (fun j : Fin m => v (Fin.natAdd n j)) (adelicPlaceFamily_right_injective v hv) h * a.val)
        (adelicCyclicUnitReference F.toCuspForm)  :=
  adelicFiniteTensorAssociation_original_orbit v F hv hgood g h a

/-- Exact original-object consumer of `adelicFiniteBlockedOrbitFamily_span`. -/
theorem actual_finite_block_tensor_span_source {N : ℕ} [NeZero N] {k : ℤ} {n m : ℕ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin (n + m) → HeightOneSpectrum ℤ)  (hf : f ≠ 0) :
    Submodule.span ℂ (Set.range (adelicFiniteBlockedOrbitFamily f v)) = ⊤  :=
  adelicFiniteBlockedOrbitFamily_span f v hf

/-- Exact original-object consumer of `adelicFiniteTensorIsometry_association`. -/
theorem actual_finite_block_association_source {N : ℕ} [NeZero N] {k : ℤ} {n m : ℕ} (v : Fin (n + m) → HeightOneSpectrum ℤ) (F : PrimitiveCuspForm N k)  (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (x : AdelicFiniteBlockedTensor F.toCuspForm v) :
    adelicFiniteFullTensorIsometry F v hv hgood (adelicFiniteTensorAssociation F.toCuspForm v x) =
      adelicFiniteBlockedTensorIsometry v F hv hgood x  :=
  adelicFiniteTensorIsometry_association v F hv hgood x

/-- Exact original-object consumer of `adelicFiniteHilbertTensorIsometry_association`. -/
theorem actual_completed_finite_block_association_source {N : ℕ} [NeZero N] {k : ℤ} {n m : ℕ} (v : Fin (n + m) → HeightOneSpectrum ℤ) (F : PrimitiveCuspForm N k)  (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (x : UniformSpace.Completion (AdelicFiniteBlockedTensor F.toCuspForm v)) :
    adelicFiniteFullHilbertTensorIsometry F v hv hgood
      (linearIsometryCompletionFunctor (adelicFiniteTensorAssociation F.toCuspForm v) x) =
      @linearIsometryCompletion (AdelicFiniteBlockedTensor F.toCuspForm v)
        (AdelicCyclicHilbert F.toCuspForm)
        inferInstance inferInstance inferInstance inferInstance inferInstance
        (adelicFiniteBlockedTensorIsometry v F hv hgood) x  :=
  adelicFiniteHilbertTensorIsometry_association v F hv hgood x

/-- Exact original-object consumer of `adelicRestrictedBaseCore_le_finiteAway`. -/
theorem actual_fixed_base_core_inclusion_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin n → HeightOneSpectrum ℤ)  (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    adelicRestrictedBaseCore f ≤ adelicFiniteFamilyAwayCore f v  :=
  adelicRestrictedBaseCore_le_finiteAway f v hgood

/-- Exact original-object consumer of `adelicRestrictedFiniteTensorFamily_span`. -/
theorem actual_fixed_base_finite_tensor_span_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin n → HeightOneSpectrum ℤ)  (hf : f ≠ 0) :
    Submodule.span ℂ (Set.range (adelicRestrictedFiniteTensorFamily f v)) = ⊤  :=
  adelicRestrictedFiniteTensorFamily_span f v hf

/-- Exact original-object consumer of `adelicRestrictedFiniteTensorIsometry_family`. -/
theorem actual_fixed_base_finite_orbit_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (F : PrimitiveCuspForm N k)  (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N) :
    adelicRestrictedFiniteTensorIsometry v F hv hgood (adelicRestrictedFiniteTensorFamily F.toCuspForm v b) =
      adelicCyclicHilbertRepresentation F.toCuspForm (adelicFinitePlaceProduct v hv b.1 * b.2.val)
        (adelicCyclicUnitReference F.toCuspForm)  :=
  adelicRestrictedFiniteTensorIsometry_family v F hv hgood b


/-- Exact original-object consumer of `goodAdelicPrimes_infinite`. -/
theorem actual_good_primes_infinite_source (N : ℕ) [NeZero N]  : {p : ℕ | p.Prime ∧ p.Coprime N}.Infinite  :=
  goodAdelicPrimes_infinite N

/-- Exact original-object consumer of `goodAdelicPlaceInitial_covers_finset`. -/
theorem actual_good_place_initial_coverage_source (N : ℕ) [NeZero N]  (S : Finset (HeightOneSpectrum ℤ)) :
    ∃ n, ∀ v ∈ S, IsGoodAdelicPlace N v → ∃ i : Fin n, goodAdelicPlaceInitial N n i = v  :=
  goodAdelicPlaceInitial_covers_finset N S

/-- Exact original-object consumer of `adelicGoodLevel_exists_base_mul_level`. -/
theorem actual_good_level_base_decomposition_source  (N : ℕ) [NeZero N] (a : RationalAdelicGL2)
    (ha : ∀ v, IsGoodAdelicPlace N v → adelicPlaceGL2Hom v a ∈ finitePlaceGL2Gamma0 N v) :
    ∃ b : adelicRestrictedBaseGroup N, ∃ u : finiteAdeleGL2Gamma0 N,
      b.val * rationalAdelicFiniteGL2Embedding u.val = a  :=
  adelicGoodLevel_exists_base_mul_level N a ha

/-- Exact original-object consumer of `adelicRestrictedStageIsometry_map`. -/
theorem actual_restricted_reference_transition_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)  (n m : ℕ) (h : n ≤ m) (x : adelicRestrictedStage F.toCuspForm n) :
    adelicRestrictedStageIsometry F m
      (adelicRestrictedStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m h x) =
      adelicRestrictedStageIsometry F n x  :=
  adelicRestrictedStageIsometry_map F n m h x

/-- Exact original-object consumer of `adelicRestrictedStageIsometry_covers_original_orbit`. -/
theorem actual_restricted_finite_orbit_coverage_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)  (a : RationalAdelicGL2) :
    ∃ n x, adelicRestrictedStageIsometry F n x =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicCyclicUnitReference F.toCuspForm)  :=
  adelicRestrictedStageIsometry_covers_original_orbit F a

/-- Exact original-object consumer of `adelicRestrictedTensor_exists_stage`. -/
theorem actual_restricted_tensor_finite_representative_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)  (x : AdelicRestrictedAlgebraicTensor F) :
    ∃ n y, adelicRestrictedTensorOf F n y = x  :=
  adelicRestrictedTensor_exists_stage F x

/-- Exact original-object consumer of `adelicRestrictedAlgebraicTensorIsometry_mem_range_iff`. -/
theorem actual_restricted_algebraic_range_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)  (y : AdelicCyclicHilbert F.toCuspForm) :
    y ∈ (adelicRestrictedAlgebraicTensorIsometry F).toLinearMap.range ↔
      ∃ n x, adelicRestrictedStageIsometry F n x = y  :=
  adelicRestrictedAlgebraicTensorIsometry_mem_range_iff F y

/-- Exact original-object consumer of `adelicRestrictedAlgebraicTensorIsometry_range_closure`. -/
theorem actual_restricted_tensor_density_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)  :
    (adelicRestrictedAlgebraicTensorIsometry F).toLinearMap.range.topologicalClosure = ⊤  :=
  adelicRestrictedAlgebraicTensorIsometry_range_closure F

/-- Exact original-object consumer of `adelicRestrictedHilbertTensorIsometry_of`. -/
theorem actual_restricted_completion_finite_vector_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)  (n : ℕ) (x : adelicRestrictedStage F.toCuspForm n) :
    adelicRestrictedHilbertTensorIsometry F ((adelicRestrictedTensorOf F n x : AdelicRestrictedAlgebraicTensor F) :
      AdelicRestrictedHilbertTensor F) = adelicRestrictedStageIsometry F n x  :=
  adelicRestrictedHilbertTensorIsometry_of F n x

/-- Exact original-object consumer of `adelicRestrictedHilbertTensorIsometry_range`. -/
theorem actual_restricted_completion_full_range_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)  :
    (adelicRestrictedHilbertTensorIsometry F).toLinearMap.range = ⊤  :=
  adelicRestrictedHilbertTensorIsometry_range F

/-- The actual directed quotient retains exactly the original finite tensor inner product. -/
theorem actual_restricted_quotient_inner_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)
    (n : ℕ) (x y : adelicRestrictedStage F.toCuspForm n) :
    inner ℂ (adelicRestrictedTensorOf F n x) (adelicRestrictedTensorOf F n y) = inner ℂ x y :=
  @LinearIsometry.inner_map_map ℂ (adelicRestrictedStage F.toCuspForm n)
    inferInstance inferInstance inferInstance (AdelicRestrictedAlgebraicTensor F)
    inferInstance inferInstance (adelicRestrictedTensorOf F n) x y

/-- Every actual original adelic Hilbert vector has a genuine completed restricted tensor representative. -/
theorem actual_restricted_completion_surjective_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)
    (y : AdelicCyclicHilbert F.toCuspForm) :
    ∃ x : AdelicRestrictedHilbertTensor F, adelicRestrictedHilbertTensorEquiv F x = y :=
  (adelicRestrictedHilbertTensorEquiv F).surjective y


/-- Exact original-object consumer of `finiteAdelicGL2On_mem`. -/
theorem actual_place_restriction_coordinate_source  (S : Set (HeightOneSpectrum ℤ))
    (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (v : HeightOneSpectrum ℤ) (hv : v ∈ S) :
    GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicGL2On S g) = GeneralLinearGroup.map (finiteAdelePlace v) g  :=
  finiteAdelicGL2On_mem S g v hv

/-- Exact original-object consumer of `finiteAdelicGL2On_mul_compl`. -/
theorem actual_complementary_adelic_restriction_source (S : Set (HeightOneSpectrum ℤ))  (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    finiteAdelicGL2On S g * finiteAdelicGL2On Sᶜ g = g  :=
  finiteAdelicGL2On_mul_compl S g

/-- Exact original-object consumer of `adelicGoodPart_mul_base`. -/
theorem actual_good_base_original_factor_source  (N : ℕ) (a : RationalAdelicGL2) :
    adelicGoodPartHom N a * (adelicBaseProjection N a).val = a  :=
  adelicGoodPart_mul_base N a

/-- Exact original-object consumer of `adelicBaseProjection_base`. -/
theorem actual_fixed_base_projection_source  (N : ℕ) (b : adelicRestrictedBaseGroup N) : adelicBaseProjection N b.val = b  :=
  adelicBaseProjection_base N b

/-- Exact original-object consumer of `adelicRestrictedFiniteTensorIsometry_intertwines`. -/
theorem actual_fixed_base_external_action_source {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (F : PrimitiveCuspForm N k)  (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N)
    (x : AdelicRestrictedFiniteTensor F.toCuspForm v) :
    adelicRestrictedFiniteTensorIsometry v F hv hgood (adelicRestrictedFiniteTensorRepresentation F.toCuspForm v b x) =
      adelicRestrictedFiniteJointRepresentation F.toCuspForm v hv hgood b
        (adelicRestrictedFiniteTensorIsometry v F hv hgood x)  :=
  adelicRestrictedFiniteTensorIsometry_intertwines v F hv hgood b x

/-- Exact original-object consumer of `adelicGoodTail_unitReference`. -/
theorem actual_good_tail_reference_fixed_source (N : ℕ) {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v)  [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (a : RationalAdelicGL2)
    (ha : ∀ w, IsGoodAdelicPlace N w → (∀ i, w ≠ v i) → adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w) :
    adelicCyclicHilbertRepresentation f (adelicGoodTail N v hv a) (adelicCyclicUnitReference f) =
      adelicCyclicUnitReference f  :=
  adelicGoodTail_unitReference N v hv f hgood a ha

/-- Exact original-object consumer of `adelicActionStage_spec`. -/
theorem actual_full_action_stage_bound_source (N : ℕ) [NeZero N]  (a : RationalAdelicGL2) (n : ℕ) :
    ∀ w, IsGoodAdelicPlace N w → (∀ i : Fin (adelicActionStage N a n), w ≠ goodAdelicPlaceInitial N (adelicActionStage N a n) i) →
      adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w  :=
  adelicActionStage_spec N a n

/-- Exact original-object consumer of `adelicRestrictedActionOnStage_intertwines`. -/
theorem actual_finite_stage_full_action_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)  (a : RationalAdelicGL2) (n : ℕ)
    (x : adelicRestrictedStage F.toCuspForm n) :
    adelicRestrictedAlgebraicTensorIsometry F (adelicRestrictedActionOnStage F a n x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicRestrictedStageIsometry F n x)  :=
  adelicRestrictedActionOnStage_intertwines F a n x

/-- Exact original-object consumer of `adelicRestrictedAlgebraicAction_intertwines`. -/
theorem actual_restricted_algebraic_full_action_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)  (a : RationalAdelicGL2) (x : AdelicRestrictedAlgebraicTensor F) :
    adelicRestrictedAlgebraicTensorIsometry F (adelicRestrictedAlgebraicAction F a x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicRestrictedAlgebraicTensorIsometry F x)  :=
  adelicRestrictedAlgebraicAction_intertwines F a x

/-- Exact original-object consumer of `adelicRestrictedHilbertTensorIsometry_intertwines`. -/
theorem actual_restricted_completed_full_action_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)  (a : RationalAdelicGL2) (x : AdelicRestrictedHilbertTensor F) :
    adelicRestrictedHilbertTensorIsometry F (adelicRestrictedHilbertTensorRepresentation F a x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicRestrictedHilbertTensorIsometry F x)  :=
  adelicRestrictedHilbertTensorIsometry_intertwines F a x

/-- Exact original-object consumer of `adelicRestrictedHilbertTensorRepresentation_stronglyContinuous`. -/
theorem actual_restricted_full_action_continuous_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)  (x : AdelicRestrictedHilbertTensor F) :
    Continuous (fun a => adelicRestrictedHilbertTensorRepresentation F a x)  :=
  adelicRestrictedHilbertTensorRepresentation_stronglyContinuous F x

/-- Exact original-object consumer of `adelicRestrictedHilbertTensorEquiv_intertwines`. -/
theorem actual_restricted_equivalence_full_action_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)  (a : RationalAdelicGL2) (x : AdelicRestrictedHilbertTensor F) :
    adelicRestrictedHilbertTensorEquiv F (adelicRestrictedHilbertTensorRepresentation F a x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicRestrictedHilbertTensorEquiv F x)  :=
  adelicRestrictedHilbertTensorEquiv_intertwines F a x


/-- Exact original-object consumer of `not_isGoodAdelicPlace_iff_dvd`. -/
theorem actual_bad_place_level_divisor_source  (N : ℕ) (v : HeightOneSpectrum ℤ) :
    ¬ IsGoodAdelicPlace N v ↔ Rat.HeightOneSpectrum.natGenerator v ∣ N :=
  not_isGoodAdelicPlace_iff_dvd N v

/-- Exact original-object consumer of `adelicFiniteOpenLowest_finiteDimensional`. -/
theorem actual_full_finite_open_lowest_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (hf : f ≠ 0) (hk : 0 < k)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    FiniteDimensional ℂ ↥(adelicRotationWeightSpace f ⊓ adelicFiniteSubgroupFixedSpace f J :
      Submodule ℂ (AdelicCyclicHilbert f)) :=
  adelicFiniteOpenLowest_finiteDimensional f hf hk J hJ

/-- Exact original-object consumer of `adelicNormalizedCuspCoefficient_coordinates`. -/
theorem actual_real_finite_coefficient_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (hf : f ≠ 0) (hk : 0 < k) (b : RationalAdelicGL2) :
    adelicNormalizedCuspCoefficient f b =
      adelicNormalizedCuspCoefficient f (adelicRealGL2Embedding (rationalAdelicGL2RealFiniteEquiv b).1) *
      adelicNormalizedCuspCoefficient f (rationalAdelicFiniteGL2Embedding (rationalAdelicGL2RealFiniteEquiv b).2) :=
  adelicNormalizedCuspCoefficient_coordinates f hf hk b

/-- Exact original-object consumer of `adelicCyclicUnitReference_realFinite_gram`. -/
theorem actual_real_finite_gram_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (hf : f ≠ 0) (hk : 0 < k)
    (a b : GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    inner ℂ
      (adelicCyclicHilbertRepresentation f (rationalAdelicGL2RealFiniteEquiv.symm a) (adelicCyclicUnitReference f))
      (adelicCyclicHilbertRepresentation f (rationalAdelicGL2RealFiniteEquiv.symm b) (adelicCyclicUnitReference f)) =
    inner ℂ
      (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding a.1) (adelicCyclicUnitReference f))
      (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding b.1) (adelicCyclicUnitReference f)) *
    inner ℂ
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.2) (adelicCyclicUnitReference f))
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding b.2) (adelicCyclicUnitReference f)) :=
  adelicCyclicUnitReference_realFinite_gram f hf hk a b

/-- Exact original-object consumer of `adelicRealFiniteTensorIsometry_family`. -/
theorem actual_real_finite_tensor_family_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (hf : f ≠ 0) (hk : 0 < k)
    (a : GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicRealFiniteTensorIsometry f hf hk (adelicRealFiniteTensorFamily f a) = adelicRealFiniteMixedFamily f a :=
  adelicRealFiniteTensorIsometry_family f hf hk a

/-- Exact original-object consumer of `adelicRealFiniteTensorIsometry_range_closure`. -/
theorem actual_real_finite_tensor_density_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (hf : f ≠ 0) (hk : 0 < k) :
    (adelicRealFiniteTensorIsometry f hf hk).toLinearMap.range.topologicalClosure = ⊤ :=
  adelicRealFiniteTensorIsometry_range_closure f hf hk

/-- Exact original-object consumer of `adelicRealFiniteHilbertTensorIsometry_range`. -/
theorem actual_real_finite_completed_range_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (hf : f ≠ 0) (hk : 0 < k) :
    (adelicRealFiniteHilbertTensorIsometry f hf hk).toLinearMap.range = ⊤ :=
  adelicRealFiniteHilbertTensorIsometry_range f hf hk

/-- Exact original-object consumer of `adelicRealFiniteHilbertTensorEquiv_intertwines`. -/
theorem actual_real_finite_completed_equivariance_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (hf : f ≠ 0) (hk : 0 < k)
    (a : RationalAdelicGL2) (x : AdelicRealFiniteHilbertTensor f) :
    adelicRealFiniteHilbertTensorEquiv f hf hk
      (adelicRealFiniteHilbertTensorRepresentation f hf hk (rationalAdelicGL2RealFiniteEquiv a) x) =
      adelicCyclicHilbertRepresentation f a (adelicRealFiniteHilbertTensorEquiv f hf hk x) :=
  adelicRealFiniteHilbertTensorEquiv_intertwines f hf hk a x

/-- Exact original-object consumer of `adelicRealFiniteHilbertTensorRepresentation_stronglyContinuous`. -/
theorem actual_real_finite_completed_continuity_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (hf : f ≠ 0) (hk : 0 < k)
    (x : AdelicRealFiniteHilbertTensor f) :
    Continuous (fun b => adelicRealFiniteHilbertTensorRepresentation f hf hk b x) :=
  adelicRealFiniteHilbertTensorRepresentation_stronglyContinuous f hf hk x

/-- Exact original-object consumer of `adelicFullFiniteUnitCore_closure_eq_weight`. -/
theorem actual_full_finite_factor_weight_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (hf : f ≠ 0) (hk : 0 < k) :
    (adelicFullFiniteUnitCore f).topologicalClosure = adelicRotationWeightSpace f :=
  adelicFullFiniteUnitCore_closure_eq_weight f hf hk

/-- Exact original-object consumer of `adelicFullFiniteUnitCoreRepresentation_admissible`. -/
theorem actual_full_finite_core_admissibility_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (hf : f ≠ 0) (hk : 0 < k)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    FiniteDimensional ℂ (Representation.invariants ((adelicFullFiniteUnitCoreRepresentation f).comp J.subtype)) :=
  adelicFullFiniteUnitCoreRepresentation_admissible f hf hk J hJ

/-- Exact original-object consumer of `adelicFullFiniteHilbertRepresentation_admissible`. -/
theorem actual_full_finite_hilbert_admissibility_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (hf : f ≠ 0) (hk : 0 < k)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    FiniteDimensional ℂ (Representation.invariants ((adelicFullFiniteHilbertRepresentation f).comp J.subtype)) :=
  adelicFullFiniteHilbertRepresentation_admissible f hf hk J hJ


/-- Exact original-object consumer of `adelicLocalNormalizedHecke_distinct_component`. -/
theorem actual_distinct_local_hecke_component_source {N : ℕ} [NeZero N] {k : ℤ}  {p : ℕ} [NeZero p]
    (F : PrimitiveCuspForm N k) (hp : p.Prime) (hpN : p.Coprime N)
    (v : HeightOneSpectrum ℤ) (hv : v ≠ rationalPrimePlace p hp)
    (x : AdelicCyclicHilbert F.toCuspForm) (hx : x ∈ adelicLocalCyclicClosedSpan F.toCuspForm v) :
    adelicLocalNormalizedHecke F.toCuspForm p hp hpN x = normalizedCuspCoefficients F.toCuspForm p • x :=
  adelicLocalNormalizedHecke_distinct_component F hp hpN v hv x hx

/-- Exact original-object consumer of `adelicNormalizedHecke_eigen_iff`. -/
theorem actual_reverse_hecke_normalization_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (p : ℕ) [NeZero p] (hpN : p.Coprime N) (x : AdelicCyclicHilbert f) :
    adelicNormalizedHecke f p hpN x = normalizedCuspCoefficients f p • x ↔
      adelicHilbertHeckeTrace f p hpN x =
        ((Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) * cuspCoefficients f p) • x :=
  adelicNormalizedHecke_eigen_iff f p hpN x

/-- Exact original-object consumer of `adelicBadLocalCyclic_fixed_generator_scalar`. -/
theorem actual_bad_local_fixed_line_source {N : ℕ} [NeZero N] {k : ℤ}  (F : PrimitiveCuspForm N k) (hk : 0 < k)
    (v : HeightOneSpectrum ℤ) (hv : ¬ IsGoodAdelicPlace N v)
    (x : AdelicCyclicHilbert F.toCuspForm) (hx : x ∈ adelicLocalCyclicClosedSpan F.toCuspForm v)
    (hfix : x ∈ adelicLocalFixedSpace F.toCuspForm v) :
    ∃ c : ℂ, x = c • adelicCyclicHilbertGenerator F.toCuspForm :=
  adelicBadLocalCyclic_fixed_generator_scalar F hk v hv x hx hfix

/-- Exact original-object consumer of `adelicEveryLocalCyclic_fixed_eq_generator_line`. -/
theorem actual_every_local_fixed_line_source  {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hk : 0 < k) (v : HeightOneSpectrum ℤ) :
    adelicLocalCyclicClosedSpan F.toCuspForm v ⊓ adelicLocalFixedSpace F.toCuspForm v =
      Submodule.span ℂ {adelicCyclicHilbertGenerator F.toCuspForm} :=
  adelicEveryLocalCyclic_fixed_eq_generator_line F hk v

/-- Exact original-object consumer of `adelicEveryLocalCyclicProjection_fixed_scalar`. -/
theorem actual_every_local_cyclic_projection_source  {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hk : 0 < k) (v : HeightOneSpectrum ℤ)
    (x : AdelicCyclicHilbert F.toCuspForm) (hx : x ∈ adelicLocalFixedSpace F.toCuspForm v) :
    ∃ c : ℂ, adelicLocalCyclicProjection F.toCuspForm v x = c • adelicCyclicHilbertGenerator F.toCuspForm :=
  adelicEveryLocalCyclicProjection_fixed_scalar F hk v x hx

/-- Exact original-object consumer of `adelicEveryLocalCyclic_intertwiner_scalar`. -/
theorem actual_every_local_schur_source  {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (v : HeightOneSpectrum ℤ)
    (T : AdelicCyclicHilbert F.toCuspForm →L[ℂ] AdelicCyclicHilbert F.toCuspForm)
    (hT : ∀ g x, T (adelicCyclicLocalRepresentation F.toCuspForm
      v g x) =
        adelicCyclicLocalRepresentation F.toCuspForm v g (T x))
    (hcyclic : T (adelicCyclicHilbertGenerator F.toCuspForm) ∈
      adelicLocalCyclicClosedSpan F.toCuspForm v) :
    ∃ c : ℂ, ∀ x ∈ adelicLocalCyclicClosedSpan F.toCuspForm v,
      T x = c • x :=
  adelicEveryLocalCyclic_intertwiner_scalar F hk v T hT hcyclic

/-- Exact original-object consumer of `adelicEveryLocalCyclicClosedSpan_irreducible`. -/
theorem actual_every_local_hilbert_irreducibility_source  {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (v : HeightOneSpectrum ℤ)
    (S : Submodule ℂ (AdelicCyclicHilbert F.toCuspForm))
    (hclosed : IsClosed (S : Set (AdelicCyclicHilbert F.toCuspForm)))
    (hle : S ≤ adelicLocalCyclicClosedSpan F.toCuspForm v)
    (hinv : ∀ g x, x ∈ S → adelicCyclicLocalRepresentation F.toCuspForm
      v g x ∈ S) :
    S = ⊥ ∨ S = adelicLocalCyclicClosedSpan F.toCuspForm v :=
  adelicEveryLocalCyclicClosedSpan_irreducible F hk v S hclosed hle hinv

/-- Exact original-object consumer of `adelicEveryLocalCyclicCore_irreducible`. -/
theorem actual_every_local_core_irreducibility_source  {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (v : HeightOneSpectrum ℤ)
    (W : Submodule ℂ (AdelicCyclicHilbert F.toCuspForm))
    (hW : W ≤ adelicLocalCyclicCore F.toCuspForm v)
    (hinv : ∀ g x, x ∈ W → adelicCyclicLocalRepresentation F.toCuspForm
      v g x ∈ W) :
    W = ⊥ ∨ W = adelicLocalCyclicCore F.toCuspForm v :=
  adelicEveryLocalCyclicCore_irreducible F hk v W hW hinv

/-- Exact original-object consumer of `adelicEveryLocal_fullAway_mixed_gram`. -/
theorem actual_every_local_full_complement_gram_source {N : ℕ} [NeZero N] {k : ℤ}  (F : PrimitiveCuspForm N k) (hk : 0 < k) (v : HeightOneSpectrum ℤ)
    (g₁ g₂ : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (a₁ a₂ : AdelicFullAwayGroup v) :
    inner ℂ
      (adelicCyclicLocalRepresentation F.toCuspForm v g₁
        (adelicCyclicFullAwayRepresentation F.toCuspForm v a₁
          (adelicCyclicHilbertGenerator F.toCuspForm)))
      (adelicCyclicLocalRepresentation F.toCuspForm v g₂
        (adelicCyclicFullAwayRepresentation F.toCuspForm v a₂
          (adelicCyclicHilbertGenerator F.toCuspForm))) *
      inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm) (adelicCyclicHilbertGenerator F.toCuspForm) =
    inner ℂ
      (adelicCyclicLocalRepresentation F.toCuspForm v g₁
        (adelicCyclicHilbertGenerator F.toCuspForm))
      (adelicCyclicLocalRepresentation F.toCuspForm v g₂
        (adelicCyclicHilbertGenerator F.toCuspForm)) *
    inner ℂ
      (adelicCyclicFullAwayRepresentation F.toCuspForm v a₁
        (adelicCyclicHilbertGenerator F.toCuspForm))
      (adelicCyclicFullAwayRepresentation F.toCuspForm v a₂
        (adelicCyclicHilbertGenerator F.toCuspForm)) :=
  adelicEveryLocal_fullAway_mixed_gram F hk v g₁ g₂ a₁ a₂

/-- Exact original-object consumer of `adelicNormalizedCuspCoefficient_everyLocal_mul`. -/
theorem actual_every_local_normalized_factor_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k)  (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (a : RationalAdelicGL2) (ha : adelicPlaceGL2Hom v a = 1) :
    adelicNormalizedCuspCoefficient F.toCuspForm (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g) * a) =
      adelicNormalizedCuspCoefficient F.toCuspForm (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) *
        adelicNormalizedCuspCoefficient F.toCuspForm a :=
  adelicNormalizedCuspCoefficient_everyLocal_mul F hk v g a ha

/-- Exact original-object consumer of `adelicFullFiniteHilbert_smooth_iff_core`. -/
theorem actual_full_finite_smooth_core_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)  (hf : f ≠ 0) (hk : 0 < k)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicRotationWeightSpace f) :
    (∃ J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)),
      IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) ∧
        ∀ g ∈ J, adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding g) x = x) ↔
      x ∈ adelicFullFiniteUnitCore f :=
  adelicFullFiniteHilbert_smooth_iff_core f hf hk x hx

/-- Exact original-object consumer of `adelicNormalizedCuspCoefficient_every_finiteFamilyEquiv`. -/
theorem actual_every_finite_family_coefficient_source {N : ℕ} [NeZero N] {k : ℤ} {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v) (F : PrimitiveCuspForm N k) 
    (hk : 0 < k)
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicNormalizedCuspCoefficient F.toCuspForm (adelicFiniteFamilyEquiv v hv b) =
      (∏ i, adelicNormalizedCuspCoefficient F.toCuspForm
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (b.1 i)))) *
      adelicNormalizedCuspCoefficient F.toCuspForm b.2.val :=
  adelicNormalizedCuspCoefficient_every_finiteFamilyEquiv v hv F hk b

/-- Exact original-object consumer of `adelicCyclicUnitReference_every_finiteFamily_gram`. -/
theorem actual_every_finite_family_gram_source {N : ℕ} [NeZero N] {k : ℤ} {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v) (F : PrimitiveCuspForm N k) 
    (hk : 0 < k)
    (b₁ b₂ : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    inner ℂ
      (adelicCyclicHilbertRepresentation F.toCuspForm (adelicFiniteFamilyEquiv v hv b₁)
        (adelicCyclicUnitReference F.toCuspForm))
      (adelicCyclicHilbertRepresentation F.toCuspForm (adelicFiniteFamilyEquiv v hv b₂)
        (adelicCyclicUnitReference F.toCuspForm)) =
      (∏ i, inner ℂ
        (adelicCyclicHilbertRepresentation F.toCuspForm
          (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (b₁.1 i)))
          (adelicCyclicUnitReference F.toCuspForm))
        (adelicCyclicHilbertRepresentation F.toCuspForm
          (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (b₂.1 i)))
          (adelicCyclicUnitReference F.toCuspForm))) *
      inner ℂ
        (adelicCyclicHilbertRepresentation F.toCuspForm b₁.2.val (adelicCyclicUnitReference F.toCuspForm))
        (adelicCyclicHilbertRepresentation F.toCuspForm b₂.2.val (adelicCyclicUnitReference F.toCuspForm)) :=
  adelicCyclicUnitReference_every_finiteFamily_gram v hv F hk b₁ b₂


/-- Exact original-object consumer of `adelicEveryFiniteFullTensorFamily_gram`. -/
theorem actual_full_split_adelicEveryFiniteFullTensorFamily_gram_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v) (hk : 0 < k)
    (a b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    inner ℂ (adelicFiniteFullTensorFamily F.toCuspForm v a) (adelicFiniteFullTensorFamily F.toCuspForm v b) =
      inner ℂ (adelicFiniteFullMixedFamily F.toCuspForm v hv a) (adelicFiniteFullMixedFamily F.toCuspForm v hv b) :=
  adelicEveryFiniteFullTensorFamily_gram F v hv hk a b

/-- Exact original-object consumer of `adelicBadPlaceFamily_surjective_bad`. -/
theorem actual_full_split_adelicBadPlaceFamily_surjective_bad_source  (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ)
    (hv : ¬ IsGoodAdelicPlace N v) : ∃ i, adelicBadPlaceFamily N i = v :=
  adelicBadPlaceFamily_surjective_bad N v hv

/-- Exact original-object consumer of `adelicFiniteRealJointHom_apply`. -/
theorem actual_full_split_adelicFiniteRealJointHom_apply_source  {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ)
    (hv : Function.Injective v)
    (a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ) :
    adelicFiniteRealJointHom v hv a = adelicFinitePlaceProduct v hv a.1 * adelicRealGL2Embedding a.2 :=
  adelicFiniteRealJointHom_apply v hv a

/-- Exact original-object consumer of `adelicBadRealJointHom_reconstruct`. -/
theorem actual_full_split_adelicBadRealJointHom_reconstruct_source (N : ℕ) [NeZero N] (b : adelicRestrictedBaseGroup N) :
    adelicBadRealJointHom N
      (adelicFinitePlaceEvaluation (adelicBadPlaceFamily N) b.val, (rationalAdelicGL2RealFiniteEquiv b.val).1) = b.val :=
  adelicBadRealJointHom_reconstruct N b

/-- Exact original-object consumer of `adelicFiniteRealTensorFamily_gram`. -/
theorem actual_full_split_adelicFiniteRealTensorFamily_gram_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v) (hk : 0 < k)
    (a b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ) :
    inner ℂ (adelicFiniteRealTensorFamily F.toCuspForm v a) (adelicFiniteRealTensorFamily F.toCuspForm v b) =
      inner ℂ (adelicFiniteRealMixedFamily F.toCuspForm v hv a) (adelicFiniteRealMixedFamily F.toCuspForm v hv b) :=
  adelicFiniteRealTensorFamily_gram v F hv hk a b

/-- Exact original-object consumer of `adelicBadRealTensorBaseEquiv_family`. -/
theorem actual_full_split_adelicBadRealTensorBaseEquiv_family_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k)
    (a : AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ) :
    adelicBadRealTensorBaseEquiv F hk (adelicFiniteRealTensorFamily F.toCuspForm (adelicBadPlaceFamily N) a) =
      adelicRestrictedBaseOrbit F.toCuspForm (adelicBadRealBaseEquiv N a) :=
  adelicBadRealTensorBaseEquiv_family F hk a

/-- Exact original-object consumer of `adelicFiniteRealTensorIsometry_intertwines`. -/
theorem actual_full_split_adelicFiniteRealTensorIsometry_intertwines_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v) (hk : 0 < k)
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ)
    (x : AdelicFiniteRealTensor F.toCuspForm v) :
    adelicFiniteRealTensorIsometry v F hv hk (adelicFiniteRealTensorRepresentation F.toCuspForm v b x) =
      adelicFiniteRealJointRepresentation F.toCuspForm v hv b (adelicFiniteRealTensorIsometry v F hv hk x) :=
  adelicFiniteRealTensorIsometry_intertwines v F hv hk b x

/-- Exact original-object consumer of `adelicBadRealTensorBaseEquiv_intertwines`. -/
theorem actual_full_split_adelicBadRealTensorBaseEquiv_intertwines_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k)
    (a : AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ)
    (x : AdelicFiniteRealTensor F.toCuspForm (adelicBadPlaceFamily N)) :
    adelicBadRealTensorBaseEquiv F hk
      (adelicFiniteRealTensorRepresentation F.toCuspForm (adelicBadPlaceFamily N) a x) =
      adelicRestrictedBaseCoreRepresentation F.toCuspForm (adelicBadRealBaseEquiv N a)
        (adelicBadRealTensorBaseEquiv F hk x) :=
  adelicBadRealTensorBaseEquiv_intertwines F hk a x

/-- Exact original-object consumer of `adelicSplitStageEquiv_step`. -/
theorem actual_full_split_adelicSplitStageEquiv_step_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (n : ℕ)
    (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitStageEquiv F hk (n + 1)
      (adelicSplitStageStep F.toCuspForm (primitiveCuspForm_ne_zero F) n x) =
      adelicRestrictedStageStep F.toCuspForm (primitiveCuspForm_ne_zero F) n
        (adelicSplitStageEquiv F hk n x) :=
  adelicSplitStageEquiv_step F hk n x

/-- Exact original-object consumer of `adelicSplitAlgebraicTensorIsometry_mem_range_iff`. -/
theorem actual_full_split_adelicSplitAlgebraicTensorIsometry_mem_range_iff_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k)
    (y : AdelicCyclicHilbert F.toCuspForm) :
    y ∈ (adelicSplitAlgebraicTensorIsometry F hk).toLinearMap.range ↔
      ∃ n x, adelicSplitStageIsometry F hk n x = y :=
  adelicSplitAlgebraicTensorIsometry_mem_range_iff F hk y

/-- Exact original-object consumer of `adelicSplitStageIsometry_covers_original_orbit`. -/
theorem actual_full_split_adelicSplitStageIsometry_covers_original_orbit_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (a : RationalAdelicGL2) :
    ∃ n x, adelicSplitStageIsometry F hk n x =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicCyclicUnitReference F.toCuspForm) :=
  adelicSplitStageIsometry_covers_original_orbit F hk a

/-- Exact original-object consumer of `adelicSplitHilbertTensorIsometry_range`. -/
theorem actual_full_split_adelicSplitHilbertTensorIsometry_range_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) :
    (adelicSplitHilbertTensorIsometry F hk).toLinearMap.range = ⊤ :=
  adelicSplitHilbertTensorIsometry_range F hk

/-- Exact original-object consumer of `adelicSplitStageIsometry_map`. -/
theorem actual_full_split_adelicSplitStageIsometry_map_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (n m : ℕ) (h : n ≤ m)
    (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitStageIsometry F hk m
      (adelicSplitStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m h x) =
      adelicSplitStageIsometry F hk n x :=
  adelicSplitStageIsometry_map F hk n m h x

/-- Exact original-object consumer of `adelicSplitStageFullOperator_intertwines`. -/
theorem actual_full_split_adelicSplitStageFullOperator_intertwines_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (n : ℕ) (a : RationalAdelicGL2)
    (ha : ∀ w, IsGoodAdelicPlace N w → (∀ i : Fin n, w ≠ goodAdelicPlaceInitial N n i) →
      adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w)
    (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitStageIsometry F hk n (adelicSplitStageFullOperator F n a x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicSplitStageIsometry F hk n x) :=
  adelicSplitStageFullOperator_intertwines F hk n a ha x

/-- Exact original-object consumer of `adelicSplitActionOnStage_compatible`. -/
theorem actual_full_split_adelicSplitActionOnStage_compatible_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (a : RationalAdelicGL2)
    (n m : ℕ) (h : n ≤ m) (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitActionOnStage F a m
      (adelicSplitStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m h x) =
      adelicSplitActionOnStage F a n x :=
  adelicSplitActionOnStage_compatible F hk a n m h x

/-- Exact original-object consumer of `adelicSplitAlgebraicRepresentation_norm`. -/
theorem actual_full_split_adelicSplitAlgebraicRepresentation_norm_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (a : RationalAdelicGL2) (x : AdelicSplitAlgebraicTensor F) :
    ‖adelicSplitAlgebraicRepresentation F hk a x‖ = ‖x‖ :=
  adelicSplitAlgebraicRepresentation_norm F hk a x

/-- Exact original-object consumer of `adelicSplitHilbertTensorEquiv_intertwines`. -/
theorem actual_full_split_adelicSplitHilbertTensorEquiv_intertwines_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (a : RationalAdelicGL2) (x : AdelicSplitHilbertTensor F) :
    adelicSplitHilbertTensorEquiv F hk (adelicSplitHilbertTensorRepresentation F hk a x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicSplitHilbertTensorEquiv F hk x) :=
  adelicSplitHilbertTensorEquiv_intertwines F hk a x

/-- Exact original-object consumer of `adelicSplitHilbertTensorRepresentation_stronglyContinuous`. -/
theorem actual_full_split_adelicSplitHilbertTensorRepresentation_stronglyContinuous_source {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (x : AdelicSplitHilbertTensor F) :
    Continuous (fun a => adelicSplitHilbertTensorRepresentation F hk a x) :=
  adelicSplitHilbertTensorRepresentation_stronglyContinuous F hk x


/-- Exact original-object consumer of `adelicNormalizedSignedRaisingJet_orthonormal`. -/
theorem actual_integer_weight_adelicNormalizedSignedRaisingJet_orthonormal_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k) :
    Orthonormal ℂ (adelicNormalizedSignedRaisingJet f) :=
  adelicNormalizedSignedRaisingJet_orthonormal f hf hk

/-- Exact original-object consumer of `adelicSignedRaisingClosedSpan_eq_fullRealClosure`. -/
theorem actual_integer_weight_adelicSignedRaisingClosedSpan_eq_fullRealClosure_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) :
    adelicSignedRaisingClosedSpan f = (adelicFullRealUnitCore f).topologicalClosure :=
  adelicSignedRaisingClosedSpan_eq_fullRealClosure f hf

/-- Exact original-object consumer of `adelicFullRealHilbertBasis_apply`. -/
theorem actual_integer_weight_adelicFullRealHilbertBasis_apply_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    (adelicFullRealHilbertBasis f hf hk i).val = adelicNormalizedSignedRaisingJet f i :=
  adelicFullRealHilbertBasis_apply f hf hk i

/-- Exact original-object consumer of `adelicFullRealRotationEigenspace_finiteDimensional`. -/
theorem actual_integer_weight_adelicFullRealRotationEigenspace_finiteDimensional_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k) (m : ℤ) :
    FiniteDimensional ℂ (adelicFullRealRotationEigenspace f m) :=
  adelicFullRealRotationEigenspace_finiteDimensional f hf hk m

/-- Exact original-object consumer of `adelicIntegerRotationWeightProjection_finite`. -/
theorem actual_integer_weight_adelicIntegerRotationWeightProjection_finite_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (m : ℤ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (x : AdelicCyclicHilbert f) :
    adelicIntegerRotationWeightProjection f m
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) x) =
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicIntegerRotationWeightProjection f m x) :=
  adelicIntegerRotationWeightProjection_finite f m a x

/-- Exact original-object consumer of `adelicIntegerRotationWeightProjection_realClosure`. -/
theorem actual_integer_weight_adelicIntegerRotationWeightProjection_realClosure_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k)
    (i : ℕ ⊕ ℕ) (x : AdelicCyclicHilbert f) (hx : x ∈ (adelicFullRealUnitCore f).topologicalClosure) :
    adelicIntegerRotationWeightProjection f (adelicSignedRaisingWeight k i) x ∈
      Submodule.span ℂ {adelicSignedRaisingJet f i} :=
  adelicIntegerRotationWeightProjection_realClosure f hf hk i x hx

/-- Exact original-object consumer of `adelicIntegerRotationWeightSpace_eq_signedFiniteClosure`. -/
theorem actual_integer_weight_adelicIntegerRotationWeightSpace_eq_signedFiniteClosure_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) = adelicSignedFiniteCyclicClosedSpan f i :=
  adelicIntegerRotationWeightSpace_eq_signedFiniteClosure f hf hk i

/-- Exact original-object consumer of `continuous_gram_factor_closure`. -/
theorem actual_integer_weight_continuous_gram_factor_closure_source {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (u : ι → E) (T U : E →L[ℂ] F) (c : ℂ)
    (h : ∀ i j, inner ℂ (T (u i)) (U (u j)) = inner ℂ (u i) (u j) * c)
    (x y : E) (hx : x ∈ (Submodule.span ℂ (Set.range u)).topologicalClosure)
    (hy : y ∈ (Submodule.span ℂ (Set.range u)).topologicalClosure) :
    inner ℂ (T x) (U y) = inner ℂ x y * c :=
  continuous_gram_factor_closure u T U c h x y hx hy

/-- Exact original-object consumer of `adelicFullRealClosure_finite_gram`. -/
theorem actual_integer_weight_adelicFullRealClosure_finite_gram_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k)
    (a b : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (x y : AdelicCyclicHilbert f)
    (hx : x ∈ (adelicFullRealUnitCore f).topologicalClosure)
    (hy : y ∈ (adelicFullRealUnitCore f).topologicalClosure) :
    inner ℂ (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) x)
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding b) y) =
      inner ℂ x y * inner ℂ
        (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) (adelicCyclicUnitReference f))
        (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding b) (adelicCyclicUnitReference f)) :=
  adelicFullRealClosure_finite_gram f hf hk a b x y hx hy

/-- Exact original-object consumer of `adelicSignedFiniteCoreIsometry_range_closure`. -/
theorem actual_integer_weight_adelicSignedFiniteCoreIsometry_range_closure_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    (adelicSignedFiniteCoreIsometry f hf hk i).toLinearMap.range.topologicalClosure =
      adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) :=
  adelicSignedFiniteCoreIsometry_range_closure f hf hk i

/-- Exact original-object consumer of `adelicFullFiniteCoreCompletionInclusion_intertwines`. -/
theorem actual_integer_weight_adelicFullFiniteCoreCompletionInclusion_intertwines_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (x : AdelicFullFiniteCoreCompletion f) :
    adelicFullFiniteCoreCompletionInclusion f (adelicFullFiniteCoreCompletionRepresentation f a x) =
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicFullFiniteCoreCompletionInclusion f x) :=
  adelicFullFiniteCoreCompletionInclusion_intertwines f a x

/-- Exact original-object consumer of `adelicSignedFiniteCoreIsometry_intertwines`. -/
theorem actual_integer_weight_adelicSignedFiniteCoreIsometry_intertwines_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (x : adelicFullFiniteUnitCore f) :
    adelicSignedFiniteCoreIsometry f hf hk i (adelicFullFiniteUnitCoreRepresentation f a x) =
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicSignedFiniteCoreIsometry f hf hk i x) :=
  adelicSignedFiniteCoreIsometry_intertwines f hf hk i a x

/-- Exact original-object consumer of `adelicSignedFiniteCompletionIsometry_intertwines`. -/
theorem actual_integer_weight_adelicSignedFiniteCompletionIsometry_intertwines_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (x : AdelicFullFiniteCoreCompletion f) :
    adelicSignedFiniteCompletionIsometry f hf hk i (adelicFullFiniteCoreCompletionRepresentation f a x) =
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicSignedFiniteCompletionIsometry f hf hk i x) :=
  adelicSignedFiniteCompletionIsometry_intertwines f hf hk i a x

/-- Exact original-object consumer of `adelicSignedWeight_finiteDimensional`. -/
theorem actual_integer_weight_adelicSignedWeight_finiteDimensional_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    FiniteDimensional ℂ
      (adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) ⊓ adelicFiniteSubgroupFixedSpace f J :
        Submodule ℂ (AdelicCyclicHilbert f)) :=
  adelicSignedWeight_finiteDimensional f hf hk i J hJ

/-- Exact original-object consumer of `adelicIntegerRotationWeightSpace_eq_bot`. -/
theorem actual_integer_weight_adelicIntegerRotationWeightSpace_eq_bot_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (m : ℤ)
    (hm : ∀ i, m ≠ adelicSignedRaisingWeight k i) : adelicIntegerRotationWeightSpace f m = ⊥ :=
  adelicIntegerRotationWeightSpace_eq_bot f hf m hm

/-- Exact original-object consumer of `adelicIntegerWeight_finiteDimensional`. -/
theorem actual_integer_weight_adelicIntegerWeight_finiteDimensional_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k) (m : ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    FiniteDimensional ℂ (adelicIntegerRotationWeightSpace f m ⊓ adelicFiniteSubgroupFixedSpace f J :
      Submodule ℂ (AdelicCyclicHilbert f)) :=
  adelicIntegerWeight_finiteDimensional f hf hk m J hJ


/-- Exact original-object consumer of `finiteDimensional_polynomial_kernel_of_eigenspaces`. -/
theorem actual_compact_type_finiteDimensional_polynomial_kernel_of_eigenspaces_source {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (hT : ∀ c : ℂ, FiniteDimensional ℂ (Module.End.eigenspace T c))
    (p : Polynomial ℂ) (hp : p.Monic) : FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval T p)) :=
  finiteDimensional_polynomial_kernel_of_eigenspaces T hT p hp

/-- Exact original-object consumer of `eigenspace_eq_of_dense_eigenfamily`. -/
theorem actual_compact_type_eigenspace_eq_of_dense_eigenfamily_source {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : Module.End ℂ V) (hT : ∀ x y, inner ℂ (T x) (T y) = inner ℂ x y)
    (u : ι → V) (θ : ι → ℂ) (hθ : ∀ i, ‖θ i‖ = 1)
    (hu : ∀ i, T (u i) = θ i • u i)
    (hd : (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤)
    (c : ℂ) (S : Submodule ℂ V) [CompleteSpace S]
    (hS : S ≤ Module.End.eigenspace T c)
    (hm : ∀ i, θ i = c → u i ∈ S) : Module.End.eigenspace T c = S :=
  eigenspace_eq_of_dense_eigenfamily T hT u θ hθ hu hd c S hS hm

/-- Exact original-object consumer of `adelicSignedFiniteFamily_dense`. -/
theorem actual_compact_type_adelicSignedFiniteFamily_dense_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) :
    (Submodule.span ℂ (Set.range (adelicSignedFiniteFamily f))).topologicalClosure = ⊤ :=
  adelicSignedFiniteFamily_dense f hf

/-- Exact original-object consumer of `adelicIrrationalRotation_eigenspace`. -/
theorem actual_compact_type_adelicIrrationalRotation_eigenspace_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (i : ℕ ⊕ ℕ) :
    Module.End.eigenspace (adelicIrrationalRotation f) (integerIrrationalCharacter (adelicSignedRaisingWeight k i)) =
      adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) :=
  adelicIrrationalRotation_eigenspace f hf i

/-- Exact original-object consumer of `adelicIrrationalRotation_fixed_eigenspace_finiteDimensional`. -/
theorem actual_compact_type_adelicIrrationalRotation_fixed_eigenspace_finiteDimensional_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) (c : ℂ) :
    FiniteDimensional ℂ (Module.End.eigenspace (adelicIrrationalRotation f) c ⊓
      adelicFiniteSubgroupFixedSpace f J : Submodule ℂ (AdelicCyclicHilbert f)) :=
  adelicIrrationalRotation_fixed_eigenspace_finiteDimensional f hf hk J hJ c

/-- Exact original-object consumer of `finiteDimensional_intertwining_of_eigenspaces`. -/
theorem actual_compact_type_finiteDimensional_intertwining_of_eigenspaces_source {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {G : Type*} [Monoid G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (g : G)
    (hg : ∀ c : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (σ g) c)) :
    FiniteDimensional ℂ (Representation.IntertwiningMap ρ σ) :=
  finiteDimensional_intertwining_of_eigenspaces ρ σ g hg

/-- Exact original-object consumer of `adelicFiniteFixedRealRepresentation_eigenspace_finiteDimensional`. -/
theorem actual_compact_type_adelicFiniteFixedRealRepresentation_eigenspace_finiteDimensional_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hf : f ≠ 0) (hk : 0 < k)
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) (c : ℂ) :
    FiniteDimensional ℂ (Module.End.eigenspace
      (adelicFiniteFixedRealRepresentation f J (toGL (realRotationCurve (Real.pi * Real.sqrt 2)))) c) :=
  adelicFiniteFixedRealRepresentation_eigenspace_finiteDimensional f J hf hk hJ c

/-- Exact original-object consumer of `adelicRealType_finiteMultiplicity`. -/
theorem actual_compact_type_adelicRealType_finiteMultiplicity_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ι : G →* GeneralLinearGroup (Fin 2) ℝ) (g : G)
    (hg : ι g = toGL (realRotationCurve (Real.pi * Real.sqrt 2))) (σ : Representation ℂ G V) :
    FiniteDimensional ℂ (Representation.IntertwiningMap σ ((adelicFiniteFixedRealRepresentation f J).comp ι)) :=
  adelicRealType_finiteMultiplicity f hf hk J hJ ι g hg σ

/-- Exact original-object consumer of `adelicOrthogonalType_admissible`. -/
theorem actual_compact_type_adelicOrthogonalType_admissible_source {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k)
    (J : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : Representation ℂ (Matrix.orthogonalGroup (Fin 2) ℝ) V) :
    FiniteDimensional ℂ (Representation.IntertwiningMap σ
      ((adelicFiniteFixedRealRepresentation f J).comp realOrthogonalGL2Embedding)) :=
  adelicOrthogonalType_admissible f hf hk J hJ σ


/-- Exact original-object consumer of `sphericalChebyshevCoefficient_recurrence`. -/
theorem actual_spherical_formula_sphericalChebyshevCoefficient_recurrence_source (q r z : ℂ) (hr : r ≠ 0)
    (hs : r ^ 2 = q) (hq : q + 1 ≠ 0) (n : ℕ) :
    (r * z) * sphericalChebyshevCoefficient q r z (n + 1) =
      sphericalChebyshevCoefficient q r z n + q * sphericalChebyshevCoefficient q r z (n + 2) :=
  sphericalChebyshevCoefficient_recurrence q r z hr hs hq n

/-- Exact original-object consumer of `radial_recurrence_chebyshev_formula`. -/
theorem actual_spherical_formula_radial_recurrence_chebyshev_formula_source (p : ℕ) [NeZero p] (r z : ℂ)
    (hr : r ≠ 0) (hs : r ^ 2 = (p : ℂ)) (φ : ℕ → ℂ)
    (hb : (r * z) * φ 0 = ((p : ℂ) + 1) * φ 1)
    (hrec : ∀ n, (r * z) * φ (n + 1) = φ n + (p : ℂ) * φ (n + 2)) (n : ℕ) :
    φ n = φ 0 * sphericalChebyshevCoefficient p r z n :=
  radial_recurrence_chebyshev_formula p r z hr hs φ hb hrec n

/-- Exact original-object consumer of `sphericalChebyshevCoefficient_satake`. -/
theorem actual_spherical_formula_sphericalChebyshevCoefficient_satake_source {α β : ℂ} (hprod : α * β = 1)
    (q r : ℂ) (n : ℕ) :
    sphericalChebyshevCoefficient q r (α + β) (n + 2) =
      (r ^ (n + 2))⁻¹ *
        (q * satakeSymmetricTrace α β (n + 2) - satakeSymmetricTrace α β n) / (q + 1) :=
  sphericalChebyshevCoefficient_satake hprod q r n

/-- Exact original-object consumer of `primitive_sphericalChebyshevCoefficient_primePower`. -/
theorem actual_spherical_formula_primitive_sphericalChebyshevCoefficient_primePower_source {Q : ℕ} [NeZero Q] {k : ℤ}
    (F : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) (n : ℕ) :
    sphericalChebyshevCoefficient p (Real.sqrt p) (normalizedCuspCoefficients F.toCuspForm p) (n + 2) =
      ((Real.sqrt p : ℂ) ^ (n + 2))⁻¹ *
        ((p : ℂ) * normalizedCuspCoefficients F.toCuspForm (p ^ (n + 2)) -
          normalizedCuspCoefficients F.toCuspForm (p ^ n)) / ((p : ℂ) + 1) :=
  primitive_sphericalChebyshevCoefficient_primePower F hp hpQ n

/-- Exact original-object consumer of `adelicCyclicLocal_primitive_spherical_formula`. -/
theorem actual_spherical_formula_adelicCyclicLocal_primitive_spherical_formula_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    ∃ n : ℕ, inner ℂ x (adelicCyclicLocalRepresentation F.toCuspForm
      (rationalPrimePlace p (Fact.out : p.Prime)) g (adelicCyclicHilbertGenerator F.toCuspForm)) =
      inner ℂ x (adelicCyclicHilbertGenerator F.toCuspForm) *
        sphericalChebyshevCoefficient p (Real.sqrt p) (normalizedCuspCoefficients F.toCuspForm p) n :=
  adelicCyclicLocal_primitive_spherical_formula F hpN x hx g

/-- Exact original-object consumer of `adelicCyclicLocal_primitive_radial_primePowers`. -/
theorem actual_spherical_formula_adelicCyclicLocal_primitive_radial_primePowers_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) (n : ℕ) :
    @finitePlaceRadialCoefficient (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance p inferInstance inferInstance
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      x (adelicCyclicHilbertGenerator F.toCuspForm) (n + 2) =
    inner ℂ x (adelicCyclicHilbertGenerator F.toCuspForm) *
      (((Real.sqrt p : ℂ) ^ (n + 2))⁻¹ *
        ((p : ℂ) * normalizedCuspCoefficients F.toCuspForm (p ^ (n + 2)) -
          normalizedCuspCoefficients F.toCuspForm (p ^ n)) / ((p : ℂ) + 1)) :=
  adelicCyclicLocal_primitive_radial_primePowers F hpN x hx n

/-- Exact original-object consumer of `adelicLocalUnitReference_radial_formula`. -/
theorem actual_spherical_formula_adelicLocalUnitReference_radial_formula_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) (n : ℕ) :
    @finitePlaceRadialCoefficient (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance p inferInstance inferInstance
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicCyclicUnitReference F.toCuspForm) (adelicCyclicUnitReference F.toCuspForm) n =
      sphericalChebyshevCoefficient p (Real.sqrt p) (normalizedCuspCoefficients F.toCuspForm p) n :=
  adelicLocalUnitReference_radial_formula F hpN n

/-- Exact original-object consumer of `finitePlace_unit_spherical_cartan_formula`. -/
theorem actual_spherical_formula_finitePlace_unit_spherical_cartan_formula_source {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hscalar : ∀ u z, ρ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (v : V) (hv : inner ℂ v v = 1)
    (hfixed : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val v = v)
    (z : ℂ) (heigen : @finitePlaceHeckeTrace V inferInstance inferInstance 1 p
      inferInstance inferInstance inferInstance (Nat.coprime_one_right p) ρ v = ((Real.sqrt p : ℂ) * z) • v)
    (u : ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)ˣ) (n : ℕ)
    (l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime))) :
    inner ℂ v (ρ (GeneralLinearGroup.scalar (Fin 2) u * l.val *
      (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
        (finiteAdelicHeckeDiagonal p)) ^ n * r.val) v) =
      sphericalChebyshevCoefficient p (Real.sqrt p) z n :=
  finitePlace_unit_spherical_cartan_formula p ρ hρ hscalar v hv hfixed z heigen u n l r

/-- Exact original-object consumer of `finitePlace_unit_spherical_orbit_gram`. -/
theorem actual_spherical_formula_finitePlace_unit_spherical_orbit_gram_source {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (σ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) W)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hσ : ∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y)
    (hcρ : ∀ u z, ρ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (hcσ : ∀ u z, σ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (v : V) (w : W) (hv : inner ℂ v v = 1) (hw : inner ℂ w w = 1)
    (hvK : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val v = v)
    (hwK : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), σ g.val w = w)
    (z : ℂ)
    (hzv : @finitePlaceHeckeTrace V inferInstance inferInstance 1 p inferInstance inferInstance
      inferInstance (Nat.coprime_one_right p) ρ v = ((Real.sqrt p : ℂ) * z) • v)
    (hzw : @finitePlaceHeckeTrace W inferInstance inferInstance 1 p inferInstance inferInstance
      inferInstance (Nat.coprime_one_right p) σ w = ((Real.sqrt p : ℂ) * z) • w)
    (g h : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    inner ℂ (ρ g v) (ρ h v) = inner ℂ (σ g w) (σ h w) :=
  finitePlace_unit_spherical_orbit_gram p ρ σ hρ hσ hcρ hcσ v w hv hw hvK hwK z hzv hzw g h


section


variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]


/-- Exact source-type consumer of `gramSpanIsometry_range`. -/
theorem actual_spherical_equivalence_gramSpanIsometry_range_source (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j)) :
    (gramSpanIsometry u v h).toLinearMap.range = Submodule.span ℂ (Set.range v) :=
  gramSpanIsometry_range u v h

end

section

open UniformSpace

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]


omit [CompleteSpace E] in

/-- Exact source-type consumer of `gramSpanIsometryCompletion_range`. -/
theorem actual_spherical_equivalence_gramSpanIsometryCompletion_range_source (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j)) :
    (linearIsometryCompletion (gramSpanIsometry u v h)).toLinearMap.range =
      (Submodule.span ℂ (Set.range v)).topologicalClosure :=
  gramSpanIsometryCompletion_range u v h

end

section

open UniformSpace

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]


/-- Exact source-type consumer of `gramDenseFamilyEquiv_intertwines`. -/
theorem actual_spherical_equivalence_gramDenseFamilyEquiv_intertwines_source (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j))
    (hu : (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (τ : ι → ι)
    (hA : ∀ i, A (u i) = u (τ i)) (hB : ∀ i, B (v i) = v (τ i)) (x : E) :
    gramDenseFamilyEquiv u v h hu hv (A x) = B (gramDenseFamilyEquiv u v h hu hv x) :=
  gramDenseFamilyEquiv_intertwines u v h hu hv A B τ hA hB x

end

section



/-- Exact source-type consumer of `closedSpan_subtype_family_dense`. -/
theorem actual_spherical_equivalence_closedSpan_subtype_family_dense_source {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (S : Submodule ℂ E) (u : ι → S)
    (h : (Submodule.span ℂ (Set.range (fun i => (u i).val))).topologicalClosure = S) :
    (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤ :=
  closedSpan_subtype_family_dense S u h

end

section

open IsDedekindDomain Matrix


/-- Exact source-type consumer of `finitePlaceHeckeTrace_good_eq_one`. -/
theorem actual_spherical_equivalence_finitePlaceHeckeTrace_good_eq_one_source {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (hpN : p.Coprime N)
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hscalar : ∀ u z, ρ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (y : V) (hy : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val y = y) :
    finitePlaceHeckeTrace N p hpN ρ y = finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ y :=
  finitePlaceHeckeTrace_good_eq_one N p hpN ρ hρ hscalar y hy

end

section

open IsDedekindDomain Matrix

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (σ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) W)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hσ : ∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y)
    (hcρ : ∀ u z, ρ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (hcσ : ∀ u z, σ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (v : V) (w : W) (hv : inner ℂ v v = 1) (hw : inner ℂ w w = 1)
    (hvK : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val v = v)
    (hwK : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), σ g.val w = w)
    (z : ℂ)
    (hzv : @finitePlaceHeckeTrace V inferInstance inferInstance 1 p inferInstance inferInstance
      inferInstance (Nat.coprime_one_right p) ρ v = ((Real.sqrt p : ℂ) * z) • v)
    (hzw : @finitePlaceHeckeTrace W inferInstance inferInstance 1 p inferInstance inferInstance
      inferInstance (Nat.coprime_one_right p) σ w = ((Real.sqrt p : ℂ) * z) • w)

include hρ hσ hcρ hcσ hv hw hvK hwK hzv hzw


include hρ hσ hcρ hcσ hv hw hvK hwK hzv hzw

/-- Exact source-type consumer of `finitePlaceSphericalCyclicEquiv_intertwines`. -/
theorem actual_spherical_equivalence_finitePlaceSphericalCyclicEquiv_intertwines_source
    (hvcyclic : (Submodule.span ℂ (Set.range (fun g => ρ g v))).topologicalClosure = ⊤)
    (hwcyclic : (Submodule.span ℂ (Set.range (fun g => σ g w))).topologicalClosure = ⊤)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) (x : V) :
    finitePlaceSphericalCyclicEquiv p ρ σ hρ hσ hcρ hcσ v w hv hw hvK hwK z hzv hzw hvcyclic hwcyclic (ρ g x) =
      σ g (finitePlaceSphericalCyclicEquiv p ρ σ hρ hσ hcρ hcσ v w hv hw hvK hwK z hzv hzw hvcyclic hwcyclic x) :=
  finitePlaceSphericalCyclicEquiv_intertwines p ρ σ hρ hσ hcρ hcσ v w hv hw hvK hwK z hzv hzw hvcyclic hwcyclic g x

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)


/-- Exact source-type consumer of `adelicLocalClosedUnitReference_cyclic`. -/
theorem actual_spherical_equivalence_adelicLocalClosedUnitReference_cyclic_source (hf : f ≠ 0) (v : HeightOneSpectrum ℤ) :
    (Submodule.span ℂ (Set.range (fun g =>
      adelicLocalCyclicRepresentation f v g (adelicLocalClosedUnitReference f v)))).topologicalClosure = ⊤ :=
  adelicLocalClosedUnitReference_cyclic f hf v

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)


include hpN

/-- Exact source-type consumer of `adelicLocalClosedUnitReference_hecke_eigen`. -/
theorem actual_spherical_equivalence_adelicLocalClosedUnitReference_hecke_eigen_source :
    finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p)
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
    ((Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p) •
      adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) :=
  adelicLocalClosedUnitReference_hecke_eigen F hpN

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (σ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) W)
    (hσ : ∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y)
    (hcσ : ∀ u x, σ (GeneralLinearGroup.scalar (Fin 2) u) x = x)
    (w : W) (hw : inner ℂ w w = 1)
    (hwK : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), σ g.val w = w)
    (hzw : finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) σ w =
      ((Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p) • w)
    (hwcyclic : (Submodule.span ℂ (Set.range (fun g => σ g w))).topologicalClosure = ⊤)


include hσ hcσ hw hwK hzw hwcyclic

/-- Exact source-type consumer of `adelicLocalSphericalEquiv_intertwines`. -/
theorem actual_spherical_equivalence_adelicLocalSphericalEquiv_intertwines_source
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (x : adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalSphericalEquiv F hpN σ hσ hcσ w hw hwK hzw hwcyclic
      (adelicLocalCyclicRepresentation F.toCuspForm _ g x) =
    σ g (adelicLocalSphericalEquiv F hpN σ hσ hcσ w hw hwK hzw hwcyclic x) :=
  adelicLocalSphericalEquiv_intertwines F hpN σ hσ hcσ w hw hwK hzw hwcyclic g x

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N M p : ℕ} [NeZero N] [NeZero M] [NeZero p] [Fact p.Prime] {k l : ℤ}
    (F : PrimitiveCuspForm N k) (G : PrimitiveCuspForm M l)
    (hpN : p.Coprime N) (hpM : p.Coprime M)
    (h : normalizedCuspCoefficients F.toCuspForm p = normalizedCuspCoefficients G.toCuspForm p)


/-- Exact source-type consumer of `adelicPrimitiveLocalEquiv_intertwines`. -/
theorem actual_spherical_equivalence_adelicPrimitiveLocalEquiv_intertwines_source
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (x : adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicPrimitiveLocalEquiv F G hpN hpM h (adelicLocalCyclicRepresentation F.toCuspForm _ g x) =
      adelicLocalCyclicRepresentation G.toCuspForm _ g (adelicPrimitiveLocalEquiv F G hpN hpM h x) :=
  adelicPrimitiveLocalEquiv_intertwines F G hpN hpM h g x

end


section

open IsDedekindDomain Matrix

variable {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)

/-- The actual fixed-space operator consumes the literal original local coset trace. -/
theorem actual_intrinsic_fixed_hecke_operator_source
    (x : finitePlaceSphericalFixedSpace p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) :
    (finitePlaceSphericalFixedHecke p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) x).val =
      finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p)
        (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) x.val :=
  finitePlaceSphericalFixedHecke_val p _ x

include hpN

/-- The genuine original primitive local factor has exactly one integral-fixed dimension. -/
theorem actual_intrinsic_fixed_dimension_source :
    Module.finrank ℂ (Representation.invariants
      ((adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).comp
        (finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime))).subtype)) = 1 :=
  adelicLocalSphericalFixedSpace_finrank F hpN

/-- Actual trace normalization gives the original Fourier eigenvalue on the proved one-dimensional space. -/
theorem actual_intrinsic_spherical_trace_source :
    LinearMap.trace ℂ (finitePlaceSphericalFixedSpace p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))))
      (finitePlaceSphericalFixedHecke p
        (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) /
      (Real.sqrt p : ℂ) = normalizedCuspCoefficients F.toCuspForm p :=
  adelicLocalNormalizedSphericalTrace_eq_fourier F hpN

/-- The original convergent prime-power series consumes the actual fixed-line Hecke polynomial. -/
theorem actual_intrinsic_hecke_euler_series_source (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    (∑' r : ℕ, normalizedCuspCoefficients F.toCuspForm (p ^ r) * ((p : ℂ) ^ (-s)) ^ r) =
      ((adelicLocalHeckeEulerPolynomial (p := p) F).eval ((p : ℂ) ^ (-s)))⁻¹ :=
  primitive_good_euler_series_intrinsic_trace F hk hpN hs

/-- All symmetric powers of the roots of the original local Hecke quadratic retain the original prime-power Fourier trace. -/
theorem actual_intrinsic_hecke_symmetric_trace_source (r : ℕ) :
    (symmetricEulerPolynomial (adelicLocalHeckeRootPlus (p := p) F)
      (adelicLocalHeckeRootMinus (p := p) F) r).coeff 1 =
      -normalizedCuspCoefficients F.toCuspForm (p ^ r) :=
  adelicLocalHecke_symmetricEulerPolynomial_coeff_one F hpN r

omit hpN [NeZero p] in
/-- The actual orthogonal projector commutes with every original full complementary operator. -/
theorem actual_full_away_fixed_projection_source
    (a : AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (x : AdelicCyclicHilbert F.toCuspForm) :
    adelicLocalFixedProjection F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))
      (adelicCyclicFullAwayRepresentation F.toCuspForm _ a x) =
      adelicCyclicFullAwayRepresentation F.toCuspForm _ a
        (adelicLocalFixedProjection F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) x) :=
  adelicLocalFixedProjection_fullAway_commutes F.toCuspForm _ a x

/-- The entire original global local-fixed space equals the closed actual full complementary orbit span. -/
theorem actual_full_away_fixed_closure_source :
    adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) =
      (Submodule.span ℂ (Set.range (fun a => adelicCyclicFullAwayRepresentation F.toCuspForm
        (rationalPrimePlace p (Fact.out : p.Prime)) a (adelicCyclicHilbertGenerator F.toCuspForm)))).topologicalClosure :=
  adelicLocalFixedSpace_eq_fullAwayClosure F hpN

/-- Actual global fixed vectors, including images under later genuine intertwiners, retain the original Fourier Hecke eigenvalue. -/
theorem actual_full_global_fixed_hecke_source (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalNormalizedHecke F.toCuspForm p (Fact.out : p.Prime) hpN x =
      normalizedCuspCoefficients F.toCuspForm p • x :=
  adelicLocalNormalizedHecke_full_fixed F hpN x hx

end


section

open NumberField IsDedekindDomain Matrix



/-- Exact original source-type consumer of `finiteIdele_integral_factor_unique`. -/
theorem actual_idele_finiteIdele_integral_factor_unique_source (q r : ℚ) (hq : 0 < q) (hr : 0 < r)
    (u v : finiteAdeleIntegerSubringˣ)
    (h : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q * u.val.val =
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) r * v.val.val) : u = v :=
  finiteIdele_integral_factor_unique q r hq hr u v h

end

section

open NumberField IsDedekindDomain Matrix



/-- Exact original source-type consumer of `finiteIdeleIntegralUnitPart_mul`. -/
theorem actual_idele_finiteIdeleIntegralUnitPart_mul_source (a b : (FiniteAdeleRing ℤ ℚ)ˣ) :
    finiteIdeleIntegralUnitPart (a * b) = finiteIdeleIntegralUnitPart a * finiteIdeleIntegralUnitPart b :=
  finiteIdeleIntegralUnitPart_mul a b

end

section

open NumberField IsDedekindDomain Matrix

variable {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)

/-- Exact original source-type consumer of `finiteIdeleDirichletCharacter_integral`. -/
theorem actual_idele_finiteIdeleDirichletCharacter_integral_source (u : finiteAdeleIntegerSubringˣ) :
    finiteIdeleDirichletCharacter χ (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u) =
      (χ (finiteAdeleResidue D u.val))⁻¹ :=
  finiteIdeleDirichletCharacter_integral χ u

end

section

open NumberField IsDedekindDomain Matrix

variable {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)

/-- Exact original source-type consumer of `finiteIdeleDirichletCharacter_continuous`. -/
theorem actual_idele_finiteIdeleDirichletCharacter_continuous_source : Continuous (finiteIdeleDirichletCharacter χ) :=
  finiteIdeleDirichletCharacter_continuous χ

end

section

open NumberField IsDedekindDomain Matrix

variable {D : ℕ} (χ : DirichletCharacter ℂ D)

/-- Exact original source-type consumer of `realDirichletSignCharacter_continuous`. -/
theorem actual_idele_realDirichletSignCharacter_continuous_source : Continuous (realDirichletSignCharacter χ) :=
  realDirichletSignCharacter_continuous χ

end

section

open NumberField IsDedekindDomain Matrix

variable {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)

/-- Exact original source-type consumer of `adelicDirichletCharacter_continuous`. -/
theorem actual_idele_adelicDirichletCharacter_continuous_source : Continuous (adelicDirichletCharacter χ) :=
  adelicDirichletCharacter_continuous χ

end

section

open NumberField IsDedekindDomain Matrix

variable {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)

/-- Exact original source-type consumer of `adelicDirichletCharacter_rational`. -/
theorem actual_idele_adelicDirichletCharacter_rational_source (q : ℚˣ) :
    adelicDirichletCharacter χ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1 :=
  adelicDirichletCharacter_rational χ q

end

section

open NumberField IsDedekindDomain Matrix

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- Exact original source-type consumer of `scalarTwist_intertwining_fixed`. -/
theorem actual_idele_scalarTwist_intertwining_fixed_source (ρ : Representation ℂ G V) (χ : G →* ℂ)
    (T : Representation.IntertwiningMap ρ (scalarTwistRepresentation ρ χ))
    (K : Subgroup G) (hχ : ∀ g : K, χ g.val = 1)
    (x : V) (hx : ∀ g : K, ρ g.val x = x) : ∀ g : K, ρ g.val (T x) = T x :=
  scalarTwist_intertwining_fixed ρ χ T K hχ x hx

end

section

open NumberField IsDedekindDomain Matrix

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (hpN : p.Coprime N)
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (χ : GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) →* ℂ)
    (z : ℂ)
    (hχ : ∀ i : Option (ZMod p), χ
      (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
        ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹)) = z)

include hχ

/-- Exact original source-type consumer of `finitePlaceHeckeTrace_character_intertwines`. -/
theorem actual_idele_finitePlaceHeckeTrace_character_intertwines_source
    (T : Representation.IntertwiningMap ρ (scalarTwistRepresentation ρ χ)) (x : V) :
    T (finitePlaceHeckeTrace N p hpN ρ x) = z • finitePlaceHeckeTrace N p hpN ρ (T x) :=
  finitePlaceHeckeTrace_character_intertwines N p hpN ρ χ z hχ T x

end

section

open NumberField IsDedekindDomain Matrix

variable {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (χ : GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) →* ℂ)
    (T : Representation.IntertwiningMap
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (scalarTwistRepresentation
        (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) χ))

/-- Exact original source-type consumer of `adelicLocalSelfTwist_fourier_relation`. -/
theorem actual_idele_adelicLocalSelfTwist_fourier_relation_source
    (hχK : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), χ g.val = 1)
    (z : ℂ) (hχ : ∀ i : Option (ZMod p), χ
      (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
        ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹)) = z)
    (hT : T (adelicCyclicHilbertGenerator F.toCuspForm) ≠ 0) :
    z * normalizedCuspCoefficients F.toCuspForm p = normalizedCuspCoefficients F.toCuspForm p :=
  adelicLocalSelfTwist_fourier_relation F hpN χ T hχK z hχ hT

end


section

open NumberField IsDedekindDomain Matrix


/-- Exact source consumer of `finiteAdelicLocalGL2_det`. -/
theorem actual_dirichlet_finiteAdelicLocalGL2_det_source (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    GeneralLinearGroup.det (finiteAdelicLocalGL2 v g) = finiteAdeleLocalUnit v (GeneralLinearGroup.det g) :=
  finiteAdelicLocalGL2_det v g

end

section

open NumberField IsDedekindDomain Matrix


/-- Exact source consumer of `finiteIdeleDirichletCharacter_local_integral`. -/
theorem actual_dirichlet_finiteIdeleDirichletCharacter_local_integral_source {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (v : HeightOneSpectrum ℤ) (hD : (D : ℤ) ∉ v.asIdeal)
    (u : (v.adicCompletion ℚ)ˣ) (hu : u.val ∈ v.adicCompletionIntegers ℚ)
    (hui : u.inv ∈ v.adicCompletionIntegers ℚ) :
    finiteIdeleDirichletCharacter χ (finiteAdeleLocalUnit v u) = 1 :=
  finiteIdeleDirichletCharacter_local_integral χ v hD u hu hui

end

section

open NumberField IsDedekindDomain Matrix

variable {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)


/-- Exact source consumer of `adelicDirichletCharacter_norm`. -/
theorem actual_dirichlet_adelicDirichletCharacter_norm_source (a : (AdeleRing ℤ ℚ)ˣ) :
    ‖adelicDirichletCharacter χ a‖ = 1 :=
  adelicDirichletCharacter_norm χ a

end

section

open NumberField IsDedekindDomain Matrix

variable {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)


/-- Exact source consumer of `adelicDirichletDeterminant_rational`. -/
theorem actual_dirichlet_adelicDirichletDeterminant_rational_source (g : GeneralLinearGroup (Fin 2) ℚ) :
    adelicDirichletDeterminant χ (GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) g) = 1 :=
  adelicDirichletDeterminant_rational χ g

end

section

open NumberField IsDedekindDomain Matrix


/-- Exact source consumer of `finiteIdelePrimeAway_residue`. -/
theorem actual_dirichlet_finiteIdelePrimeAway_residue_source (D p : ℕ) [NeZero D] [NeZero p] (hp : p.Prime)
    (hpD : p.Coprime D) :
    finiteAdeleResidue D (finiteIdelePrimeAwayIntegerUnit p hp).val = (p : ZMod D) :=
  finiteIdelePrimeAway_residue D p hp hpD

end

section

open NumberField IsDedekindDomain Matrix


/-- Exact source consumer of `finiteIdeleDirichletCharacter_uniformizer`. -/
theorem actual_dirichlet_finiteIdeleDirichletCharacter_uniformizer_source {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (p : ℕ) [NeZero p] (hp : p.Prime) (hpD : p.Coprime D) :
    finiteIdeleDirichletCharacter χ
      (finiteAdeleLocalUnit (rationalPrimePlace p hp) (finitePlacePrimeUnit p _)) = χ (p : ZMod D) :=
  finiteIdeleDirichletCharacter_uniformizer χ p hp hpD

end

section

open NumberField IsDedekindDomain Matrix


/-- Exact source consumer of `finitePlaceDirichletDeterminant_level`. -/
theorem actual_dirichlet_finitePlaceDirichletDeterminant_level_source {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (N : ℕ) (v : HeightOneSpectrum ℤ)
    (hD : (D : ℤ) ∉ v.asIdeal) (g : finitePlaceGL2Gamma0 N v) :
    finitePlaceDirichletDeterminant χ v g.val = 1 :=
  finitePlaceDirichletDeterminant_level χ N v hD g

end

section

open NumberField IsDedekindDomain Matrix


/-- Exact source consumer of `adelicDirichletDeterminant_local`. -/
theorem actual_dirichlet_adelicDirichletDeterminant_local_source {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    adelicDirichletDeterminant χ (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) =
      finitePlaceDirichletDeterminant χ v g :=
  adelicDirichletDeterminant_local χ v g

end

section

open NumberField IsDedekindDomain Matrix


/-- Exact source consumer of `finitePlaceDirichletDeterminant_hecke_quadratic`. -/
theorem actual_dirichlet_finitePlaceDirichletDeterminant_hecke_quadratic_source {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic) (N p : ℕ) [NeZero N] [NeZero p]
    (hp : p.Prime) (hpN : p.Coprime N) (hpD : p.Coprime D) (i : Option (ZMod p)) :
    finitePlaceDirichletDeterminant χ (rationalPrimePlace p hp)
      (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
        ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹)) = χ (p : ZMod D) :=
  finitePlaceDirichletDeterminant_hecke_quadratic χ hχ N p hp hpN hpD i

end

section

open NumberField IsDedekindDomain Matrix

variable {N D : ℕ} [NeZero N] [NeZero D] {k : ℤ}
    (F : PrimitiveCuspForm N k) (χ : DirichletCharacter ℂ D)
    (T : Representation.IntertwiningMap (adelicCyclicHilbertRepresentation F.toCuspForm)
      (scalarTwistRepresentation (adelicCyclicHilbertRepresentation F.toCuspForm)
        (adelicDirichletDeterminant χ)))


/-- Exact source consumer of `adelicDirichletSelfTwist_classical`. -/
theorem actual_dirichlet_adelicDirichletSelfTwist_classical_source (hχ : χ.IsQuadratic) (hT : Function.Injective T) :
    IsCoefficientSelfTwist N χ (cuspCoefficients F.toCuspForm) :=
  adelicDirichletSelfTwist_classical F χ T hχ hT

end

section

open NumberField IsDedekindDomain Matrix


/-- Exact source consumer of `nonCM_no_adelicDirichletSelfTwist`. -/
theorem actual_dirichlet_nonCM_no_adelicDirichletSelfTwist_source {N : ℕ} [NeZero N] {k : ℤ}
    (F : NonCMPrimitiveCuspForm N k) (D : ℕ+) (χ : DirichletCharacter ℂ D)
    (hχp : χ.IsPrimitive) (hχne : χ ≠ 1) (hχq : χ.IsQuadratic)
    (T : Representation.IntertwiningMap (adelicCyclicHilbertRepresentation F.toCuspForm)
      (scalarTwistRepresentation (adelicCyclicHilbertRepresentation F.toCuspForm)
        (adelicDirichletDeterminant χ))) : ¬ Function.Injective T :=
  nonCM_no_adelicDirichletSelfTwist F D χ hχp hχne hχq T

end

section

open NumberField IsDedekindDomain Matrix Filter Set Topology


/-- Exact source consumer of `realQuadraticCharacter_negative`. -/
theorem actual_classification_realQuadraticCharacter_negative_source (ψ : ℝˣ →* ℂ) (hψ : ∀ u, ψ u ^ 2 = 1)
    (u : ℝˣ) (hu : u.val < 0) : ψ u = ψ (-1) :=
  realQuadraticCharacter_negative ψ hψ u hu

end

section

open NumberField IsDedekindDomain Matrix Filter Set Topology


/-- Exact source consumer of `rationalIdele_principal_factor`. -/
theorem actual_classification_rationalIdele_principal_factor_source (q : ℚˣ) :
    Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q =
      rationalIdeleRealEmbedding (Units.map (Rat.castHom ℝ).toMonoidHom q) *
        rationalIdeleFiniteEmbedding (Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom q) :=
  rationalIdele_principal_factor q

end

section

open NumberField IsDedekindDomain Matrix Filter Set Topology


/-- Exact source consumer of `finiteAdeleResidue_units_surjective`. -/
theorem actual_classification_finiteAdeleResidue_units_surjective_source (D : ℕ) [NeZero D] :
    Function.Surjective (Units.map (finiteAdeleResidue D).toMonoidHom) :=
  finiteAdeleResidue_units_surjective D

end

section

open NumberField IsDedekindDomain Matrix Filter Set Topology

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] [Infinite R]


/-- Exact source consumer of `compactRing_positive_integer_ideal_small`. -/
theorem actual_classification_compactRing_positive_integer_ideal_small_source (hd : DenseRange (Int.cast : ℤ → R))
    (U : Set R) (hU : U ∈ 𝓝 (0 : R)) :
    ∃ D : ℕ, 0 < D ∧ ∀ x : R, (D : R) * x ∈ U :=
  compactRing_positive_integer_ideal_small hd U hU

end

section

open NumberField IsDedekindDomain Matrix Filter Set Topology


/-- Exact source consumer of `finiteAdeleLevelMultiple_cofinal`. -/
theorem actual_classification_finiteAdeleLevelMultiple_cofinal_source (U : Set (FiniteAdeleRing ℤ ℚ)) (hU : U ∈ 𝓝 0) :
    ∃ D : ℕ, 0 < D ∧ ∀ x, finiteAdeleLevelMultiple D x → x ∈ U :=
  finiteAdeleLevelMultiple_cofinal U hU

end

section

open NumberField IsDedekindDomain Matrix Filter Set Topology

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] [Infinite R]


/-- Exact source consumer of `compactRing_unit_congruence_small`. -/
theorem actual_classification_compactRing_unit_congruence_small_source (hd : DenseRange (Int.cast : ℤ → R))
    (W : Set Rˣ) (hW : W ∈ 𝓝 1) :
    ∃ D : ℕ, 0 < D ∧ ∀ u : Rˣ, (D : R) ∣ u.val - 1 → u ∈ W :=
  compactRing_unit_congruence_small hd W hW

end

section

open NumberField IsDedekindDomain Matrix Filter Set Topology


/-- Exact source consumer of `integralIdele_quadratic_congruence`. -/
theorem actual_classification_integralIdele_quadratic_congruence_source {ψ : finiteAdeleIntegerSubringˣ →* ℂ}
    (hc : Continuous ψ) (hq : ∀ u, ψ u ^ 2 = 1) :
    ∃ D : ℕ, ∃ hD : 0 < D, ∀ u : finiteAdeleIntegerSubringˣ,
      @finiteAdeleResidue D ⟨ne_of_gt hD⟩ u.val = 1 → ψ u = 1 :=
  integralIdele_quadratic_congruence hc hq

end

section

open NumberField IsDedekindDomain Matrix Filter Set Topology


/-- Exact source consumer of `integralIdele_quadratic_dirichlet_exists`. -/
theorem actual_classification_integralIdele_quadratic_dirichlet_exists_source
    (φ : finiteAdeleIntegerSubringˣ →* ℂ) (hc : Continuous φ) (hq : ∀ u, φ u ^ 2 = 1) :
    ∃ D : ℕ, ∃ hD : 0 < D, ∃ χ : DirichletCharacter ℂ D,
      χ.IsQuadratic ∧ ∀ u : finiteAdeleIntegerSubringˣ,
        χ (@finiteAdeleResidue D ⟨ne_of_gt hD⟩ u.val) = φ u :=
  integralIdele_quadratic_dirichlet_exists φ hc hq

end

section

open NumberField IsDedekindDomain Matrix

/-- Exact source consumer of `adelicQuadraticCharacter_coordinate_value`. -/
theorem actual_fullCharacter_adelicQuadraticCharacter_coordinate_value_source (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hq : ∀ a, ψ a ^ 2 = 1)
    (hp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (a : (AdeleRing ℤ ℚ)ˣ) :
    ψ a = ψ (rationalIdeleRealEmbedding (rationalIdeleRealHom a)) *
      ψ (rationalIdeleFiniteEmbedding (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom
        (finiteIdeleIntegralUnitPart (rationalIdeleFiniteHom a)))) :=
  adelicQuadraticCharacter_coordinate_value ψ hq hp a

end

section

open NumberField IsDedekindDomain Matrix

/-- Exact source consumer of `adelicQuadraticCharacter_eq_of_integral`. -/
theorem actual_fullCharacter_adelicQuadraticCharacter_eq_of_integral_source
    (ψ φ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hψq : ∀ a, ψ a ^ 2 = 1) (hφq : ∀ a, φ a ^ 2 = 1)
    (hψp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (hφp : ∀ q : ℚˣ, φ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (hi : ∀ u : finiteAdeleIntegerSubringˣ,
      ψ (rationalIdeleFiniteEmbedding (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u)) =
        φ (rationalIdeleFiniteEmbedding (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u))) : ψ = φ :=
  adelicQuadraticCharacter_eq_of_integral ψ φ hψq hφq hψp hφp hi

end

section

open NumberField IsDedekindDomain Matrix

/-- Exact source consumer of `adelicDirichletCharacter_quadratic`. -/
theorem actual_fullCharacter_adelicDirichletCharacter_quadratic_source {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic) (a : (AdeleRing ℤ ℚ)ˣ) :
    adelicDirichletCharacter χ a ^ 2 = 1 :=
  adelicDirichletCharacter_quadratic χ hχ a

end

section

open NumberField IsDedekindDomain Matrix

/-- Exact source consumer of `adelicQuadraticCharacter_dirichlet_exists`. -/
theorem actual_fullCharacter_adelicQuadraticCharacter_dirichlet_exists_source (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hc : Continuous ψ) (hq : ∀ a, ψ a ^ 2 = 1)
    (hp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1) :
    ∃ D : ℕ+, ∃ χ : DirichletCharacter ℂ D, χ.IsQuadratic ∧ ψ = adelicDirichletCharacter χ :=
  adelicQuadraticCharacter_dirichlet_exists ψ hc hq hp

end

section

open NumberField IsDedekindDomain Matrix

/-- Exact source consumer of `dirichlet_changeLevel_integral_residue`. -/
theorem actual_fullCharacter_dirichlet_changeLevel_integral_residue_source {M D : ℕ} [NeZero M] [NeZero D]
    (χ : DirichletCharacter ℂ M) (h : M ∣ D) (u : finiteAdeleIntegerSubringˣ) :
    DirichletCharacter.changeLevel h χ (finiteAdeleResidue D u.val) = χ (finiteAdeleResidue M u.val) :=
  dirichlet_changeLevel_integral_residue χ h u

end

section

open NumberField IsDedekindDomain Matrix

/-- Exact source consumer of `adelicDirichletCharacter_primitive`. -/
theorem actual_fullCharacter_adelicDirichletCharacter_primitive_source {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    adelicDirichletCharacter χ.primitiveCharacter = adelicDirichletCharacter χ :=
  adelicDirichletCharacter_primitive χ hχ

end

section

open NumberField IsDedekindDomain Matrix

/-- Exact source consumer of `adelicQuadraticCharacter_primitive_exists`. -/
theorem actual_fullCharacter_adelicQuadraticCharacter_primitive_exists_source (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hc : Continuous ψ) (hq : ∀ a, ψ a ^ 2 = 1)
    (hp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (hne : ψ ≠ 1) :
    ∃ D : ℕ+, ∃ χ : DirichletCharacter ℂ D,
      χ.IsPrimitive ∧ χ ≠ 1 ∧ χ.IsQuadratic ∧ ψ = adelicDirichletCharacter χ :=
  adelicQuadraticCharacter_primitive_exists ψ hc hq hp hne

end

section

open NumberField IsDedekindDomain Matrix

/-- Exact source consumer of `nonCM_no_adelicQuadraticSelfTwist`. -/
theorem actual_fullCharacter_nonCM_no_adelicQuadraticSelfTwist_source {N : ℕ} [NeZero N] {k : ℤ}
    (F : NonCMPrimitiveCuspForm N k) (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hc : Continuous ψ) (hq : ∀ a, ψ a ^ 2 = 1)
    (hp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (hne : ψ ≠ 1)
    (T : Representation.IntertwiningMap (adelicCyclicHilbertRepresentation F.toCuspForm)
      (scalarTwistRepresentation (adelicCyclicHilbertRepresentation F.toCuspForm)
        (ψ.comp GeneralLinearGroup.det))) : ¬ Function.Injective T :=
  nonCM_no_adelicQuadraticSelfTwist F ψ hc hq hp hne T

end

section

open NumberField IsDedekindDomain Matrix

/-- Exact source consumer of `adelicSelfTwist_quadratic`. -/
theorem actual_fullCharacter_adelicSelfTwist_quadratic_source {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (T : Representation.IntertwiningMap (adelicCyclicHilbertRepresentation F.toCuspForm)
      (scalarTwistRepresentation (adelicCyclicHilbertRepresentation F.toCuspForm)
        (ψ.comp GeneralLinearGroup.det))) (hT : Function.Injective T) :
    ∀ a, ψ a ^ 2 = 1 :=
  adelicSelfTwist_quadratic F ψ T hT

end

section

open NumberField IsDedekindDomain Matrix

/-- Exact source consumer of `nonCM_no_adelicSelfTwist`. -/
theorem actual_fullCharacter_nonCM_no_adelicSelfTwist_source {N : ℕ} [NeZero N] {k : ℤ}
    (F : NonCMPrimitiveCuspForm N k) (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hc : Continuous ψ)
    (hp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (hne : ψ ≠ 1)
    (T : Representation.IntertwiningMap (adelicCyclicHilbertRepresentation F.toCuspForm)
      (scalarTwistRepresentation (adelicCyclicHilbertRepresentation F.toCuspForm)
        (ψ.comp GeneralLinearGroup.det))) : ¬ Function.Injective T :=
  nonCM_no_adelicSelfTwist F ψ hc hp hne T

end

section

open NumberField IsDedekindDomain Matrix

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Exact source consumer of `smoothInducedCharacterRepresentation_smooth`. -/
theorem actual_induced_smoothInducedCharacterRepresentation_smooth_source (B : Subgroup G) (χ : B →* ℂ)
    (f : smoothInducedCharacterSpace B χ) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧
      ∀ h ∈ H, smoothInducedCharacterRepresentation B χ h f = f :=
  smoothInducedCharacterRepresentation_smooth B χ f

end

section

open NumberField IsDedekindDomain Matrix

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (B K : Subgroup G) (χ : B →* ℂ)
    (hdec : ∀ g : G, ∃ b : B, ∃ k : K, g = b.val * k.val)

/-- Exact source consumer of `iwasawaInducedSection_fixed_line`. -/
theorem actual_induced_iwasawaInducedSection_fixed_line_source (hK : IsOpen (K : Set G))
    (hχ : ∀ b : B, b.val ∈ K → χ b = 1)
    (f : smoothInducedCharacterSpace B χ)
    (hf : ∀ k : K, smoothInducedCharacterRepresentation B χ k.val f = f) :
    f = f.val 1 • iwasawaInducedSection B K χ hdec hK hχ :=
  iwasawaInducedSection_fixed_line B K χ hdec hK hχ f hf

end

section

open NumberField IsDedekindDomain Matrix



/-- Exact source consumer of `valuationSubring_gl2_firstRow_pivot`. -/
theorem actual_induced_valuationSubring_gl2_firstRow_pivot_source {K : Type*} [Field K] (A : ValuationSubring K)
    (g : GeneralLinearGroup (Fin 2) K) :
    ∃ j : Fin 2, g.val 0 j ≠ 0 ∧ ∀ s : Fin 2, g.val 0 s / g.val 0 j ∈ A :=
  valuationSubring_gl2_firstRow_pivot A g

end

section

open NumberField IsDedekindDomain Matrix



/-- Exact source consumer of `finitePlaceGL2_iwasawa`. -/
theorem actual_induced_finitePlaceGL2_iwasawa_source (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    ∃ b : gl2UpperZeroSubgroup (v.adicCompletion ℚ), ∃ k : finitePlaceGL2Gamma0 1 v,
      g = b.val * k.val :=
  finitePlaceGL2_iwasawa v g

end

section

open NumberField IsDedekindDomain Matrix



/-- Exact source consumer of `finitePlaceUnramifiedCharacter_prime`. -/
theorem actual_induced_finitePlaceUnramifiedCharacter_prime_source (p : ℕ) [NeZero p] (hp : p.Prime) (z : ℂˣ) :
    finitePlaceUnramifiedCharacter (rationalPrimePlace p hp) z
      (finitePlacePrimeUnit p (rationalPrimePlace p hp)) = z :=
  finitePlaceUnramifiedCharacter_prime p hp z

end

section

open NumberField IsDedekindDomain Matrix



/-- Exact source consumer of `finitePlaceLowerCharacter_integral`. -/
theorem actual_induced_finitePlaceLowerCharacter_integral_source (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (b : gl2UpperZeroSubgroup (v.adicCompletion ℚ)) (hb : b.val ∈ finitePlaceGL2Gamma0 1 v) :
    finitePlaceLowerCharacter v z₁ z₂ b = 1 :=
  finitePlaceLowerCharacter_integral v z₁ z₂ b hb

end

section

open NumberField IsDedekindDomain Matrix



/-- Exact source consumer of `finitePlaceInducedSpherical_fixed_line`. -/
theorem actual_induced_finitePlaceInducedSpherical_fixed_line_source (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (f : FinitePlaceInducedSpace v z₁ z₂)
    (hf : ∀ k : finitePlaceGL2Gamma0 1 v,
      smoothInducedCharacterRepresentation _ (finitePlaceLowerCharacter v z₁ z₂) k.val f = f) :
    f = f.val 1 • finitePlaceInducedSpherical v z₁ z₂ :=
  finitePlaceInducedSpherical_fixed_line v z₁ z₂ f hf

end

section

open NumberField IsDedekindDomain Matrix



/-- Exact source consumer of `normalizedLocalPrincipalRepresentation_scalar`. -/
theorem actual_induced_normalizedLocalPrincipalRepresentation_scalar_source (v : HeightOneSpectrum ℤ) (α β : ℂˣ)
    (hαβ : α * β = 1) (u : (v.adicCompletion ℚ)ˣ)
    (f : NormalizedLocalPrincipalSeries v α β) :
    normalizedLocalPrincipalRepresentation v α β (GeneralLinearGroup.scalar (Fin 2) u) f = f :=
  normalizedLocalPrincipalRepresentation_scalar v α β hαβ u f

end

section

/-- Exact source consumer of `primitiveSatake_non_special`. -/
theorem actual_induced_primitiveSatake_non_special_source {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hk : 2 ≤ k) {p : ℕ} (hp : p.Prime) (hpN : ¬p ∣ N) :
    primitiveSatakePlus F p / primitiveSatakeMinus F p ≠ (p : ℂ) ∧
      primitiveSatakePlus F p / primitiveSatakeMinus F p ≠ (p : ℂ)⁻¹ :=
  primitiveSatake_non_special F hk hp hpN

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (B : Subgroup G) (χ : B →* ℂ)
    (hρ : ∀ x : V, ∃ H : Subgroup G, IsOpen (H : Set G) ∧ ∀ h ∈ H, ρ h x = x)
    (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ b : B, ∀ x : V, ℓ (ρ b.val x) = χ b * ℓ x)

/-- Exact source consumer of `smoothInducedFrobeniusMap_injective`. -/
theorem actual_induced_hecke_smoothInducedFrobeniusMap_injective_source [ρ.IsIrreducible] (hne : ℓ ≠ 0) :
    Function.Injective (smoothInducedFrobeniusMap ρ B χ hρ ℓ hℓ) :=
  smoothInducedFrobeniusMap_injective ρ B χ hρ ℓ hℓ hne

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- Exact source consumer of `finitePlaceInducedSpherical_diagonal`. -/
theorem actual_induced_hecke_finitePlaceInducedSpherical_diagonal_source (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (a b : (v.adicCompletion ℚ)ˣ) :
    (finitePlaceInducedSpherical v z₁ z₂).val (gl2UnitDiagonalPair a b) =
      ((finitePlaceUnramifiedCharacter v z₁ a * finitePlaceUnramifiedCharacter v z₂ b : ℂˣ) : ℂ) :=
  finitePlaceInducedSpherical_diagonal v z₁ z₂ a b

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- Exact source consumer of `gl2_upper_inverse_diagonal_factor`. -/
theorem actual_induced_hecke_gl2_upper_inverse_diagonal_factor_source {F : Type*} [Field F] (a q : Fˣ) :
    toGL (ringUpperUnipotent (-a.val)) * gl2UnitDiagonalPair 1 q⁻¹ =
      (toGL (ringLowerUnipotent (-(a⁻¹).val)) * gl2UnitDiagonalPair (-a * q⁻¹) a⁻¹) *
        (toGL (ringUpperUnipotent (-(q * a⁻¹).val)) * gl2CoordinateSwap) :=
  gl2_upper_inverse_diagonal_factor a q

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- Exact source consumer of `finitePlaceInducedSpherical_upper_inverse`. -/
theorem actual_induced_hecke_finitePlaceInducedSpherical_upper_inverse_source (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (a q : (v.adicCompletion ℚ)ˣ)
    (ha : a.val ∈ v.adicCompletionIntegers ℚ)
    (hai : a.inv ∈ v.adicCompletionIntegers ℚ)
    (hq : q.val ∈ v.adicCompletionIntegers ℚ) :
    (finitePlaceInducedSpherical v z₁ z₂).val
      (toGL (ringUpperUnipotent (-a.val)) * gl2UnitDiagonalPair 1 q⁻¹) =
      ((finitePlaceUnramifiedCharacter v z₁ q)⁻¹ : ℂˣ) :=
  finitePlaceInducedSpherical_upper_inverse v z₁ z₂ a q ha hai hq

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- Exact source consumer of `finitePlaceHecke_none_inverse_pair`. -/
theorem actual_induced_hecke_finitePlaceHecke_none_inverse_pair_source (p : ℕ) [NeZero p] (hp : p.Prime)
    (v : HeightOneSpectrum ℤ) :
    (finitePlaceHeckeGamma 1 p (Nat.coprime_one_right p) v none)⁻¹ *
      (GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p))⁻¹ =
    (toGL (ringLowerUnipotent (p : v.adicCompletion ℚ)) *
      gl2UnitDiagonalPair (finitePlacePrimeUnit p v)⁻¹ (-1)) * gl2CoordinateSwap :=
  finitePlaceHecke_none_inverse_pair p hp v

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- Exact source consumer of `finitePlaceInducedSpherical_hecke_nonzero`. -/
theorem actual_induced_hecke_finitePlaceInducedSpherical_hecke_nonzero_source (p : ℕ) [NeZero p] (hp : p.Prime)
    (z₁ z₂ : ℂˣ) (a : ZMod p) (ha : a ≠ 0) :
    (finitePlaceInducedSpherical (rationalPrimePlace p hp) z₁ z₂).val
      ((finitePlaceHeckeGamma 1 p (Nat.coprime_one_right p) (rationalPrimePlace p hp) (some a))⁻¹ *
        (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
          (finiteAdelicHeckeDiagonal p))⁻¹) = (z₁⁻¹ : ℂˣ) :=
  finitePlaceInducedSpherical_hecke_nonzero p hp z₁ z₂ a ha

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- Exact source consumer of `finitePlaceInducedSpherical_hecke_eigenvalue`. -/
theorem actual_induced_hecke_finitePlaceInducedSpherical_hecke_eigenvalue_source (p : ℕ) [NeZero p] [Fact p.Prime]
    (z₁ z₂ : ℂˣ) :
    finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p)
      (smoothInducedCharacterRepresentation _
        (finitePlaceLowerCharacter (rationalPrimePlace p (Fact.out : p.Prime)) z₁ z₂))
      (finitePlaceInducedSpherical (rationalPrimePlace p (Fact.out : p.Prime)) z₁ z₂) =
    ((p : ℂ) * (z₁⁻¹ : ℂˣ) + (z₂⁻¹ : ℂˣ)) •
      finitePlaceInducedSpherical (rationalPrimePlace p (Fact.out : p.Prime)) z₁ z₂ :=
  finitePlaceInducedSpherical_hecke_eigenvalue p z₁ z₂

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- Exact source consumer of `normalizedLocalPrincipal_hecke_eigenvalue`. -/
theorem actual_induced_hecke_normalizedLocalPrincipal_hecke_eigenvalue_source (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β : ℂˣ) :
    finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p)
      (normalizedLocalPrincipalRepresentation (rationalPrimePlace p (Fact.out : p.Prime)) α β)
      (finitePlaceInducedSpherical (rationalPrimePlace p (Fact.out : p.Prime))
        (α * finitePlaceSqrtResidueUnit (rationalPrimePlace p (Fact.out : p.Prime)))
        (β * (finitePlaceSqrtResidueUnit (rationalPrimePlace p (Fact.out : p.Prime)))⁻¹)) =
    ((Real.sqrt p : ℂ) * (((α⁻¹ : ℂˣ) : ℂ) + (β⁻¹ : ℂˣ))) •
      finitePlaceInducedSpherical (rationalPrimePlace p (Fact.out : p.Prime))
        (α * finitePlaceSqrtResidueUnit (rationalPrimePlace p (Fact.out : p.Prime)))
        (β * (finitePlaceSqrtResidueUnit (rationalPrimePlace p (Fact.out : p.Prime)))⁻¹) :=
  normalizedLocalPrincipal_hecke_eigenvalue p α β

end

section

open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- Exact source consumer of `primitiveLocalInducedSpherical_hecke`. -/
theorem actual_induced_hecke_primitiveLocalInducedSpherical_hecke_source {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) [NeZero p] [Fact p.Prime] :
    finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p)
      (normalizedLocalPrincipalRepresentation (rationalPrimePlace p (Fact.out : p.Prime))
        (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p))
      (primitiveLocalInducedSpherical F p Fact.out) =
    ((Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p) •
      primitiveLocalInducedSpherical F p Fact.out :=
  primitiveLocalInducedSpherical_hecke F p

end


section

open IsDedekindDomain Matrix MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Exact source consumer of `smoothInducedCharacter_continuous`. -/
theorem actual_induced_coefficient_smoothInducedCharacter_continuous_source (B : Subgroup G) (χ : B →* ℂ)
    (f : smoothInducedCharacterSpace B χ) : Continuous f.val :=
  smoothInducedCharacter_continuous B χ f

end

section

open IsDedekindDomain Matrix MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (B K : Subgroup G) (χ : B →* ℂ) [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]

/-- Exact source consumer of `smoothInducedCompactAverage_fixed`. -/
theorem actual_induced_coefficient_smoothInducedCompactAverage_fixed_source [IsProbabilityMeasure μ]
    (f : smoothInducedCharacterSpace B χ)
    (hf : ∀ k : K, smoothInducedCharacterRepresentation B χ k.val f = f) :
    smoothInducedCompactAverage B K χ μ f = f.val 1 :=
  smoothInducedCompactAverage_fixed B K χ μ f hf

end

section

open IsDedekindDomain Matrix MeasureTheory

/-- Exact source consumer of `finitePlaceInducedAverage_spherical`. -/
theorem actual_induced_coefficient_finitePlaceInducedAverage_spherical_source (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ) :
    finitePlaceInducedAverage v z₁ z₂ (finitePlaceInducedSpherical v z₁ z₂) = 1 :=
  finitePlaceInducedAverage_spherical v z₁ z₂

end

section

open IsDedekindDomain Matrix MeasureTheory

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) (ℓ : V →ₗ[ℂ] ℂ)
    (hℓ : ∀ k : K, ∀ x : V, ℓ (ρ k.val x) = ℓ x)
    (y : V) (hy : ∀ k : K, ρ k.val y = y)

include hℓ hy

/-- Exact source consumer of `sphericalFunctional_scalar_double_coset`. -/
theorem actual_induced_coefficient_sphericalFunctional_scalar_double_coset_source (c a : G)
    (hc : ∀ x : V, ρ c x = x) (l r : K) :
    ℓ (ρ (c * l.val * a * r.val) y) = ℓ (ρ a y) :=
  sphericalFunctional_scalar_double_coset ρ K ℓ hℓ y hy c a hc l r

end

section

open IsDedekindDomain Matrix MeasureTheory

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (ℓ : V →ₗ[ℂ] ℂ) (y : V)

variable
    (hℓ : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)),
      ∀ x : V, ℓ (ρ k.val x) = ℓ x)
    (hy : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ k.val y = y)

include hℓ hy

/-- Exact source consumer of `finitePlaceFunctionalRadial_forward`. -/
theorem actual_induced_coefficient_finitePlaceFunctionalRadial_forward_source (n : ℕ) (i : Option (ZMod p))
    (hi : i ≠ some 0) :
    ℓ (ρ (finitePlaceHeckeRadialMatrix 1 p (Nat.coprime_one_right p)
      (rationalPrimePlace p (Fact.out : p.Prime)) n i) y) =
      finitePlaceFunctionalRadial p ρ ℓ y (n + 1) :=
  finitePlaceFunctionalRadial_forward p ρ ℓ y hℓ hy n i hi

end

section

open IsDedekindDomain Matrix MeasureTheory

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (ℓ : V →ₗ[ℂ] ℂ) (y : V)
    (hℓ : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)),
      ∀ x : V, ℓ (ρ k.val x) = ℓ x)
    (hy : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ k.val y = y)
    (hc : ∀ u x, ρ (GeneralLinearGroup.scalar (Fin 2) u) x = x)

include hℓ hy hc

/-- Exact source consumer of `finitePlaceFunctionalHecke_eigen_recurrence`. -/
theorem actual_induced_coefficient_finitePlaceFunctionalHecke_eigen_recurrence_source (μ : ℂ)
    (heigen : finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ y = μ • y) :
    μ * finitePlaceFunctionalRadial p ρ ℓ y 0 =
      ((p : ℂ) + 1) * finitePlaceFunctionalRadial p ρ ℓ y 1 ∧
    ∀ n, μ * finitePlaceFunctionalRadial p ρ ℓ y (n + 1) =
      finitePlaceFunctionalRadial p ρ ℓ y n +
        (p : ℂ) * finitePlaceFunctionalRadial p ρ ℓ y (n + 2) :=
  finitePlaceFunctionalHecke_eigen_recurrence p ρ ℓ y hℓ hy hc μ heigen

end

section

open IsDedekindDomain Matrix MeasureTheory

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (ℓ : V →ₗ[ℂ] ℂ) (y : V)
    (hℓ : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)),
      ∀ x : V, ℓ (ρ k.val x) = ℓ x)
    (hy : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ k.val y = y)
    (hc : ∀ u x, ρ (GeneralLinearGroup.scalar (Fin 2) u) x = x)
    (hn : ℓ y = 1) (z : ℂ)
    (heigen : finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ y =
      ((Real.sqrt p : ℂ) * z) • y)

include hℓ hy hc hn heigen

/-- Exact source consumer of `finitePlaceFunctional_unitary_unique`. -/
theorem actual_induced_coefficient_finitePlaceFunctional_unitary_unique_source {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W]
    (σ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) W)
    (hσ : ∀ g a b, inner ℂ (σ g a) (σ g b) = inner ℂ a b)
    (hσc : ∀ u a, σ (GeneralLinearGroup.scalar (Fin 2) u) a = a)
    (w : W) (hw : inner ℂ w w = 1)
    (hwK : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), σ k.val w = w)
    (hwT : finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) σ w =
      ((Real.sqrt p : ℂ) * z) • w)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    ℓ (ρ g y) = inner ℂ w (σ g w) :=
  finitePlaceFunctional_unitary_unique p ρ ℓ y hℓ hy hc hn z heigen σ hσ hσc w hw hwK hwT g

end

section

open IsDedekindDomain Matrix MeasureTheory

variable {G V W : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (v : V) (w : W) (ℓ : W →ₗ[ℂ] ℂ)
    (hcoeff : ∀ g, ℓ (σ g w) = inner ℂ v (ρ g v))

include hρ hcoeff

/-- Exact source consumer of `sphericalCoefficient_linearCombination_ker_le`. -/
theorem actual_induced_coefficient_sphericalCoefficient_linearCombination_ker_le_source :
    (Finsupp.linearCombination ℂ (fun g => σ g w)).ker ≤
      (Finsupp.linearCombination ℂ (fun g => ρ g v)).ker :=
  sphericalCoefficient_linearCombination_ker_le ρ σ hρ v w ℓ hcoeff

end

section

open IsDedekindDomain Matrix MeasureTheory

/-- Exact source consumer of `primitiveLocalInduced_smooth_coefficient`. -/
theorem actual_induced_coefficient_primitiveLocalInduced_smooth_coefficient_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    primitiveLocalInducedAverage F p Fact.out
      (normalizedLocalPrincipalRepresentation (rationalPrimePlace p (Fact.out : p.Prime))
        (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p) g
        (primitiveLocalInducedSpherical F p Fact.out)) =
    inner ℂ (adelicLocalUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g
        (adelicLocalUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) :=
  primitiveLocalInduced_smooth_coefficient F hpN g

end


section

open IsDedekindDomain Matrix

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V)

/-- Exact original-object consumer of `representation_orbit_linearCombination`. -/
theorem actual_induced_quotient_representation_orbit_linearCombination_source (g : G) (a : G →₀ ℂ) :
    ρ g (Finsupp.linearCombination ℂ (fun h => ρ h v) a) =
      Finsupp.linearCombination ℂ (fun h => ρ h v) (a.mapDomain (fun h => g * h)) :=
  representation_orbit_linearCombination ρ v g a

end

section

open IsDedekindDomain Matrix

variable {G V W : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (v : V) (w : W) (ℓ : W →ₗ[ℂ] ℂ)
    (hcoeff : ∀ g, ℓ (σ g w) = inner ℂ v (ρ g v))

/-- Exact original-object consumer of `sphericalCoefficientIntertwiner_surjective`. -/
theorem actual_induced_quotient_sphericalCoefficientIntertwiner_surjective_source
    (hspan : Submodule.span ℂ (Set.range (fun g => ρ g v)) = ⊤) :
    Function.Surjective (sphericalCoefficientIntertwiner ρ σ hρ v w ℓ hcoeff) :=
  sphericalCoefficientIntertwiner_surjective ρ σ hρ v w ℓ hcoeff hspan

end

section

open IsDedekindDomain Matrix

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (T : Representation.IntertwiningMap ρ σ)

/-- Exact original-object consumer of `intertwiningQuotientEquiv_intertwines`. -/
theorem actual_induced_quotient_intertwiningQuotientEquiv_intertwines_source (hs : Function.Surjective T)
    (g : G) (x : V ⧸ T.toLinearMap.ker) :
    T.toLinearMap.quotKerEquivOfSurjective hs (intertwiningQuotientRepresentation ρ σ T g x) =
      σ g (T.toLinearMap.quotKerEquivOfSurjective hs x) :=
  intertwiningQuotientEquiv_intertwines ρ σ T hs g x

end

section

open IsDedekindDomain Matrix

/-- Exact original-object consumer of `primitiveLocalInduced_spherical_constituent`. -/
theorem actual_induced_quotient_primitiveLocalInduced_spherical_constituent_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    Nonempty (Representation.Equiv (primitiveLocalInducedQuotientRepresentation F hpN)
      (adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) ∧
      (adelicLocalSmoothRepresentation F.toCuspForm
        (rationalPrimePlace p (Fact.out : p.Prime))).IsIrreducible :=
  primitiveLocalInduced_spherical_constituent F hpN

end

section

open IsDedekindDomain Matrix

/-- Exact original-object consumer of `homogeneousMatrixAction_diagonal_monomial`. -/
theorem actual_induced_quotient_homogeneousMatrixAction_diagonal_monomial_source {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (n : ℕ) (d : ι →₀ ℕ) (hd : d.degree = n) :
    homogeneousMatrixAction n (Matrix.diagonal a) (homogeneousMonomial n d hd) =
      (d.prod (fun i m => a i ^ m)) • homogeneousMonomial n d hd :=
  homogeneousMatrixAction_diagonal_monomial a n d hd

end

section

open IsDedekindDomain Matrix

/-- Exact original-object consumer of `homogeneousMonomial_span`. -/
theorem actual_induced_quotient_homogeneousMonomial_span_source {ι : Type*} (n : ℕ) :
    Submodule.span ℂ (Set.range (fun d : {d : ι →₀ ℕ | d.degree = n} =>
      homogeneousMonomial (R := ℂ) n d.val d.property)) = ⊤ :=
  homogeneousMonomial_span (R := ℂ) n

end

section

open IsDedekindDomain Matrix

/-- Exact original-object consumer of `homogeneousUnitDiagonal_euler`. -/
theorem actual_induced_quotient_homogeneousUnitDiagonal_euler_source (a b : ℂˣ) (n : ℕ) :
    homogeneousMatrixEulerPolynomial n (gl2UnitDiagonalPair a b).val =
      symmetricEulerPolynomial a.val b.val n :=
  homogeneousUnitDiagonal_euler a b n

end

section

open IsDedekindDomain Matrix

/-- Exact original-object consumer of `primitiveLocalInduced_actual_symmetric_factor`. -/
theorem actual_induced_quotient_primitiveLocalInduced_actual_symmetric_factor_source {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) (r : ℕ) (s : ℂ) :
    Nonempty (Representation.Equiv (primitiveLocalInducedQuotientRepresentation F hpN)
      (adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) ∧
    primeSpectralEulerFactor (primitiveSymmetricSpectralRoots F r) ⟨p, Fact.out⟩ s =
      ((primitiveSymmetricMatrixEulerPolynomial F p r).eval ((p : ℂ) ^ (-s)))⁻¹ :=
  primitiveLocalInduced_actual_symmetric_factor F hpN r s

end

section

open IsDedekindDomain Matrix

/-- Exact original-object consumer of `primitiveSymmetricMatrix_hasProd_far`. -/
theorem actual_induced_quotient_primitiveSymmetricMatrix_hasProd_far_source {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hk : 2 ≤ k) (r : ℕ) {s : ℂ} (hs : (r : ℝ) + 1 < s.re) :
    HasProd (fun p : Nat.Primes => primitiveSymmetricMatrixLocalFactor F r p s)
      (primitiveSymmetricLFunction F r s) :=
  primitiveSymmetricMatrix_hasProd_far F hk r hs

end


section

open IsDedekindDomain Matrix MvPolynomial Module

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- Exact original-object consumer of `matrixPolynomialAction_mul`. -/
theorem actual_arithmetic_symmetric_matrixPolynomialAction_mul_source (g h : Matrix ι ι R) :
    matrixPolynomialAction (g * h) = (matrixPolynomialAction g).comp (matrixPolynomialAction h) :=
  matrixPolynomialAction_mul g h

end

section

open IsDedekindDomain Matrix MvPolynomial Module

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- Exact original-object consumer of `matrixCoefficientPolynomial_eval`. -/
theorem actual_arithmetic_symmetric_matrixCoefficientPolynomial_eval_source (p : MvPolynomial ι R) (d : ι →₀ ℕ) (a : Matrix ι ι R) :
    MvPolynomial.eval (fun ij : ι × ι => a ij.1 ij.2) (matrixCoefficientPolynomial p d) =
      MvPolynomial.coeff d (matrixPolynomialAction a p) :=
  matrixCoefficientPolynomial_eval p d a

end

section

open IsDedekindDomain Matrix MvPolynomial Module

variable {R : Type*} [CommRing R]
open MvPolynomial Module

/-- Exact original-object consumer of `homogeneousMonomial_span`. -/
theorem actual_arithmetic_symmetric_homogeneousMonomial_span_source {ι : Type*} (n : ℕ) :
    Submodule.span R (Set.range (fun d : {d : ι →₀ ℕ | d.degree = n} =>
      homogeneousMonomial (R := R) n d.val d.property)) = ⊤ :=
  homogeneousMonomial_span n

end

section

open IsDedekindDomain Matrix MvPolynomial Module

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι]

/-- Exact original-object consumer of `homogeneousCoefficientMap_GL`. -/
theorem actual_arithmetic_symmetric_homogeneousCoefficientMap_GL_source [DecidableEq ι] (n : ℕ) (φ : R →+* S)
    (g : Matrix.GeneralLinearGroup ι R) (p : homogeneousSubmodule ι R n) :
    homogeneousCoefficientMap n φ (homogeneousGLRepresentation (R := R) (ι := ι) n g p) =
      homogeneousGLRepresentation (R := S) (ι := ι) n
        (Matrix.GeneralLinearGroup.map (n := ι) φ g)
        (homogeneousCoefficientMap n φ p) :=
  homogeneousCoefficientMap_GL n φ g p

end

section

open IsDedekindDomain Matrix MvPolynomial Module

variable {R : Type*} [CommRing R]

/-- Exact original-object consumer of `homogeneousSymmetricGL_val`. -/
theorem actual_arithmetic_symmetric_homogeneousSymmetricGL_val_source (n : ℕ) (g : GeneralLinearGroup (Fin 2) R) :
    (homogeneousSymmetricGL n g).val =
      LinearMap.toMatrix (binaryHomogeneousMonomialBasis n) (binaryHomogeneousMonomialBasis n)
        (homogeneousGLRepresentation n g) :=
  homogeneousSymmetricGL_val n g

end

section

open IsDedekindDomain Matrix MvPolynomial Module

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Exact original-object consumer of `homogeneousSymmetricGL_map`. -/
theorem actual_arithmetic_symmetric_homogeneousSymmetricGL_map_source (n : ℕ) (φ : R →+* S)
    (g : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.map φ (homogeneousSymmetricGL n g) =
      homogeneousSymmetricGL n (GeneralLinearGroup.map φ g) :=
  homogeneousSymmetricGL_map n φ g

end

section

open IsDedekindDomain Matrix MvPolynomial Module

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `homogeneousSymmetricGL_continuous`. -/
theorem actual_arithmetic_symmetric_homogeneousSymmetricGL_continuous_source (n : ℕ) :
    Continuous (homogeneousSymmetricGL (R := R) n) :=
  homogeneousSymmetricGL_continuous n

end

section

open IsDedekindDomain Matrix MvPolynomial Module

variable {G R S : Type*} [Group G] [CommRing R]
    [CommRing S]

/-- Exact original-object consumer of `symmetricMatrixRepresentation_map`. -/
theorem actual_arithmetic_symmetric_symmetricMatrixRepresentation_map_source (n : ℕ) (ρ : G →* GeneralLinearGroup (Fin 2) R)
    (φ : R →+* S) :
    (GeneralLinearGroup.map φ).comp (symmetricMatrixRepresentation n ρ) =
      symmetricMatrixRepresentation n ((GeneralLinearGroup.map φ).comp ρ) :=
  symmetricMatrixRepresentation_map n ρ φ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

variable {G ι R S : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S]

/-- Exact original-object consumer of `groupAlgebraMatrix_map`. -/
theorem actual_matrix_determinant_groupAlgebraMatrix_map_source (ρ : G →* GeneralLinearGroup ι R)
    (φ : R →+* S) (x : MonoidAlgebra R G) :
    φ.mapMatrix (groupAlgebraMatrix ρ x) =
      groupAlgebraMatrix ((GeneralLinearGroup.map φ).comp ρ)
        (MonoidAlgebra.mapRingHom G φ x) :=
  groupAlgebraMatrix_map ρ φ x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

variable {G ι R S : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S]

/-- Exact original-object consumer of `matrixRepresentationDeterminant_map`. -/
theorem actual_matrix_determinant_matrixRepresentationDeterminant_map_source (ρ : G →* GeneralLinearGroup ι R)
    (φ : R →+* S) (x : MonoidAlgebra R G) :
    φ (matrixRepresentationDeterminant ρ x) =
      matrixRepresentationDeterminant ((GeneralLinearGroup.map φ).comp ρ)
        (MonoidAlgebra.mapRingHom G φ x) :=
  matrixRepresentationDeterminant_map ρ φ x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

variable {G ι R S T : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] [CommRing T]

/-- Exact original-object consumer of `determinantCoefficientLaw_natural`. -/
theorem actual_matrix_determinant_determinantCoefficientLaw_natural_source (ρ : G →* GeneralLinearGroup ι R)
    (φ : R →+* S) (ψ : S →+* T) (x : MonoidAlgebra S G) :
    ψ (determinantCoefficientLaw ρ φ x) =
      determinantCoefficientLaw ρ (ψ.comp φ) (MonoidAlgebra.mapRingHom G ψ x) :=
  determinantCoefficientLaw_natural ρ φ ψ x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

variable {G R S : Type*} [Group G] [CommRing R] [CommRing S] [Algebra R S]

/-- Exact original-object consumer of `groupAlgebraScalarExtensionEquiv_tmul`. -/
theorem actual_matrix_determinant_groupAlgebraScalarExtensionEquiv_tmul_source (a : S) (x : MonoidAlgebra R G) :
    groupAlgebraScalarExtensionEquiv (a ⊗ₜ[R] x) =
      a • MonoidAlgebra.mapRingHom G (algebraMap R S) x :=
  groupAlgebraScalarExtensionEquiv_tmul a x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

variable {G R S : Type*} [Group G] [CommRing R] [CommRing S]

/-- Exact original-object consumer of `symmetricMatrixRepresentation_determinant_baseChange`. -/
theorem actual_matrix_determinant_symmetricMatrixRepresentation_determinant_baseChange_source (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (φ : R →+* S)
    (x : MonoidAlgebra S G) :
    determinantCoefficientLaw (symmetricMatrixRepresentation n ρ) φ x =
      matrixRepresentationDeterminant
        (symmetricMatrixRepresentation n ((GeneralLinearGroup.map φ).comp ρ)) x :=
  symmetricMatrixRepresentation_determinant_baseChange n ρ φ x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

variable {G ι R S : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] [Algebra R S]

/-- Exact original-object consumer of `matrixTensorDeterminant_natural`. -/
theorem actual_matrix_determinant_matrixTensorDeterminant_natural_source {T : Type*} [CommRing T] [Algebra R T]
    (ρ : G →* GeneralLinearGroup ι R) (ψ : S →ₐ[R] T)
    (x : S ⊗[R] MonoidAlgebra R G) :
    ψ (matrixTensorDeterminant ρ x) =
      matrixTensorDeterminant ρ
        (Algebra.TensorProduct.map ψ (AlgHom.id R (MonoidAlgebra R G)) x) :=
  matrixTensorDeterminant_natural ρ ψ x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

variable {G ι R : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `determinantCharacteristicPolynomial_annihilates`. -/
theorem actual_matrix_determinant_determinantCharacteristicPolynomial_annihilates_source
    (ρ : G →* GeneralLinearGroup ι R) (g : G) :
    Polynomial.aeval (ρ g).val (determinantCharacteristicPolynomial ρ g) = 0 :=
  determinantCharacteristicPolynomial_annihilates ρ g

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixCharacteristicCoefficient_continuous`. -/
theorem actual_matrix_determinant_matrixCharacteristicCoefficient_continuous_source [TopologicalSpace R] [IsTopologicalRing R]
    (k : ℕ) : Continuous (fun A : Matrix ι ι R => A.charpoly.coeff k) :=
  matrixCharacteristicCoefficient_continuous k

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

variable {G ι R : Type*} [Group G] [TopologicalSpace G]
    [Fintype ι] [DecidableEq ι] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `symmetricMatrixRepresentation_determinant_continuous`. -/
theorem actual_matrix_determinant_symmetricMatrixRepresentation_determinant_continuous_source (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (hρ : Continuous ρ) (k : ℕ) :
    Continuous (fun g =>
      (determinantCharacteristicPolynomial (symmetricMatrixRepresentation n ρ) g).coeff k) :=
  symmetricMatrixRepresentation_determinant_continuous n ρ hρ k

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R S : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S]

/-- Exact original-object consumer of `determinantCoefficientLaw_conjugate`. -/
theorem actual_natural_determinant_determinantCoefficientLaw_conjugate_source (ρ σ : G →* GeneralLinearGroup ι R)
    (A : GeneralLinearGroup ι R) (h : ∀ g, σ g = A * ρ g * A⁻¹)
    (φ : R →+* S) (x : MonoidAlgebra S G) :
    determinantCoefficientLaw σ φ x = determinantCoefficientLaw ρ φ x :=
  determinantCoefficientLaw_conjugate ρ σ A h φ x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

universe u v w z u'

variable {R : Type u} {G : Type v} {ι : Type z}
    [CommRing R] [Group G] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrixGroupDeterminantLaw_baseChange`. -/
theorem actual_natural_determinant_matrixGroupDeterminantLaw_baseChange_source {S : Type u'} [CommRing S]
    (ρ : G →* GeneralLinearGroup ι R) (φ : R →+* S) :
    (matrixGroupDeterminantLaw ρ : GroupDeterminantLaw.{u, v, w} R G (Fintype.card ι)).baseChange φ =
      matrixGroupDeterminantLaw ((GeneralLinearGroup.map φ).comp ρ) :=
  matrixGroupDeterminantLaw_baseChange ρ φ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {σ ι R S : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S]

/-- Exact original-object consumer of `matrixCombinationDeterminant_groupAlgebra`. -/
theorem actual_natural_determinant_matrixCombinationDeterminant_groupAlgebra_source {G : Type*} [Group G]
    (ρ : G →* GeneralLinearGroup ι R) (g : σ → G) :
    Matrix.det (groupAlgebraMatrix ((GeneralLinearGroup.map
      (MvPolynomial.C : R →+* MvPolynomial σ R)).comp ρ)
        (∑ t, MonoidAlgebra.single (g t) (MvPolynomial.X t))) =
      matrixCombinationDeterminant (fun t => (ρ (g t)).val) :=
  matrixCombinationDeterminant_groupAlgebra ρ g

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {σ ι R : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixGroupDeterminantLaw_multicoefficient_continuous`. -/
theorem actual_natural_determinant_matrixGroupDeterminantLaw_multicoefficient_continuous_source
    {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalSpace R] [IsTopologicalRing R]
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) (d : σ →₀ ℕ) :
    Continuous (fun g : σ → G => MvPolynomial.coeff d
      ((matrixGroupDeterminantLaw ρ).eval (MvPolynomial σ R) MvPolynomial.C
        (∑ t, MonoidAlgebra.single (g t) (MvPolynomial.X t)))) :=
  matrixGroupDeterminantLaw_multicoefficient_continuous ρ hρ d

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `dualMatrixInfinitesimal_mul`. -/
theorem actual_first_order_dualMatrixInfinitesimal_mul_source (A B : GeneralLinearGroup ι (DualNumber R)) :
    dualMatrixInfinitesimal (A * B) = dualMatrixInfinitesimal A +
      (dualMatrixReduction A).val * dualMatrixInfinitesimal B *
        ((dualMatrixReduction A)⁻¹).val :=
  dualMatrixInfinitesimal_mul A B

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixFirstOrderCocycle_apply`. -/
theorem actual_first_order_matrixFirstOrderCocycle_apply_source (ρ : G →* GeneralLinearGroup ι R)
    (τ : MatrixFirstOrderLift ρ) (g : G) :
    matrixFirstOrderCocycle ρ τ g = dualMatrixInfinitesimal (τ.val g) :=
  matrixFirstOrderCocycle_apply ρ τ g

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixFirstOrderCocycle_fromCocycle`. -/
theorem actual_first_order_matrixFirstOrderCocycle_fromCocycle_source (ρ : G →* GeneralLinearGroup ι R)
    (c : groupCohomology.cocycles₁ (matrixAdjointRep ρ)) :
    matrixFirstOrderCocycle ρ (firstOrderLiftFromCocycle ρ c) = c :=
  matrixFirstOrderCocycle_fromCocycle ρ c

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `firstOrderLiftFromCocycle_cocycle`. -/
theorem actual_first_order_firstOrderLiftFromCocycle_cocycle_source (ρ : G →* GeneralLinearGroup ι R)
    (τ : MatrixFirstOrderLift ρ) :
    firstOrderLiftFromCocycle ρ (matrixFirstOrderCocycle ρ τ) = τ :=
  firstOrderLiftFromCocycle_cocycle ρ τ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `dualMatrixInfinitesimal_strictConjugate`. -/
theorem actual_strict_deformation_dualMatrixInfinitesimal_strictConjugate_source (A : GeneralLinearGroup ι (DualNumber R))
    (X : Matrix ι ι R) :
    dualMatrixInfinitesimal (dualMatrixStrictUnit X * A * (dualMatrixStrictUnit X)⁻¹) =
      dualMatrixInfinitesimal A + X -
        (dualMatrixReduction A).val * X * ((dualMatrixReduction A)⁻¹).val :=
  dualMatrixInfinitesimal_strictConjugate A X

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixFirstOrderConjugate_coboundary`. -/
theorem actual_strict_deformation_matrixFirstOrderConjugate_coboundary_source (ρ : G →* GeneralLinearGroup ι R)
    (τ : MatrixFirstOrderLift ρ) (X : Matrix ι ι R) :
    (fun g => matrixFirstOrderCocycle ρ τ g -
      matrixFirstOrderCocycle ρ (matrixFirstOrderConjugate ρ τ X) g) =
        groupCohomology.d₀₁ (matrixAdjointRep ρ) X :=
  matrixFirstOrderConjugate_coboundary ρ τ X

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixFirstOrderStrictlyConjugate_iff`. -/
theorem actual_strict_deformation_matrixFirstOrderStrictlyConjugate_iff_source (ρ : G →* GeneralLinearGroup ι R)
    (τ σ : MatrixFirstOrderLift ρ) :
    MatrixFirstOrderStrictlyConjugate ρ τ σ ↔
      groupCohomology.H1π (matrixAdjointRep ρ) (matrixFirstOrderCocycle ρ τ) =
        groupCohomology.H1π (matrixAdjointRep ρ) (matrixFirstOrderCocycle ρ σ) :=
  matrixFirstOrderStrictlyConjugate_iff ρ τ σ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `matrixFirstOrderLift_continuous_iff`. -/
theorem actual_strict_deformation_matrixFirstOrderLift_continuous_iff_source (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (τ : MatrixFirstOrderLift ρ) :
    Continuous τ.val ↔ Continuous (fun g => matrixFirstOrderCocycle ρ τ g) :=
  matrixFirstOrderLift_continuous_iff ρ hρ τ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `dualMatrixUnit_det`. -/
theorem actual_deformation_conditions_dualMatrixUnit_det_source (A : GeneralLinearGroup ι (DualNumber R)) :
    Matrix.det A.val = (Matrix.det (dualMatrixReduction A).val,
      Matrix.trace (dualMatrixInfinitesimal A) * Matrix.det (dualMatrixReduction A).val) :=
  dualMatrixUnit_det A

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `matrixFirstOrderLift_fixedDeterminant_iff`. -/
theorem actual_deformation_conditions_matrixFirstOrderLift_fixedDeterminant_iff_source (ρ : G →* GeneralLinearGroup ι R)
    (τ : MatrixFirstOrderLift ρ) :
    (∀ g, Matrix.det (τ.val g).val =
      TrivSqZeroExt.inl (Matrix.det (ρ g).val)) ↔
        ∀ g, Matrix.trace (matrixFirstOrderCocycle ρ τ g) = 0 :=
  matrixFirstOrderLift_fixedDeterminant_iff ρ τ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalGroup G] in
/-- Exact original-object consumer of `continuousMatrixFirstOrderClass_eq_iff`. -/
theorem actual_deformation_conditions_continuousMatrixFirstOrderClass_eq_iff_source (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (τ σ : MatrixFirstOrderLift ρ)
    (hτ : Continuous τ.val) (hσ : Continuous σ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ = continuousMatrixFirstOrderClass ρ hρ σ hσ ↔
      MatrixFirstOrderStrictlyConjugate ρ τ σ :=
  continuousMatrixFirstOrderClass_eq_iff ρ hρ τ σ hτ hσ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G H ι R : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Exact original-object consumer of `continuousMatrixAdjointH1Restriction_class`. -/
theorem actual_deformation_conditions_continuousMatrixAdjointH1Restriction_class_source (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (φ : H →* G) (hφ : Continuous φ)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixAdjointH1Restriction ρ hρ φ hφ
      (continuousMatrixFirstOrderClass ρ hρ τ hτ) =
        continuousMatrixFirstOrderClass (ρ.comp φ) (hρ.comp hφ)
          (matrixFirstOrderLiftRestriction ρ τ φ) (hτ.comp hφ) :=
  continuousMatrixAdjointH1Restriction_class ρ hρ φ hφ τ hτ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable (G ι R : Type*) [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `representationCoordinateMatrix_mul`. -/
theorem actual_coordinate_representation_representationCoordinateMatrix_mul_source (g h : G) :
    representationCoordinateMatrix G ι R (g * h) =
      representationCoordinateMatrix G ι R g * representationCoordinateMatrix G ι R h :=
  representationCoordinateMatrix_mul G ι R g h

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable (G ι R : Type*) [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `universalMatrixRepresentation_entry`. -/
theorem actual_coordinate_representation_universalMatrixRepresentation_entry_source (g : G) (i j : ι) :
    (universalMatrixRepresentation G ι R g).val i j =
      Ideal.Quotient.mk (representationCoordinateIdeal G ι R)
        (MvPolynomial.X (g, i, j)) :=
  universalMatrixRepresentation_entry G ι R g i j

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R S : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing S] [Algebra R S]

/-- Exact original-object consumer of `universalMatrixRepresentation_evaluation`. -/
theorem actual_coordinate_representation_universalMatrixRepresentation_evaluation_source (ρ : G →* GeneralLinearGroup ι S) :
    (GeneralLinearGroup.map (representationCoordinateEvaluation (R := R) ρ).toRingHom).comp
      (universalMatrixRepresentation G ι R) = ρ :=
  universalMatrixRepresentation_evaluation ρ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R S T : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- Exact original-object consumer of `representationCoordinateEvaluation_fromCoordinates`. -/
theorem actual_coordinate_representation_representationCoordinateEvaluation_fromCoordinates_source
    (f : RepresentationCoordinateAlgebra G ι R →ₐ[R] S) :
    representationCoordinateEvaluation (representationFromCoordinates f) = f :=
  representationCoordinateEvaluation_fromCoordinates f

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [DiscreteTopology R]

/-- Exact original-object consumer of `continuousMatrixRepresentation_quotient_finite`. -/
theorem actual_finite_symmetric_parameters_continuousMatrixRepresentation_quotient_finite_source [CompactSpace G]
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) : Finite (G ⧸ ρ.ker) :=
  continuousMatrixRepresentation_quotient_finite ρ hρ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `continuousMatrixRepresentation_noetherianCoordinates`. -/
theorem actual_finite_symmetric_parameters_continuousMatrixRepresentation_noetherianCoordinates_source
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace R] [DiscreteTopology R] [IsNoetherianRing R]
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) :
    IsNoetherianRing (RepresentationCoordinateAlgebra (G ⧸ ρ.ker) ι R) ∧
      ∃ f : RepresentationCoordinateAlgebra (G ⧸ ρ.ker) ι R →ₐ[R] R,
        ((GeneralLinearGroup.map f.toRingHom).comp
          (universalMatrixRepresentation (G ⧸ ρ.ker) ι R)).comp
            (QuotientGroup.mk' ρ.ker) = ρ :=
  continuousMatrixRepresentation_noetherianCoordinates ρ hρ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable (G R : Type*) [Group G] [CommRing R]

variable {G R} {S : Type*} [CommRing S] [Algebra R S]

/-- Exact original-object consumer of `symmetricRepresentationCoordinateMap_evaluation`. -/
theorem actual_finite_symmetric_parameters_symmetricRepresentationCoordinateMap_evaluation_source (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) S) :
    representationCoordinateEvaluation (R := R) (symmetricMatrixRepresentation n ρ) =
      (representationCoordinateEvaluation (R := R) ρ).comp
        (symmetricRepresentationCoordinateMap G R n) :=
  symmetricRepresentationCoordinateMap_evaluation n ρ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G R : Type} [Group G] [CommRing R]

/-- Exact original-object consumer of `symmetricFirstOrderLift_cohomology`. -/
theorem actual_finite_symmetric_parameters_symmetricFirstOrderLift_cohomology_source (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (τ σ : MatrixFirstOrderLift ρ)
    (h : groupCohomology.H1π (matrixAdjointRep ρ) (matrixFirstOrderCocycle ρ τ) =
      groupCohomology.H1π (matrixAdjointRep ρ) (matrixFirstOrderCocycle ρ σ)) :
    groupCohomology.H1π (matrixAdjointRep (symmetricMatrixRepresentation n ρ))
      (matrixFirstOrderCocycle _ (symmetricFirstOrderLift n ρ τ)) =
        groupCohomology.H1π (matrixAdjointRep (symmetricMatrixRepresentation n ρ))
          (matrixFirstOrderCocycle _ (symmetricFirstOrderLift n ρ σ)) :=
  symmetricFirstOrderLift_cohomology n ρ τ σ h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R A B : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Exact original-object consumer of `representationCoordinateFiber_iff`. -/
theorem actual_coordinate_derivation_representationCoordinateFiber_iff_source
    (ρ : G →* GeneralLinearGroup ι B) (π : A →ₐ[R] B)
    (f : RepresentationCoordinateAlgebra G ι R →ₐ[R] A) :
    (GeneralLinearGroup.map π.toRingHom).comp (representationFromCoordinates f) = ρ ↔
      π.comp f = representationCoordinateEvaluation (R := R) ρ :=
  representationCoordinateFiber_iff ρ π f

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `firstOrderCoordinateCocycleEquiv_surjective`. -/
theorem actual_coordinate_derivation_firstOrderCoordinateCocycleEquiv_surjective_source (ρ : G →* GeneralLinearGroup ι R) :
    Function.Surjective (firstOrderCoordinateCocycleEquiv ρ) :=
  firstOrderCoordinateCocycleEquiv_surjective ρ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Exact original-object consumer of `dualNumberQuotient_comp_eq_iff`. -/
theorem actual_coordinate_derivation_dualNumberQuotient_comp_eq_iff_source (f g : A →ₐ[R] DualNumber R) :
    (Ideal.Quotient.mkₐ R (TrivSqZeroExt.kerIdeal R R)).comp f =
      (Ideal.Quotient.mkₐ R (TrivSqZeroExt.kerIdeal R R)).comp g ↔
        (TrivSqZeroExt.fstHom R R R).comp f = (TrivSqZeroExt.fstHom R R R).comp g :=
  dualNumberQuotient_comp_eq_iff f g

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `representationCoordinateDerivationEquiv_apply`. -/
theorem actual_coordinate_derivation_representationCoordinateDerivationEquiv_apply_source (ρ : G →* GeneralLinearGroup ι R)
    (d : RepresentationCoordinateDerivations ρ) (x : RepresentationCoordinateAlgebra G ι R) :
    (representationCoordinateDerivationEquiv ρ d).val x =
      (d x : DualNumber R) + representationCoordinateConstantLift ρ x :=
  representationCoordinateDerivationEquiv_apply ρ d x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable (G ι R : Type*) [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `representationCoordinateMatrix_generators_adjoin`. -/
theorem actual_coordinate_cotangent_representationCoordinateMatrix_generators_adjoin_source (S : Set G)
    (hS : Submonoid.closure S = ⊤) :
    Algebra.adjoin R (Set.range (fun t : S × ι × ι =>
      representationCoordinateMatrix G ι R t.1.val t.2.1 t.2.2)) = ⊤ :=
  representationCoordinateMatrix_generators_adjoin G ι R S hS

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `representationCoordinateAlgebra_isNoetherian_of_fg`. -/
theorem actual_coordinate_cotangent_representationCoordinateAlgebra_isNoetherian_of_fg_source [Group.FG G] [IsNoetherianRing R] :
    IsNoetherianRing (RepresentationCoordinateAlgebra G ι R) :=
  representationCoordinateAlgebra_isNoetherian_of_fg 

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `representationCoordinateCotangentCocycleEquiv_surjective`. -/
theorem actual_coordinate_cotangent_representationCoordinateCotangentCocycleEquiv_surjective_source
    (ρ : G →* GeneralLinearGroup ι R) :
    Function.Surjective (representationCoordinateCotangentCocycleEquiv ρ) :=
  representationCoordinateCotangentCocycleEquiv_surjective ρ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `representationCoordinatePointQuotientEquiv_mk`. -/
theorem actual_coordinate_cotangent_representationCoordinatePointQuotientEquiv_mk_source (ρ : G →* GeneralLinearGroup ι R)
    (x : RepresentationCoordinateAlgebra G ι R) :
    representationCoordinatePointQuotientEquiv ρ
      (Ideal.Quotient.mk (representationCoordinatePointIdeal ρ) x) =
        representationCoordinateEvaluation (R := R) ρ x :=
  representationCoordinatePointQuotientEquiv_mk ρ x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `representationCoordinateDerivationCocycleEquiv_value`. -/
theorem actual_coordinate_tangent_linear_representationCoordinateDerivationCocycleEquiv_value_source
    (ρ : G →* GeneralLinearGroup ι R) (d : RepresentationCoordinateDerivations ρ) (g : G) :
    representationCoordinateDerivationCocycleEquiv ρ d g =
      coordinateDerivationMatrix ρ d g * ((ρ g)⁻¹).val :=
  representationCoordinateDerivationCocycleEquiv_value ρ d g

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `coordinateDerivationCocycleLinearEquiv_apply`. -/
theorem actual_coordinate_tangent_linear_coordinateDerivationCocycleLinearEquiv_apply_source
    (ρ : G →* GeneralLinearGroup ι R) (d : RepresentationCoordinateDerivations ρ) :
    coordinateDerivationCocycleLinearEquiv ρ d =
      representationCoordinateDerivationCocycleEquiv ρ d :=
  coordinateDerivationCocycleLinearEquiv_apply ρ d

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Exact original-object consumer of `coordinateTangentCohomologyMap_eq_iff`. -/
theorem actual_coordinate_tangent_linear_coordinateTangentCohomologyMap_eq_iff_source (ρ : G →* GeneralLinearGroup ι R)
    (d e : RepresentationCoordinateDerivations ρ) :
    coordinateTangentCohomologyMap ρ d = coordinateTangentCohomologyMap ρ e ↔
      MatrixFirstOrderStrictlyConjugate ρ
        (firstOrderRepresentationCoordinateEquiv ρ (representationCoordinateDerivationEquiv ρ d))
        (firstOrderRepresentationCoordinateEquiv ρ (representationCoordinateDerivationEquiv ρ e)) :=
  coordinateTangentCohomologyMap_eq_iff ρ d e

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G R : Type} [Group G] [CommRing R]

/-- Exact original-object consumer of `symmetricCoordinateDerivationMap_firstOrder`. -/
theorem actual_coordinate_tangent_linear_symmetricCoordinateDerivationMap_firstOrder_source (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (d : RepresentationCoordinateDerivations ρ) :
    firstOrderRepresentationCoordinateEquiv (symmetricMatrixRepresentation n ρ)
      (representationCoordinateDerivationEquiv (symmetricMatrixRepresentation n ρ)
        (symmetricCoordinateDerivationMap n ρ d)) =
      symmetricFirstOrderLift n ρ
        (firstOrderRepresentationCoordinateEquiv ρ (representationCoordinateDerivationEquiv ρ d)) :=
  symmetricCoordinateDerivationMap_firstOrder n ρ d

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G R : Type} [Group G] [CommRing R]

/-- Exact original-object consumer of `symmetricTangentCohomologyLift_ker`. -/
theorem actual_symmetric_cohomology_residual_symmetricTangentCohomologyLift_ker_source (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) :
    LinearMap.ker (coordinateTangentCohomologyMap ρ) ≤
      LinearMap.ker (symmetricTangentCohomologyLift n ρ) :=
  symmetricTangentCohomologyLift_ker n ρ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G R : Type} [Group G] [CommRing R]

/-- Exact original-object consumer of `symmetricAdjointCohomologyMap_firstOrder`. -/
theorem actual_symmetric_cohomology_residual_symmetricAdjointCohomologyMap_firstOrder_source (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (τ : MatrixFirstOrderLift ρ) :
    symmetricAdjointCohomologyMap n ρ
      (groupCohomology.H1π (matrixAdjointRep ρ) (matrixFirstOrderCocycle ρ τ)) =
      groupCohomology.H1π (matrixAdjointRep (symmetricMatrixRepresentation n ρ))
        (matrixFirstOrderCocycle _ (symmetricFirstOrderLift n ρ τ)) :=
  symmetricAdjointCohomologyMap_firstOrder n ρ τ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- Exact original-object consumer of `residualRepresentationCoordinateQuotientEquiv_mk`. -/
theorem actual_symmetric_cohomology_residual_residualRepresentationCoordinateQuotientEquiv_mk_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (x : RepresentationCoordinateAlgebra G ι O) :
    residualRepresentationCoordinateQuotientEquiv ρ
      (Ideal.Quotient.mk (residualRepresentationCoordinateIdeal ρ) x) =
        representationCoordinateEvaluation (R := O) ρ x :=
  residualRepresentationCoordinateQuotientEquiv_mk ρ x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- Exact original-object consumer of `integralRepresentationCoordinates_isUnit`. -/
theorem actual_symmetric_cohomology_residual_integralRepresentationCoordinates_isUnit_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : MatrixRepresentationFiber ρ (Algebra.ofId O (IsLocalRing.ResidueField O)))
    (x : RepresentationCoordinateAlgebra G ι O) (hx : x ∉ residualRepresentationCoordinateIdeal ρ) :
    IsUnit (representationCoordinateEvaluation (R := O) τ.val x) :=
  integralRepresentationCoordinates_isUnit ρ τ x hx

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- Exact original-object consumer of `residualRepresentationLocalRing_isNoetherian`. -/
theorem actual_localized_representation_residualRepresentationLocalRing_isNoetherian_source [Group.FG G] [IsNoetherianRing O]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    IsNoetherianRing (ResidualRepresentationLocalRing ρ) :=
  residualRepresentationLocalRing_isNoetherian ρ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- Exact original-object consumer of `localizedIntegralCoordinateMap_representation`. -/
theorem actual_localized_representation_localizedIntegralCoordinateMap_representation_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : MatrixRepresentationFiber ρ (Algebra.ofId O (IsLocalRing.ResidueField O))) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationLocalRing ρ) (S := O)
      (localizedIntegralCoordinateMap ρ
      ((representationCoordinateFiberEquiv ρ (Algebra.ofId O (IsLocalRing.ResidueField O))).symm τ)).toRingHom).comp
        (localizedUniversalMatrixRepresentation ρ) = τ.val :=
  localizedIntegralCoordinateMap_representation ρ τ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- Exact original-object consumer of `localizedUniversalMatrixRepresentation_reduction`. -/
theorem actual_localized_representation_localizedUniversalMatrixRepresentation_reduction_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationLocalRing ρ)
      (S := IsLocalRing.ResidueField O) (localizedResidualRepresentationEvaluation ρ).toRingHom).comp
      (localizedUniversalMatrixRepresentation ρ) = ρ :=
  localizedUniversalMatrixRepresentation_reduction ρ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- Exact original-object consumer of `localizedIntegralRepresentationFiberEquiv_apply`. -/
theorem actual_localized_representation_localizedIntegralRepresentationFiberEquiv_apply_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (f : LocalizedIntegralCoordinateFiber ρ) :
    (localizedIntegralRepresentationFiberEquiv ρ f).val =
      (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationLocalRing ρ) (S := O)
        f.val.toRingHom).comp (localizedUniversalMatrixRepresentation ρ) :=
  localizedIntegralRepresentationFiberEquiv_apply ρ f

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {O A : Type*} [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A]

/-- Exact original-object consumer of `localCoefficientReduction_ne_zero_iff`. -/
theorem actual_local_coefficient_representation_localCoefficientReduction_ne_zero_iff_source
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) (x : A) :
    localCoefficientReduction e x ≠ 0 ↔ IsUnit x :=
  localCoefficientReduction_ne_zero_iff e x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]

/-- Exact original-object consumer of `localCoefficientRepresentationCoordinates_isUnit`. -/
theorem actual_local_coefficient_representation_localCoefficientRepresentationCoordinates_isUnit_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : MatrixRepresentationFiber ρ (localCoefficientReduction e))
    (x : RepresentationCoordinateAlgebra G ι O) (hx : x ∉ residualRepresentationCoordinateIdeal ρ) :
    IsUnit (representationCoordinateEvaluation (R := O) τ.val x) :=
  localCoefficientRepresentationCoordinates_isUnit ρ e τ x hx

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]

/-- Exact original-object consumer of `localizedCoefficientCoordinateMap_representation`. -/
theorem actual_local_coefficient_representation_localizedCoefficientCoordinateMap_representation_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : MatrixRepresentationFiber ρ (localCoefficientReduction e)) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationLocalRing ρ) (S := A)
      (localizedCoefficientCoordinateMap ρ e
      ((representationCoordinateFiberEquiv ρ (localCoefficientReduction e)).symm τ)).toRingHom).comp
        (localizedUniversalMatrixRepresentation ρ) = τ.val :=
  localizedCoefficientCoordinateMap_representation ρ e τ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]

/-- Exact original-object consumer of `localizedCoefficientRepresentationFiberEquiv_apply`. -/
theorem actual_local_coefficient_representation_localizedCoefficientRepresentationFiberEquiv_apply_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : LocalizedCoefficientCoordinateFiber ρ e) :
    (localizedCoefficientRepresentationFiberEquiv ρ e f).val =
      (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationLocalRing ρ) (S := A)
        f.val.toRingHom).comp (localizedUniversalMatrixRepresentation ρ) :=
  localizedCoefficientRepresentationFiberEquiv_apply ρ e f

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {O R A : Type*} [CommRing O] [CommRing R] [CommRing A]
  [Algebra O R] [Algebra O A]

/-- Exact original-object consumer of `adicCoefficientQuotientMap_transition`. -/
theorem actual_completed_representation_adicCoefficientQuotientMap_transition_source (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right hmn)).comp
      (adicCoefficientQuotientMap I J f hf n) =
    (adicCoefficientQuotientMap I J f hf m).comp
      (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right hmn)) :=
  adicCoefficientQuotientMap_transition I J f hf hmn

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {O R A : Type*} [CommRing O] [CommRing R] [CommRing A]
  [Algebra O R] [Algebra O A]

/-- Exact original-object consumer of `adicCoefficientCompletionMap_of`. -/
theorem actual_completed_representation_adicCoefficientCompletionMap_of_source (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) (x : R) :
    adicCoefficientCompletionMap I J f hf (AdicCompletion.of I R x) =
      AdicCompletion.of J A (f x) :=
  adicCoefficientCompletionMap_of I J f hf x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- Exact original-object consumer of `completedUniversalMatrixRepresentation_reduction`. -/
theorem actual_completed_representation_completedUniversalMatrixRepresentation_reduction_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
      (S := IsLocalRing.ResidueField O) (completedResidualRepresentationEvaluation ρ).toRingHom).comp
      (completedUniversalMatrixRepresentation ρ) = ρ :=
  completedUniversalMatrixRepresentation_reduction ρ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]

/-- Exact original-object consumer of `completedLocalCoefficientCoordinateMap_representation`. -/
theorem actual_completed_representation_completedLocalCoefficientCoordinateMap_representation_source
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : MatrixRepresentationFiber ρ (localCoefficientReduction e)) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ) (S := A)
      (completedLocalCoefficientCoordinateMap ρ e
      ((representationCoordinateFiberEquiv ρ (localCoefficientReduction e)).symm τ)).toRingHom).comp
        (completedUniversalMatrixRepresentation ρ) = τ.val :=
  completedLocalCoefficientCoordinateMap_representation ρ e τ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R : Type*} [CommRing R]

/-- Exact original-object consumer of `adicCompletion_evaluation_kernel`. -/
theorem actual_completed_local_representation_adicCompletion_evaluation_kernel_source (I : Ideal R) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap R (AdicCompletion I R)) :=
  adicCompletion_evaluation_kernel I hI n

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- Exact original-object consumer of `residualRepresentationCompletion_completeLocal`. -/
theorem actual_completed_local_representation_residualRepresentationCompletion_completeLocal_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    IsAdicComplete (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ))
      (ResidualRepresentationCompletion ρ) :=
  residualRepresentationCompletion_completeLocal ρ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- Exact original-object consumer of `completedUniversalMatrixRepresentation_trueResidue`. -/
theorem actual_completed_local_representation_completedUniversalMatrixRepresentation_trueResidue_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
      (S := IsLocalRing.ResidueField O) ((completedResidualFieldEquiv ρ).toRingHom.comp
      (IsLocalRing.residue (ResidualRepresentationCompletion ρ)))).comp
        (completedUniversalMatrixRepresentation ρ) = ρ :=
  completedUniversalMatrixRepresentation_trueResidue ρ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {O R A : Type*} [CommRing O] [CommRing R] [CommRing A]
  [Algebra O R] [Algebra O A]

variable {G ι : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [IsLocalRing O] [Group.FG G] [IsNoetherianRing O] [IsLocalRing A]

/-- Exact original-object consumer of `completedLocalCoefficientCoordinateMap_unique`. -/
theorem actual_completed_local_representation_completedLocalCoefficientCoordinateMap_unique_source
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : MatrixRepresentationFiber ρ (localCoefficientReduction e))
    (h : ResidualRepresentationCompletion ρ →ₐ[O] A)
    (hh : (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ) (S := A)
      h.toRingHom).comp
      (completedUniversalMatrixRepresentation ρ) = τ.val) :
    completedLocalCoefficientCoordinateMap ρ e
      ((representationCoordinateFiberEquiv ρ (localCoefficientReduction e)).symm τ) = h :=
  completedLocalCoefficientCoordinateMap_unique ρ e τ h hh

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- Exact original-object consumer of `residualRepresentationCompletion_finite_quotient`. -/
theorem actual_completed_topology_residualRepresentationCompletion_finite_quotient_source [Finite (IsLocalRing.ResidueField O)]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (n : ℕ) :
    Finite (ResidualRepresentationCompletion ρ ⧸
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n) :=
  residualRepresentationCompletion_finite_quotient ρ n

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `completedLocalCoefficientCoordinateMap_reduction`. -/
theorem actual_completed_topology_completedLocalCoefficientCoordinateMap_reduction_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e)) :
    (localCoefficientReduction e).comp (completedLocalCoefficientCoordinateMap ρ e f) =
      completedResidualRepresentationEvaluation ρ :=
  completedLocalCoefficientCoordinateMap_reduction ρ e f

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- Exact original-object consumer of `completedLocalCoefficientCoordinateMap_uniformContinuous`. -/
theorem actual_completed_topology_completedLocalCoefficientCoordinateMap_uniformContinuous_source
    {A : Type*} [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e)) :
    UniformContinuous (completedLocalCoefficientCoordinateMap ρ e f) :=
  completedLocalCoefficientCoordinateMap_uniformContinuous hA ρ e f

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R : Type*} [CommRing R] [WithIdeal R]

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `residualRepresentationCompletion_compactSpace`. -/
theorem actual_completed_topology_residualRepresentationCompletion_compactSpace_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    CompactSpace (ResidualRepresentationCompletion ρ) :=
  residualRepresentationCompletion_compactSpace ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {σ τ R : Type*} [CommRing R]

/-- Exact original-object consumer of `splitPowerSeriesVariables_coeff`. -/
theorem actual_noetherian_completion_splitPowerSeriesVariables_coeff_source (f : MvPowerSeries (σ ⊕ τ) R)
    (d : σ →₀ ℕ) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.coeff d (splitPowerSeriesVariables f)) =
      MvPowerSeries.coeff (d.sumElim e) f :=
  splitPowerSeriesVariables_coeff f d e

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R : Type*} [CommRing R] [IsNoetherianRing R]

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- Exact original-object consumer of `residualRepresentationLocalPowerSeries_isNoetherian`. -/
theorem actual_noetherian_completion_residualRepresentationLocalPowerSeries_isNoetherian_source
    (ρ : G →* Matrix.GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (σ : Type*) [Finite σ] :
    IsNoetherianRing (MvPowerSeries σ (ResidualRepresentationLocalRing ρ)) :=
  residualRepresentationLocalPowerSeries_isNoetherian ρ σ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {O R A : Type*} [CommRing O] [CommRing R] [CommRing A]
  [Algebra O R] [Algebra O A]

/-- Exact original-object consumer of `adicCoefficientCompletionMap_ideal_image`. -/
theorem actual_noetherian_completion_adicCoefficientCompletionMap_ideal_image_source
    (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) (hIJ : I.map f.toRingHom = J) :
    (I.map (algebraMap R (AdicCompletion I R))).map
      (adicCoefficientCompletionMap I J f hf).toRingHom =
        J.map (algebraMap A (AdicCompletion J A)) :=
  adicCoefficientCompletionMap_ideal_image I J f hf hIJ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {O R A : Type*} [CommRing O] [CommRing R] [CommRing A]
  [Algebra O R] [Algebra O A]

/-- Exact original-object consumer of `adicCoefficientCompletionMap_surjective`. -/
theorem actual_noetherian_completion_adicCoefficientCompletionMap_surjective_source
    (I : Ideal R) (hI : I.FG) (J : Ideal A) (hJ : J.FG)
    (f : R →ₐ[O] A) (hf : I ≤ Ideal.comap f.toRingHom J)
    (hIJ : I.map f.toRingHom = J) (hsurj : Function.Surjective f) :
    Function.Surjective (adicCoefficientCompletionMap I J f hf) :=
  adicCoefficientCompletionMap_surjective I hI J hJ f hf hIJ hsurj

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R : Type*} [CommRing R] [IsNoetherianRing R]

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- Exact original-object consumer of `residualRepresentationCompletion_isNoetherian`. -/
theorem actual_noetherian_completion_residualRepresentationCompletion_isNoetherian_source
    (ρ : G →* Matrix.GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    IsNoetherianRing (ResidualRepresentationCompletion ρ) :=
  residualRepresentationCompletion_isNoetherian ρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `completedCoefficientRepresentationEquiv_evaluation`. -/
theorem actual_completed_profinite_completedCoefficientRepresentationEquiv_evaluation_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : MatrixRepresentationFiber ρ (localCoefficientReduction e)) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ) (S := A)
      ((completedCoefficientRepresentationEquiv ρ e).symm τ).val.toRingHom).comp
        (completedUniversalMatrixRepresentation ρ) = τ.val :=
  completedCoefficientRepresentationEquiv_evaluation ρ e τ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R ι : Type*} [CommRing R] [WithIdeal R] [T2Space R]
  [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `adicMatrixGroup_totallyDisconnected`. -/
theorem actual_completed_profinite_adicMatrixGroup_totallyDisconnected_source : TotallyDisconnectedSpace (GeneralLinearGroup ι R) :=
  adicMatrixGroup_totallyDisconnected (R := R) (ι := ι)

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

universe u

variable {G H : Type u} [Group G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]

/-- Exact original-object consumer of `profiniteRepresentationExtension_eta`. -/
theorem actual_completed_profinite_profiniteRepresentationExtension_eta_source (τ : G →* H) (g : G) :
    profiniteRepresentationExtension τ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) =
      τ g :=
  profiniteRepresentationExtension_eta τ g

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

universe u

variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedUniversalProfiniteRepresentation_eta`. -/
theorem actual_completed_profinite_completedUniversalProfiniteRepresentation_eta_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (g : G) :
    completedUniversalProfiniteRepresentation ρ
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) =
        completedUniversalMatrixRepresentation ρ g :=
  completedUniversalProfiniteRepresentation_eta ρ g

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrixIdeal_pow_mem`. -/
theorem actual_congruence_kernel_matrixIdeal_pow_mem_source (I : Ideal R) {X : Matrix ι ι R}
    (hX : X ∈ I.matrix ι) (n : ℕ) : X ^ n ∈ (I ^ n).matrix ι :=
  matrixIdeal_pow_mem I hX n

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrix_primePower_congruence`. -/
theorem actual_congruence_kernel_matrix_primePower_congruence_source (I : Ideal R) {p : ℕ}
    (hp : p.Prime) (hpI : (p : R) ∈ I)
    (X : Matrix ι ι R) (hX : X - 1 ∈ I.matrix ι) (n : ℕ) :
    X ^ (p ^ n) - 1 ∈ (I ^ (n + 1)).matrix ι :=
  matrix_primePower_congruence I hp hpI X hX n

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrixCongruenceKernel_isPGroup`. -/
theorem actual_congruence_kernel_matrixCongruenceKernel_isPGroup_source (I : Ideal R) {p N : ℕ}
    (hp : p.Prime) (hpI : (p : R) ∈ I) (hI : I ^ N = ⊥) :
    IsPGroup p (MatrixCongruenceKernel (ι := ι) I) :=
  matrixCongruenceKernel_isPGroup I hp hpI hI

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {A ι : Type*} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
  [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `artinianResidualMatrixKernel_isPGroup`. -/
theorem actual_congruence_kernel_artinianResidualMatrixKernel_isPGroup_source (p : ℕ) (hp : p.Prime)
    [CharP (IsLocalRing.ResidueField A) p] :
    IsPGroup p ((GeneralLinearGroup.map (n := ι) (R := A)
      (S := IsLocalRing.ResidueField A) (IsLocalRing.residue A)).ker) :=
  artinianResidualMatrixKernel_isPGroup p hp

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `idealPowerMatrixKernel_isPGroup`. -/
theorem actual_completed_power_kernel_idealPowerMatrixKernel_isPGroup_source (I : Ideal R) {p : ℕ}
    (hp : p.Prime) (hpI : (p : R) ∈ I) (n : ℕ) :
    IsPGroup p (MatrixCongruenceKernel (ι := ι)
      (I.map (Ideal.Quotient.mk (I ^ n)))) :=
  idealPowerMatrixKernel_isPGroup I hp hpI n

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- Exact original-object consumer of `residualRepresentationCompletion_powerKernel_isPGroup`. -/
theorem actual_completed_power_kernel_residualRepresentationCompletion_powerKernel_isPGroup_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p] (n : ℕ) :
    IsPGroup p (MatrixCongruenceKernel (ι := ι)
      ((IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)).map
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n)))) :=
  residualRepresentationCompletion_powerKernel_isPGroup ρ p hp n

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `matrixCongruenceKernel_powerImage_isPGroup`. -/
theorem actual_completed_congruence_image_matrixCongruenceKernel_powerImage_isPGroup_source (I : Ideal R) {p : ℕ}
    (hp : p.Prime) (hpI : (p : R) ∈ I) (n : ℕ) :
    IsPGroup p ((MatrixCongruenceKernel (ι := ι) I).map
      (GeneralLinearGroup.map (n := ι) (R := R) (S := R ⧸ I ^ n)
        (Ideal.Quotient.mk (I ^ n)))) :=
  matrixCongruenceKernel_powerImage_isPGroup I hp hpI n

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- Exact original-object consumer of `completedResidualCongruenceImage_isPGroup`. -/
theorem actual_completed_congruence_image_completedResidualCongruenceImage_isPGroup_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p] (n : ℕ) :
    IsPGroup p (CompletedResidualCongruenceImage ρ n) :=
  completedResidualCongruenceImage_isPGroup ρ p hp n

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R ι : Type*} [CommRing R] [WithIdeal R] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `adicMatrixPowerReduction_continuous`. -/
theorem actual_completed_congruence_basis_adicMatrixPowerReduction_continuous_source (n : ℕ) :
    Continuous (GeneralLinearGroup.map (n := ι) (R := R)
      (S := R ⧸ (WithIdeal.i : Ideal R) ^ n)
      (Ideal.Quotient.mk ((WithIdeal.i : Ideal R) ^ n))) :=
  adicMatrixPowerReduction_continuous n

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R ι : Type*} [CommRing R] [WithIdeal R] [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `adicMatrixReductionProduct_isClosedEmbedding`. -/
theorem actual_completed_congruence_basis_adicMatrixReductionProduct_isClosedEmbedding_source [T2Space R] [CompactSpace R] :
    Topology.IsClosedEmbedding (adicMatrixReductionProduct (R := R) (ι := ι)) :=
  adicMatrixReductionProduct_isClosedEmbedding (R := R) (ι := ι)

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G : Type*} [Group G] [TopologicalSpace G]
  {H : ℕ → Type*} [∀ n, Group (H n)] [∀ n, TopologicalSpace (H n)]
  [∀ n, DiscreteTopology (H n)]

/-- Exact original-object consumer of `discreteReduction_continuous_quotient_isPGroup`. -/
theorem actual_completed_congruence_basis_discreteReduction_continuous_quotient_isPGroup_source
    (π : ∀ n, G →* H n)
    (hπ : Topology.IsEmbedding (fun g n => π n g))
    (hmono : Antitone (fun n => (π n).ker)) (p : ℕ)
    (hP : ∀ n, IsPGroup p (π n).range)
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →* Q) (hf : Continuous f) (hsurj : Function.Surjective f) :
    IsPGroup p Q :=
  discreteReduction_continuous_quotient_isPGroup π hπ hmono p hP f hf hsurj

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedResidualKernel_continuous_quotient_isPGroup`. -/
theorem actual_completed_congruence_basis_completedResidualKernel_continuous_quotient_isPGroup_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : MatrixCongruenceKernel (ι := ι)
      (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)) →* Q)
    (hf : Continuous f) (hsurj : Function.Surjective f) : IsPGroup p Q :=
  completedResidualKernel_continuous_quotient_isPGroup ρ p hp f hf hsurj

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `profiniteProPKernel_isClosed`. -/
theorem actual_fixed_prop_common_kernel_profiniteProPKernel_isClosed_source (p : ℕ) (G : ProfiniteGrp) :
    IsClosed (profiniteProPKernel p G : Set G) :=
  profiniteProPKernel_isClosed p G

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- Exact original-object consumer of `profiniteProPDiscreteFactor_continuous`. -/
theorem actual_fixed_prop_common_kernel_profiniteProPDiscreteFactor_continuous_source (p : ℕ) (G : ProfiniteGrp)
    (f : G →* Q) (hf : Continuous f) (hQ : IsPGroup p Q) :
    Continuous (profiniteProPDiscreteFactor p G f hf hQ) :=
  profiniteProPDiscreteFactor_continuous p G f hf hQ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `profiniteProPKernel_map_le`. -/
theorem actual_fixed_prop_common_kernel_profiniteProPKernel_map_le_source (p : ℕ) (G H : ProfiniteGrp)
    (f : G →* H) (hf : Continuous f) :
    (profiniteProPKernel p G).map f ≤ profiniteProPKernel p H :=
  profiniteProPKernel_map_le p G H f hf

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedResidualProfiniteKernel_commonKernel_eq_bot`. -/
theorem actual_fixed_prop_common_kernel_completedResidualProfiniteKernel_commonKernel_eq_bot_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p] :
    profiniteProPKernel p (completedResidualProfiniteKernel ρ) = ⊥ :=
  completedResidualProfiniteKernel_commonKernel_eq_bot ρ p hp

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G α : Type*} [Group G] [TopologicalSpace G]
  [CompactSpace G] {H : α → Type*} [∀ i, Group (H i)]
  [∀ i, TopologicalSpace (H i)] [∀ i, DiscreteTopology (H i)]

/-- Exact original-object consumer of `compact_reduction_continuous_quotient_isPGroup`. -/
theorem actual_fixed_prop_quotient_compact_reduction_continuous_quotient_isPGroup_source
    (π : ∀ i, G →* H i) (hπ : ∀ i, Continuous (π i))
    (p : ℕ) (hP : ∀ i, IsPGroup p (H i))
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →* Q) (hf : Continuous f) (hsurj : Function.Surjective f)
    (hcommon : (⨅ i, (π i).ker) ≤ f.ker) : IsPGroup p Q :=
  compact_reduction_continuous_quotient_isPGroup π hπ p hP f hf hsurj hcommon

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `profiniteProPQuotient_continuous_quotient_isPGroup`. -/
theorem actual_fixed_prop_quotient_profiniteProPQuotient_continuous_quotient_isPGroup_source
    (p : ℕ) (G : ProfiniteGrp)
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G ⧸ profiniteProPKernel p G →* Q) (hf : Continuous f)
    (hsurj : Function.Surjective f) : IsPGroup p Q :=
  profiniteProPQuotient_continuous_quotient_isPGroup p G f hf hsurj

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `profiniteProPQuotientCoordinates_injective`. -/
theorem actual_fixed_prop_quotient_profiniteProPQuotientCoordinates_injective_source (p : ℕ) (G : ProfiniteGrp) :
    Function.Injective (profiniteProPQuotientCoordinates p G) :=
  profiniteProPQuotientCoordinates_injective p G

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `fixedResidualProPKernel_normal`. -/
theorem actual_fixed_prop_quotient_fixedResidualProPKernel_normal_source (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G)
    [K.Normal] (hK : IsClosed (K : Set G)) :
    (fixedResidualProPKernel p G K hK).Normal :=
  fixedResidualProPKernel_normal p G K hK

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `profiniteProPContinuousFactor_continuous`. -/
theorem actual_fixed_residual_lift_profiniteProPContinuousFactor_continuous_source
    (p : ℕ) (G H : ProfiniteGrp) (f : G →* H) (hf : Continuous f)
    (hH : profiniteProPKernel p H = ⊥) :
    Continuous (profiniteProPContinuousFactor p G H f hf hH) :=
  profiniteProPContinuousFactor_continuous p G H f hf hH

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `fixedResidualProPKernel_le_representation_kernel`. -/
theorem actual_fixed_residual_lift_fixedResidualProPKernel_le_representation_kernel_source
    (p : ℕ) (G H : ProfiniteGrp) (K : Subgroup G) (hK : IsClosed (K : Set G))
    (L : Subgroup H) (hL : IsClosed (L : Set H))
    (hP : profiniteProPKernel p (closedSubgroupProfinite H L hL) = ⊥)
    (f : G →* H) (hf : Continuous f) (hres : ∀ g ∈ K, f g ∈ L) :
    fixedResidualProPKernel p G K hK ≤ f.ker :=
  fixedResidualProPKernel_le_representation_kernel p G H K hK L hL hP f hf hres

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

universe u

variable {G₀ ι O : Type u} [Group G₀] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G₀] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedResidualLiftFactor_continuous`. -/
theorem actual_fixed_residual_lift_completedResidualLiftFactor_continuous_source
    (ρ : G₀ →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ)))
    (hσ : Continuous σ)
    (f : H →* GeneralLinearGroup ι (ResidualRepresentationCompletion ρ))
    (hf : Continuous f)
    (hres : (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
      (S := IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ))
      (IsLocalRing.residue (ResidualRepresentationCompletion ρ))).comp f = σ) :
    Continuous (completedResidualLiftFactor ρ p hp H σ hσ f hf hres) :=
  completedResidualLiftFactor_continuous ρ p hp H σ hσ f hf hres

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G : Type*} [Group G] [Finite G]

/-- Exact original-object consumer of `finitePGroup_proper_subgroup_character`. -/
theorem actual_fixed_prop_topological_generation_finitePGroup_proper_subgroup_character_source (p : ℕ) (hp : p.Prime)
    (hG : IsPGroup p G) (K : Subgroup G) (hK : K ≠ ⊤) :
    ∃ f : G →* Multiplicative (ZMod p), Function.Surjective f ∧ K ≤ f.ker :=
  finitePGroup_proper_subgroup_character p hp hG K hK

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `profinite_closed_subgroup_proper_quotient`. -/
theorem actual_fixed_prop_topological_generation_profinite_closed_subgroup_proper_quotient_source (G : ProfiniteGrp)
    (K : Subgroup G) (hclosed : IsClosed (K : Set G)) (hK : K ≠ ⊤) :
    ∃ U : OpenNormalSubgroup G,
      K.map (QuotientGroup.mk' U.toSubgroup) ≠ ⊤ :=
  profinite_closed_subgroup_proper_quotient G K hclosed hK

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `proP_closed_subgroup_character`. -/
theorem actual_fixed_prop_topological_generation_proP_closed_subgroup_character_source (p : ℕ) (hp : p.Prime) (G : ProfiniteGrp)
    (hP : ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup))
    (K : Subgroup G) (hclosed : IsClosed (K : Set G)) (hK : K ≠ ⊤) :
    ∃ f : G →ₜ* Multiplicative (ZMod p),
      Function.Surjective f ∧ K ≤ f.toMonoidHom.ker :=
  proP_closed_subgroup_character p hp G hP K hclosed hK

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `proP_finitely_generated_of_finite_characters`. -/
theorem actual_fixed_prop_topological_generation_proP_finitely_generated_of_finite_characters_source (p : ℕ) (hp : p.Prime)
    (G : ProfiniteGrp)
    (hP : ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup))
    [Finite (G →ₜ* Multiplicative (ZMod p))] :
    ∃ S : Finset G, (Subgroup.closure (S : Set G)).topologicalClosure = ⊤ :=
  proP_finitely_generated_of_finite_characters p hp G hP

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `profiniteProPQuotient_finitely_generated`. -/
theorem actual_fixed_prop_topological_generation_profiniteProPQuotient_finitely_generated_source (p : ℕ) (hp : p.Prime) (G : ProfiniteGrp)
    [Finite (G →ₜ* Multiplicative (ZMod p))] :
    ∃ S : Finset (G ⧸ profiniteProPKernel p G),
      (Subgroup.closure (S : Set (G ⧸ profiniteProPKernel p G))).topologicalClosure = ⊤ :=
  profiniteProPQuotient_finitely_generated p hp G

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [DecidableEq H]

/-- Exact original-object consumer of `continuous_surjective_image_topological_generators`. -/
theorem actual_fixed_residual_topological_generation_continuous_surjective_image_topological_generators_source
    (f : G →* H) (hf : Continuous f) (hsurj : Function.Surjective f)
    (S : Finset G) (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤) :
    (Subgroup.closure ((S.image f) : Set H)).topologicalClosure = ⊤ :=
  continuous_surjective_image_topological_generators f hf hsurj S hS

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Exact original-object consumer of `finiteIndex_normal_topological_generators`. -/
theorem actual_fixed_residual_topological_generation_finiteIndex_normal_topological_generators_source
    (K : Subgroup G) [K.Normal] [Finite (G ⧸ K)]
    (S : Finset K) (hS : (Subgroup.closure (S : Set K)).topologicalClosure = ⊤) :
    ∃ T : Finset G, (Subgroup.closure (T : Set G)).topologicalClosure = ⊤ :=
  finiteIndex_normal_topological_generators K S hS

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `fixedResidualQuotientSubgroupFactor_continuous`. -/
theorem actual_fixed_residual_topological_generation_fixedResidualQuotientSubgroupFactor_continuous_source
    (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    (hK : IsClosed (K : Set G)) :
    Continuous (fixedResidualQuotientSubgroupFactor p G K hK) :=
  fixedResidualQuotientSubgroupFactor_continuous p G K hK

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `fixedResidualQuotient_finitely_generated`. -/
theorem actual_fixed_residual_topological_generation_fixedResidualQuotient_finitely_generated_source
    (p : ℕ) (hp : p.Prime) (G : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    [Finite (G ⧸ K)] (hK : IsClosed (K : Set G))
    [Finite (K →ₜ* Multiplicative (ZMod p))] :
    ∃ S : Finset (G ⧸ fixedResidualProPKernel p G K hK),
      (Subgroup.closure (S : Set (G ⧸ fixedResidualProPKernel p G K hK))).topologicalClosure = ⊤ :=
  fixedResidualQuotient_finitely_generated p hp G K hK

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [T2Space Y]

/-- Exact original-object consumer of `compactOpenSurjection_totallySeparated`. -/
theorem actual_fixed_residual_profinite_presentation_compactOpenSurjection_totallySeparated_source (f : X → Y)
    (hf : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f) :
    TotallySeparatedSpace Y :=
  compactOpenSurjection_totallySeparated f hf hopen hsurj

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `closedProfiniteQuotient_totallyDisconnected`. -/
theorem actual_fixed_residual_profinite_presentation_closedProfiniteQuotient_totallyDisconnected_source (G : ProfiniteGrp)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) :=
  closedProfiniteQuotient_totallyDisconnected G N hN

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `profiniteGeneratorPresentation_surjective`. -/
theorem actual_fixed_residual_profinite_presentation_profiniteGeneratorPresentation_surjective_source (G : ProfiniteGrp) (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤) :
    Function.Surjective (profiniteGeneratorPresentation G S) :=
  profiniteGeneratorPresentation_surjective G S hS

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


/-- Exact original-object consumer of `fixedResidualProfiniteQuotient_has_presentation`. -/
theorem actual_fixed_residual_profinite_presentation_fixedResidualProfiniteQuotient_has_presentation_source
    (p : ℕ) (hp : p.Prime) (G : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    [Finite (G ⧸ K)] (hK : IsClosed (K : Set G))
    [Finite (K →ₜ* Multiplicative (ZMod p))] :
    ∃ S : Finset (fixedResidualProfiniteQuotient p G K hK),
      Function.Surjective (profiniteGeneratorPresentation
        (fixedResidualProfiniteQuotient p G K hK) S) :=
  fixedResidualProfiniteQuotient_has_presentation p hp G K hK

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `compactNoetherianAdicQuotient_complete`. -/
theorem actual_completed_presentation_relations_compactNoetherianAdicQuotient_complete_source
    [CompactSpace R] [T2Space R] [IsNoetherianRing R]
    (I J : Ideal R) (hI : IsAdic I) :
    IsAdicComplete (I.map (Ideal.Quotient.mk J)) (R ⧸ J) :=
  compactNoetherianAdicQuotient_complete I J hI

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing A]

/-- Exact original-object consumer of `matrixRepresentationRelationIdeal_le_kernel_iff`. -/
theorem actual_completed_presentation_relations_matrixRepresentationRelationIdeal_le_kernel_iff_source
    (ρ : G →* GeneralLinearGroup ι R) (N : Subgroup G) (f : R →+* A) :
    matrixRepresentationRelationIdeal ρ N ≤ RingHom.ker f ↔
      N ≤ ((GeneralLinearGroup.map (n := ι) f).comp ρ).ker :=
  matrixRepresentationRelationIdeal_le_kernel_iff ρ N f

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι R : Type*} [Group G] [TopologicalSpace G]
  [Fintype ι] [DecidableEq ι] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `matrixRelationQuotientRepresentation_continuous`. -/
theorem actual_completed_presentation_relations_matrixRelationQuotientRepresentation_continuous_source
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (N : Subgroup G) [N.Normal] :
    Continuous (matrixRelationQuotientRepresentation ρ N) :=
  matrixRelationQuotientRepresentation_continuous ρ hρ N

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {G ι O R A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [CommRing A] [Algebra O R] [Algebra O A]

/-- Exact original-object consumer of `matrixRelationCoefficientMap_representation`. -/
theorem actual_completed_presentation_relations_matrixRelationCoefficientMap_representation_source
    (ρ : G →* GeneralLinearGroup ι R) (N : Subgroup G) [N.Normal] (f : R →ₐ[O] A)
    (hf : N ≤ ((GeneralLinearGroup.map (n := ι) f.toRingHom).comp ρ).ker) (g : G) :
    GeneralLinearGroup.map (n := ι) (matrixRelationCoefficientMap ρ N f hf).toRingHom
      (matrixRelationQuotientRepresentation ρ N (QuotientGroup.mk' N g)) =
        GeneralLinearGroup.map (n := ι) f.toRingHom (ρ g) :=
  matrixRelationCoefficientMap_representation ρ N f hf g

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

universe u

variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedPresentationCoefficientQuotient_isAdicComplete`. -/
theorem actual_completed_presentation_relations_completedPresentationCoefficientQuotient_isAdicComplete_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))) :
    IsAdicComplete
      ((IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)).map
        (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ N)))
      (CompletedPresentationCoefficientQuotient ρ N) :=
  completedPresentationCoefficientQuotient_isAdicComplete ρ N

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

universe u

variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedUniversalProfiniteRepresentation_reduction`. -/
theorem actual_original_residue_uniform_factors_completedUniversalProfiniteRepresentation_reduction_source
    [T2Space (IsLocalRing.ResidueField O)]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (σ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →*
      GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    (hσeta : ∀ g, σ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = ρ g) :
    (GeneralLinearGroup.map (n := ι)
      (completedResidualRepresentationEvaluation ρ).toRingHom).comp
        (completedUniversalProfiniteRepresentation ρ).toMonoidHom = σ :=
  completedUniversalProfiniteRepresentation_reduction ρ σ hσ hσeta

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

universe u

variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedPresentationRelationIdeal_le_maximal`. -/
theorem actual_original_residue_uniform_factors_completedPresentationRelationIdeal_le_maximal_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (σ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →*
      GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    (hσeta : ∀ g, σ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = ρ g)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ σ.ker) :
    completedPresentationRelationIdeal ρ N ≤
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) :=
  completedPresentationRelationIdeal_le_maximal ρ σ hσ hσeta N hN

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [Finite (IsLocalRing.ResidueField A)]

/-- Exact original-object consumer of `completeLocalAdic_compactSpace`. -/
theorem actual_original_residue_uniform_factors_completeLocalAdic_compactSpace_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A) : CompactSpace A :=
  completeLocalAdic_compactSpace hA

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct


variable {R ι : Type*} [CommRing R] [WithIdeal R] [T2Space R] [CompactSpace R]
  [Fintype ι] [DecidableEq ι]

/-- Exact original-object consumer of `adicResidualProfiniteKernel_commonKernel_eq_bot`. -/
theorem actual_original_residue_uniform_factors_adicResidualProfiniteKernel_commonKernel_eq_bot_source
    (p : ℕ) (hp : p.Prime) (hpI : (p : R) ∈ (WithIdeal.i : Ideal R)) :
    profiniteProPKernel p (adicResidualProfiniteKernel (R := R) (ι := ι)) = ⊥ :=
  adicResidualProfiniteKernel_commonKernel_eq_bot p hp hpI

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

universe u

variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `originalResidual_fixedKernel_le_every_coefficient_lift`. -/
theorem actual_original_residue_uniform_factors_originalResidual_fixedKernel_le_every_coefficient_lift_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (f : H →* GeneralLinearGroup ι A) (hf : Continuous f)
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp f = σ) :
    fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ) ≤ f.ker :=
  originalResidual_fixedKernel_le_every_coefficient_lift hA e p hp H σ hσ f hf hres

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

universe u

variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `completedCoefficientMapOfProfiniteLift_entire`. -/
theorem actual_continuous_presentation_universality_completedCoefficientMapOfProfiniteLift_entire_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ) :
    (GeneralLinearGroup.map (n := ι) (completedCoefficientMapOfProfiniteLift ρ e τ hτ).toRingHom).comp
      (completedUniversalProfiniteRepresentation ρ).toMonoidHom = τ.toMonoidHom :=
  completedCoefficientMapOfProfiniteLift_entire hA ρ e τ hτ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

universe u

variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `profiniteRelationCoefficientMap_unique`. -/
theorem actual_continuous_presentation_universality_profiniteRelationCoefficientMap_unique_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction τ) = ρ)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ τ.toMonoidHom.ker)
    (f : CompletedPresentationCoefficientQuotient ρ N →ₐ[O] A)
    (hf : ∀ g : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G),
      GeneralLinearGroup.map (n := ι) f.toRingHom
        (GeneralLinearGroup.map (n := ι)
          (Ideal.Quotient.mk (completedPresentationRelationIdeal ρ N))
          (completedUniversalProfiniteRepresentation ρ g)) = τ g) :
    f = profiniteRelationCoefficientMap hA ρ e τ hτ N hN :=
  profiniteRelationCoefficientMap_unique hA ρ e τ hτ N hN f hf

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

universe u

variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedPresentedGroupRepresentation_continuous`. -/
theorem actual_continuous_presentation_universality_completedPresentedGroupRepresentation_continuous_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) : Continuous (completedPresentationRepresentation ρ H q hq) :=
  completedPresentedGroupRepresentation_continuous ρ H q hq

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct

universe u

variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `completedPresentationCoefficient_exists_unique`. -/
theorem actual_continuous_presentation_universality_completedPresentationCoefficient_exists_unique_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) (σ : H →ₜ* GeneralLinearGroup ι A)
    (hσ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction (σ.comp q)) = ρ) :
    ∃! f : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker →ₐ[O] A,
      (∀ h : H, GeneralLinearGroup.map (n := ι) f.toRingHom
        (completedPresentationRepresentation ρ H q hq h) = σ h) ∧
      Continuous f ∧
      ((localCoefficientReduction e).comp f).comp
        (Ideal.Quotient.mkₐ O (completedPresentationRelationIdeal ρ q.toMonoidHom.ker)) =
          completedResidualRepresentationEvaluation ρ :=
  completedPresentationCoefficient_exists_unique hA ρ e H q hq σ hσ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField


variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Exact original-object consumer of `sUnitValuations_mem_ker_iff`. -/
theorem actual_number_field_s_unit_sUnitValuations_mem_ker_iff_source (S : Set (HeightOneSpectrum R))
    (x : S.unit K) :
    x ∈ (sUnitValuations (K := K) S).ker ↔
      x.val ∈ (∅ : Set (HeightOneSpectrum R)).unit K :=
  sUnitValuations_mem_ker_iff S x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField


/-- Exact original-object consumer of `numberField_sUnit_powerQuotient_finite`. -/
theorem actual_number_field_s_unit_numberField_sUnit_powerQuotient_finite_source (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (n : ℕ) (hn : n ≠ 0) :
    Finite (S.unit K ⧸ (powMonoidHom (α := S.unit K) n).range) :=
  numberField_sUnit_powerQuotient_finite K S hS n hn

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Exact original-object consumer of `fractionalIdealCountRootUnit_pow`. -/
theorem actual_selmer_ideal_root_fractionalIdealCountRootUnit_pow_source (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ)
    (hdiv : ∀ v : HeightOneSpectrum R, (n : ℤ) ∣ FractionalIdeal.count K v I.val) :
    fractionalIdealCountRootUnit n I ^ n = I :=
  fractionalIdealCountRootUnit_pow n I hdiv

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Exact original-object consumer of `emptySelmer_mem_iff_principal_counts`. -/
theorem actual_selmer_ideal_root_emptySelmer_mem_iff_principal_counts_source (n : ℕ) (x : Kˣ) :
    QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range x ∈
        (IsDedekindDomain.selmerGroup (R := R) (K := K)
          (S := ∅) (n := n)) ↔
      ∀ v : HeightOneSpectrum R,
        (n : ℤ) ∣ FractionalIdeal.count K v (toPrincipalIdeal R K x).val :=
  emptySelmer_mem_iff_principal_counts n x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Exact original-object consumer of `emptySelmerRepresentativeIdealRoot_mul`. -/
theorem actual_number_field_selmer_finite_emptySelmerRepresentativeIdealRoot_mul_source (n : ℕ) (hn : n ≠ 0)
    (x y : EmptySelmerRepresentativeUnits (R := R) (K := K) n) :
    emptySelmerRepresentativeIdealRoot n (x * y) =
      emptySelmerRepresentativeIdealRoot n x * emptySelmerRepresentativeIdealRoot n y :=
  emptySelmerRepresentativeIdealRoot_mul n hn x y

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Exact original-object consumer of `emptySelmerClassMap_apply_representative`. -/
theorem actual_number_field_selmer_finite_emptySelmerClassMap_apply_representative_source (n : ℕ) (hn : n ≠ 0)
    (x : EmptySelmerRepresentativeUnits (R := R) (K := K) n) :
    emptySelmerClassMap n hn (emptySelmerRepresentativeProjection n x) =
      emptySelmerRepresentativeClass n hn x :=
  emptySelmerClassMap_apply_representative n hn x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Exact original-object consumer of `emptySelmerClassMap_kernel_eq_unitRange`. -/
theorem actual_number_field_selmer_finite_emptySelmerClassMap_kernel_eq_unitRange_source (n : ℕ) (hn : n ≠ 0) :
    (emptySelmerClassMap (R := R) (K := K) n hn).ker =
      (IsDedekindDomain.selmerGroup.fromUnit (R := R) (K := K) (n := n)).range :=
  emptySelmerClassMap_kernel_eq_unitRange n hn

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


/-- Exact original-object consumer of `numberField_selmer_finite`. -/
theorem actual_number_field_selmer_finite_numberField_selmer_finite_source (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (n : ℕ) (hn : n ≠ 0) :
    Finite (IsDedekindDomain.selmerGroup (R := 𝓞 K) (K := K) (S := S) (n := n)) :=
  numberField_selmer_finite K S hS n hn

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Exact original-object consumer of `finiteGaloisCharacter_exists_radical`. -/
theorem actual_galois_kummer_character_finiteGaloisCharacter_exists_radical_source [FiniteDimensional K L] [IsGalois K L]
    (χ : Gal(L/K) →* Kˣ) (n : ℕ) (hχ : ∀ g : Gal(L/K), χ g ^ n = 1) :
    ∃ (a : Kˣ) (β : Lˣ),
      β ^ n = Units.map (algebraMap K L).toMonoidHom a ∧
      ∀ g : Gal(L/K), g • β / β = Units.map (algebraMap K L).toMonoidHom (χ g) :=
  finiteGaloisCharacter_exists_radical χ n hχ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Exact original-object consumer of `galois_characters_eq_of_radical_power_class`. -/
theorem actual_galois_kummer_character_galois_characters_eq_of_radical_power_class_source (n : ℕ) [NeZero n]
    (hζ : (primitiveRoots n K).Nonempty) (χ ψ : Gal(L/K) →* Kˣ)
    (a b : Kˣ) (β γ : Lˣ)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (hγ : γ ^ n = Units.map (algebraMap K L).toMonoidHom b)
    (hχ : ∀ g : Gal(L/K), g • β / β = Units.map (algebraMap K L).toMonoidHom (χ g))
    (hψ : ∀ g : Gal(L/K), g • γ / γ = Units.map (algebraMap K L).toMonoidHom (ψ g))
    (hab : QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range a =
      QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range b) : χ = ψ :=
  galois_characters_eq_of_radical_power_class n hζ χ ψ a b β γ hβ hγ hχ hψ hab

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω T : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [Group T]

/-- Exact original-object consumer of `continuous_galois_finite_factor`. -/
theorem actual_continuous_galois_kummer_continuous_galois_finite_factor_source [TopologicalSpace T] [DiscreteTopology T]
    (χ : Gal(Ω/K) →ₜ* T) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ ψ : Gal(F/K) →* T, ∀ g : Gal(Ω/K),
        ψ (AlgEquiv.restrictNormalHom F g) = χ g :=
  continuous_galois_finite_factor χ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Exact original-object consumer of `continuous_galois_character_exists_radical`. -/
theorem actual_continuous_galois_kummer_continuous_galois_character_exists_radical_source
    [TopologicalSpace Kˣ] [DiscreteTopology Kˣ]
    (χ : Gal(Ω/K) →ₜ* Kˣ) (n : ℕ) (hχ : ∀ g : Gal(Ω/K), χ g ^ n = 1) :
    ∃ (a : Kˣ) (β : Ωˣ),
      β ^ n = Units.map (algebraMap K Ω).toMonoidHom a ∧
      ∀ g : Gal(Ω/K), g • β / β = Units.map (algebraMap K Ω).toMonoidHom (χ g) :=
  continuous_galois_character_exists_radical χ n hχ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace Kˣ] [DiscreteTopology Kˣ]

/-- Exact original-object consumer of `continuousGaloisKummerClass_injective`. -/
theorem actual_continuous_galois_kummer_continuousGaloisKummerClass_injective_source (n : ℕ) [NeZero n]
    (hζ : (primitiveRoots n K).Nonempty) :
    Function.Injective (continuousGaloisKummerClass (K := K) (Ω := Ω) n) :=
  continuousGaloisKummerClass_injective n hζ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]

/-- Exact original-object consumer of `unramified_intValuation_algebraMap`. -/
theorem actual_unramified_radical_selmer_unramified_intValuation_algebraMap_source
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
    (he : v.asIdeal.ramificationIdx w.asIdeal = 1) (r : R) :
    w.intValuation (algebraMap R S r) = v.intValuation r :=
  unramified_intValuation_algebraMap v w he r

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R S K L : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]

/-- Exact original-object consumer of `unramified_valuationOfNeZero_algebraMap`. -/
theorem actual_unramified_radical_selmer_unramified_valuationOfNeZero_algebraMap_source
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
    (he : v.asIdeal.ramificationIdx w.asIdeal = 1) (x : Kˣ) :
    w.valuationOfNeZero (Units.map (algebraMap K L).toMonoidHom x) =
      v.valuationOfNeZero x :=
  unramified_valuationOfNeZero_algebraMap v w he x

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R S K L : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]

/-- Exact original-object consumer of `unramified_radical_mem_selmer`. -/
theorem actual_unramified_radical_selmer_unramified_radical_mem_selmer_source
    (T : Set (HeightOneSpectrum R))
    (hunram : ∀ v : HeightOneSpectrum R, v ∉ T →
      ∃ w : HeightOneSpectrum S, w.asIdeal.LiesOver v.asIdeal ∧
        v.asIdeal.ramificationIdx w.asIdeal = 1)
    (n : ℕ) (a : Kˣ) (β : Lˣ)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) :
    QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range a ∈
      IsDedekindDomain.selmerGroup (R := R) (K := K) (S := T) (n := n) :=
  unramified_radical_mem_selmer T hunram n a β hβ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Exact original-object consumer of `continuousGaloisKummerClass_eq_of_radical`. -/
theorem actual_galois_class_independence_restriction_continuousGaloisKummerClass_eq_of_radical_source
    [TopologicalSpace Kˣ] [DiscreteTopology Kˣ] (n : ℕ)
    (χ : ContinuousGaloisExponentCharacters (K := K) (Ω := Ω) n)
    (a : Kˣ) (β : Ωˣ)
    (hβ : β ^ n = Units.map (algebraMap K Ω).toMonoidHom a)
    (hχ : ∀ g : Gal(Ω/K), g • β / β =
      Units.map (algebraMap K Ω).toMonoidHom (χ.val g)) :
    continuousGaloisKummerClass n χ =
      QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range a :=
  continuousGaloisKummerClass_eq_of_radical n χ a β hβ hχ

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


/-- Exact original-object consumer of `coprime_quotient_continuous_characters_finite`. -/
theorem actual_galois_class_independence_restriction_coprime_quotient_continuous_characters_finite_source
    {G T : Type*} [Group G] [CommGroup T] [TopologicalSpace G] [TopologicalSpace T]
    (H : Subgroup G) [H.Normal]
    (hcard : (Nat.card (G ⧸ H)).Coprime (Nat.card T))
    [Finite (H →ₜ* T)] : Finite (G →ₜ* T) :=
  coprime_quotient_continuous_characters_finite H hcard

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Exact original-object consumer of `cyclotomic_prime_finrank_coprime`. -/
theorem actual_cyclotomic_galois_character_descent_cyclotomic_prime_finrank_coprime_source (p : ℕ) (hp : p.Prime)
    [IsCyclotomicExtension {p} K L] : (Module.finrank K L).Coprime p :=
  cyclotomic_prime_finrank_coprime p hp

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- Exact original-object consumer of `finiteBase_fixingSubgroup_characters_finite`. -/
theorem actual_cyclotomic_galois_character_descent_finiteBase_fixingSubgroup_characters_finite_source [IsGalois K Ω]
    {T : Type*} [Group T] [TopologicalSpace T]
    (F : IntermediateField K Ω) [FiniteDimensional K F]
    [Finite (Gal(Ω/F) →ₜ* T)] : Finite (F.fixingSubgroup →ₜ* T) :=
  finiteBase_fixingSubgroup_characters_finite F

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Exact original-object consumer of `cyclotomic_continuous_prime_characters_finite`. -/
theorem actual_cyclotomic_galois_character_descent_cyclotomic_continuous_prime_characters_finite_source
    (p : ℕ) (hp : p.Prime) (F : IntermediateField K Ω)
    [IsCyclotomicExtension {p} K F]
    [Finite (Gal(Ω/F) →ₜ* Multiplicative (ZMod p))] :
    Finite (Gal(Ω/K) →ₜ* Multiplicative (ZMod p)) :=
  cyclotomic_continuous_prime_characters_finite p hp F

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K : Type*} [Field K]

variable {Ω : Type*} [Field Ω] [Algebra K Ω]
  [TopologicalSpace Kˣ]

/-- Exact original-object consumer of `prime_characters_finite_of_unit_exponent_characters`. -/
theorem actual_prime_root_unit_characters_prime_characters_finite_of_unit_exponent_characters_source (p : ℕ) (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    [Finite (ContinuousGaloisExponentCharacters (K := K) (Ω := Ω) p)] :
    Finite (Gal(Ω/K) →ₜ* Multiplicative (ZMod p)) :=
  prime_characters_finite_of_unit_exponent_characters p hp hζ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

variable [IsGalois K Ω] [TopologicalSpace Kˣ] [DiscreteTopology Kˣ]

/-- Exact original-object consumer of `unramified_continuous_prime_characters_finite`. -/
theorem actual_unramified_galois_character_finiteness_unramified_continuous_prime_characters_finite_source
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (hunram : ∀ F : FiniteGaloisIntermediateField K Ω,
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
          v.asIdeal.ramificationIdx w.asIdeal = 1)
    (p : ℕ) (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Finite (Gal(Ω/K) →ₜ* Multiplicative (ZMod p)) :=
  unramified_continuous_prime_characters_finite S hS hunram p hp hζ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]

/-- Exact original-object consumer of `heightOneUnder_preimage_finite`. -/
theorem actual_finite_prime_base_change_heightOneUnder_preimage_finite_source
    (S : Set (HeightOneSpectrum A)) (hS : S.Finite) :
    {w : HeightOneSpectrum B | w.under A ∈ S}.Finite :=
  heightOneUnder_preimage_finite S hS

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R S T : Type*} [CommRing R] [IsDomain R]
  [CommRing S] [IsDedekindDomain S] [CommRing T] [IsDedekindDomain T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [Module.IsTorsionFree R S] [Module.IsTorsionFree S T]

/-- Exact original-object consumer of `unramifiedIdealTower_indices`. -/
theorem actual_finite_prime_base_change_unramifiedIdealTower_indices_source
    (p : Ideal R) (P : Ideal S) (Q : Ideal T)
    [Q.IsPrime] [Q.LiesOver P] [P.LiesOver p]
    (h : p.ramificationIdx Q = 1) :
    p.ramificationIdx P = 1 ∧ P.ramificationIdx Q = 1 :=
  unramifiedIdealTower_indices p P Q h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R S : Type*} [CommRing O] [CommRing R] [IsLocalRing R]
  [CommRing S] [IsLocalRing S] [Algebra O R] [Algebra O S]

/-- Exact original-object consumer of `localResidueAlgebraMap_surjective`. -/
theorem actual_local_quotient_residue_localResidueAlgebraMap_surjective_source (f : R →ₐ[O] S) [IsLocalHom f.toRingHom]
    (hf : Function.Surjective f) : Function.Surjective (localResidueAlgebraMap f) :=
  localResidueAlgebraMap_surjective f hf

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O R : Type*} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Exact original-object consumer of `compactLocalAdicQuotient_maximal_complete`. -/
theorem actual_local_quotient_residue_compactLocalAdicQuotient_maximal_complete_source
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    [IsNoetherianRing R] (J : Ideal R) [IsLocalRing (R ⧸ J)]
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) :
    IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ J)) (R ⧸ J) :=
  compactLocalAdicQuotient_maximal_complete J hR

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

/-- Exact original-object consumer of `heightOnePrime_exists_liesOver`. -/
theorem actual_finite_base_unramified_heightOnePrime_exists_liesOver_source (v : HeightOneSpectrum R) :
    ∃ w : HeightOneSpectrum S, w.asIdeal.LiesOver v.asIdeal :=
  heightOnePrime_exists_liesOver v

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Exact original-object consumer of `numberField_galois_unramified_at_every_prime`. -/
theorem actual_finite_base_unramified_numberField_galois_unramified_at_every_prime_source
    (v : HeightOneSpectrum (𝓞 K))
    (h : ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal ∧
      v.asIdeal.ramificationIdx w.asIdeal = 1)
    (z : HeightOneSpectrum (𝓞 L)) [z.asIdeal.LiesOver v.asIdeal] :
    v.asIdeal.ramificationIdx z.asIdeal = 1 :=
  numberField_galois_unramified_at_every_prime v h z

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]
  [IsGalois K Ω]

/-- Exact original-object consumer of `finiteBase_unramified_finite_subextensions`. -/
theorem actual_finite_base_unramified_finiteBase_unramified_finite_subextensions_source
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (hunram : ∀ F : FiniteGaloisIntermediateField K Ω,
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
          v.asIdeal.ramificationIdx w.asIdeal = 1)
    (E : IntermediateField K Ω) [FiniteDimensional K E] [NumberField E]
    (F : FiniteGaloisIntermediateField E Ω)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v.under (𝓞 K) ∉ S) :
    ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
      v.asIdeal.ramificationIdx w.asIdeal = 1 :=
  finiteBase_unramified_finite_subextensions S hunram E F v hv

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- Exact original-object consumer of `numberField_isUnramifiedAt_iff_ramificationIdx_one`. -/
theorem actual_unramified_tensor_image_numberField_isUnramifiedAt_iff_ramificationIdx_one_source
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal ↔
      v.asIdeal.ramificationIdx w.asIdeal = 1 :=
  numberField_isUnramifiedAt_iff_ramificationIdx_one v w

end

section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R A B Ω : Type*} [CommRing R] [CommRing A] [CommRing B] [Field Ω]
  [Algebra R A] [Algebra R B] [Algebra R Ω]

/-- Exact original-object consumer of `ambientTensorImage_isIntegralClosure`. -/
theorem actual_unramified_tensor_image_ambientTensorImage_isIntegralClosure_source [IsDedekindDomain R]
    [Module.Finite R A] [Module.Finite R B]
    [Algebra.FormallyUnramified R A] [Algebra.FormallyUnramified R B]
    (f : A →ₐ[R] Ω) (g : B →ₐ[R] Ω) :
    IsIntegralClosure (AmbientTensorImage f g) R (FractionRing (AmbientTensorImage f g)) :=
  ambientTensorImage_isIntegralClosure f g

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R A B Ω : Type*} [CommRing R] [CommRing A] [CommRing B] [Field Ω]
  [Algebra R A] [Algebra R B] [Algebra R Ω]

/-- Exact original-object consumer of `ambientTensorFractionEmbedding_compositum`. -/
theorem actual_tensor_fraction_compositum_ambientTensorFractionEmbedding_compositum_source
    {L M : Type*} [Field L] [Field M]
    [Algebra A L] [IsFractionRing A L] [Algebra B M] [IsFractionRing B M]
    (f : A →ₐ[R] Ω) (g : B →ₐ[R] Ω) (i : L →+* Ω) (j : M →+* Ω)
    (hi : i.comp (algebraMap A L) = f.toRingHom)
    (hj : j.comp (algebraMap B M) = g.toRingHom) :
    (ambientTensorFractionEmbedding f g).fieldRange = i.fieldRange ⊔ j.fieldRange :=
  ambientTensorFractionEmbedding_compositum f g i j hi hj

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R A B Ω : Type*} [CommRing R] [CommRing A] [CommRing B] [Field Ω]
  [Algebra R A] [Algebra R B] [Algebra R Ω]

/-- Exact original-object consumer of `ambientTensorImage_mem_iff_compositum_integral`. -/
theorem actual_tensor_compositum_integral_closure_ambientTensorImage_mem_iff_compositum_integral_source [IsDedekindDomain R]
    [Module.Finite R A] [Module.Finite R B]
    [Algebra.FormallyUnramified R A] [Algebra.FormallyUnramified R B]
    {L M : Type*} [Field L] [Field M]
    [Algebra A L] [IsFractionRing A L] [Algebra B M] [IsFractionRing B M]
    (f : A →ₐ[R] Ω) (g : B →ₐ[R] Ω) (i : L →+* Ω) (j : M →+* Ω)
    (hi : i.comp (algebraMap A L) = f.toRingHom)
    (hj : j.comp (algebraMap B M) = g.toRingHom) (x : Ω) :
    x ∈ AmbientTensorImage f g ↔
      x ∈ i.fieldRange ⊔ j.fieldRange ∧ IsIntegral R x :=
  ambientTensorImage_mem_iff_compositum_integral f g i j hi hj x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `completedPresentationFramedFiberEquiv_bijective`. -/
theorem actual_continuous_framed_fibers_completedPresentationFramedFiberEquiv_bijective_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) :
    Function.Bijective (completedPresentationFramedFiberEquiv hA ρ e H q hq) :=
  completedPresentationFramedFiberEquiv_bijective hA ρ e H q hq

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R : Type*} [CommRing R] [IsLocalRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Exact original-object consumer of `localQuotient_maximal_adicTopology`. -/
theorem actual_local_quotient_topology_equality_localQuotient_maximal_adicTopology_source
    (J : Ideal R) [IsLocalRing (R ⧸ J)]
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) :
    (inferInstance : TopologicalSpace (R ⧸ J)) =
      (IsLocalRing.maximalIdeal (R ⧸ J)).adicTopology :=
  localQuotient_maximal_adicTopology J hR

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G ι O A B : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B]
  [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- Exact original-object consumer of `completedPresentationFramedFiberEquiv_natural`. -/
theorem actual_continuous_framed_fiber_naturality_completedPresentationFramedFiberEquiv_natural_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (f : PresentedContinuousCoefficientFiber ρ eA H q) :
    completedPresentationFramedFiberEquiv hB ρ eB H q hq
      (presentedCoefficientFiberPostcomp ρ eA eB H q k hk hres f) =
        presentedRepresentationFiberPostcomp ρ eA eB H q k hk hres
          (completedPresentationFramedFiberEquiv hA ρ eA H q hq f) :=
  completedPresentationFramedFiberEquiv_natural hA hB ρ eA eB H q hq k hk hres f

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedPresentationCoefficientQuotient_localData`. -/
theorem actual_completed_presentation_local_data_completedPresentationCoefficientQuotient_localData_source
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (σ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →*
      GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    (hσeta : ∀ g, σ (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = ρ g)
    (N : Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))
    (hN : N ≤ σ.ker) :
    ∃ hlocal : IsLocalRing (CompletedPresentationCoefficientQuotient ρ N),
      (letI := hlocal
       ∃ e : IsLocalRing.ResidueField (CompletedPresentationCoefficientQuotient ρ N) ≃ₐ[O]
           IsLocalRing.ResidueField O,
         IsNoetherianRing (CompletedPresentationCoefficientQuotient ρ N) ∧
         IsAdicComplete (IsLocalRing.maximalIdeal (CompletedPresentationCoefficientQuotient ρ N))
           (CompletedPresentationCoefficientQuotient ρ N) ∧
         (inferInstance : TopologicalSpace (CompletedPresentationCoefficientQuotient ρ N)) =
           (IsLocalRing.maximalIdeal (CompletedPresentationCoefficientQuotient ρ N)).adicTopology ∧
         ∀ r : ResidualRepresentationCompletion ρ,
           e (IsLocalRing.residue _ (Ideal.Quotient.mk
             (completedPresentationRelationIdeal ρ N) r)) =
             completedResidualRepresentationEvaluation ρ r) :=
  completedPresentationCoefficientQuotient_localData ρ σ hσ hσeta N hN

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `completedPresentationRepresentation_trueResidue`. -/
theorem actual_completed_presentation_true_residue_completedPresentationRepresentation_trueResidue_source
    [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσeta : ∀ g, σ (q (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g)) = ρ g) :
    (GeneralLinearGroup.map (n := ι)
      (localCoefficientReduction (completedPresentationResidueEquiv ρ
        q.toMonoidHom.ker)).toRingHom).comp
        (completedPresentationRepresentation ρ H q hq) = σ.toMonoidHom :=
  completedPresentationRepresentation_trueResidue ρ H q hq σ hσeta

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- Exact original-object consumer of `numberField_formallyUnramified_away`. -/
theorem actual_number_field_unramified_away_numberField_formallyUnramified_away_source
    (a : 𝓞 K)
    (hunram : ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1) :
    Algebra.FormallyUnramified (𝓞 K)
      (Localization.Away (algebraMap (𝓞 K) (𝓞 L) a)) :=
  numberField_formallyUnramified_away a hunram

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- Exact original-object consumer of `numberField_localizedIntegers_finite_unramified`. -/
theorem actual_number_field_localized_integer_algebras_numberField_localizedIntegers_finite_unramified_source
    (a : 𝓞 K) (Rₐ Sₐ : Type*) [CommRing Rₐ] [CommRing Sₐ]
    [Algebra (𝓞 K) Rₐ] [Algebra (𝓞 K) Sₐ] [Algebra (𝓞 L) Sₐ]
    [Algebra Rₐ Sₐ] [IsScalarTower (𝓞 K) (𝓞 L) Sₐ]
    [IsScalarTower (𝓞 K) Rₐ Sₐ]
    [IsLocalization.Away a Rₐ]
    [IsLocalization.Away (algebraMap (𝓞 K) (𝓞 L) a) Sₐ]
    (hunram : ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1) :
    Module.Finite Rₐ Sₐ ∧ Algebra.FormallyUnramified Rₐ Sₐ :=
  numberField_localizedIntegers_finite_unramified a Rₐ Sₐ hunram

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- Exact original-object consumer of `localizedNumberFieldIntegers_integral_iff`. -/
theorem actual_localized_integer_integral_closure_localizedNumberFieldIntegers_integral_iff_source
    (a : 𝓞 K) (ha : a ≠ 0) (Rₐ Sₐ : Type*) [CommRing Rₐ] [CommRing Sₐ]
    [Algebra (𝓞 K) Rₐ] [Algebra (𝓞 K) Sₐ] [Algebra (𝓞 L) Sₐ]
    [Algebra Rₐ Sₐ] [IsScalarTower (𝓞 K) (𝓞 L) Sₐ]
    [IsScalarTower (𝓞 K) Rₐ Sₐ]
    [IsLocalization.Away a Rₐ]
    [IsLocalization.Away (algebraMap (𝓞 K) (𝓞 L) a) Sₐ]
    [Algebra Rₐ L] [Algebra Sₐ L] [IsScalarTower (𝓞 L) Sₐ L]
    [IsScalarTower Rₐ Sₐ L] (x : L) :
    IsIntegral Rₐ x ↔ ∃ y : Sₐ, algebraMap Sₐ L y = x :=
  localizedNumberFieldIntegers_integral_iff a ha Rₐ Sₐ x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- Exact original-object consumer of `numberField_localizedIntegers_unramified_iff`. -/
theorem actual_localized_integer_ramification_equivalence_numberField_localizedIntegers_unramified_iff_source
    (a : 𝓞 K) (Rₐ Sₐ : Type*) [CommRing Rₐ] [CommRing Sₐ]
    [Algebra (𝓞 K) Rₐ] [Algebra (𝓞 K) Sₐ] [Algebra (𝓞 L) Sₐ]
    [Algebra Rₐ Sₐ] [IsScalarTower (𝓞 K) (𝓞 L) Sₐ]
    [IsScalarTower (𝓞 K) Rₐ Sₐ]
    [IsLocalization.Away a Rₐ]
    [IsLocalization.Away (algebraMap (𝓞 K) (𝓞 L) a) Sₐ] :
    Algebra.FormallyUnramified Rₐ Sₐ ↔
      ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 :=
  numberField_localizedIntegers_unramified_iff a Rₐ Sₐ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- Exact original-object consumer of `originalLocalizedIntegers_map_mem`. -/
theorem actual_canonical_localized_integer_maps_originalLocalizedIntegers_map_mem_source (a : 𝓞 K) (ha : a ≠ 0)
    (x : originalLocalizedIntegers K a ha) :
    algebraMap K L x.val ∈ originalLocalizedIntegers L
      (algebraMap (𝓞 K) (𝓞 L) a) (originalIntegerMap_ne_zero (L := L) a ha) :=
  originalLocalizedIntegers_map_mem a ha x

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- Exact original-object consumer of `canonicalLocalizedIntegerAlgebra_data`. -/
theorem actual_canonical_localized_integer_algebras_canonicalLocalizedIntegerAlgebra_data_source (a : 𝓞 K) (ha : a ≠ 0) :
    (let Rₐ := originalLocalizedIntegers K a ha
     let Sₐ := originalLocalizedIntegers L (algebraMap (𝓞 K) (𝓞 L) a)
       (originalIntegerMap_ne_zero (L := L) a ha)
     letI : Algebra Rₐ Sₐ := (originalLocalizedIntegersMap (L := L) a ha).toRingHom.toAlgebra
     Module.Finite Rₐ Sₐ ∧ IsIntegralClosure Sₐ Rₐ L ∧
       (Algebra.FormallyUnramified Rₐ Sₐ ↔
         ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
           (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1)) :=
  canonicalLocalizedIntegerAlgebra_data a ha

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {R A B Ω : Type*} [CommRing R] [CommRing A] [CommRing B] [Field Ω]
  [Algebra R A] [Algebra R B] [Algebra R Ω]
  [IsDedekindDomain R] [Module.Finite R A] [Module.Finite R B]
  [Algebra.FormallyUnramified R A] [Algebra.FormallyUnramified R B]
  {L M : Type*} [Field L] [Field M]
  [Algebra A L] [IsFractionRing A L] [Algebra B M] [IsFractionRing B M]

/-- Exact original-object consumer of `integralClosure_formallyUnramified_of_compositum_top`. -/
theorem actual_unramified_compositum_integral_closure_integralClosure_formallyUnramified_of_compositum_top_source
    (f : A →ₐ[R] Ω) (g : B →ₐ[R] Ω) (i : L →+* Ω) (j : M →+* Ω)
    (hi : i.comp (algebraMap A L) = f.toRingHom)
    (hj : j.comp (algebraMap B M) = g.toRingHom)
    (htop : i.fieldRange ⊔ j.fieldRange = ⊤)
    (C : Type*) [CommRing C] [Algebra R C] [Algebra C Ω]
    [IsScalarTower R C Ω] [IsIntegralClosure C R Ω] :
    Algebra.FormallyUnramified R C :=
  integralClosure_formallyUnramified_of_compositum_top f g i j hi hj htop C

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L M Ω : Type*} [Field K] [Field L] [Field M] [Field Ω]
  [NumberField K] [NumberField L] [NumberField M] [NumberField Ω]
  [Algebra K L] [Algebra K M] [Algebra K Ω] [Algebra L Ω] [Algebra M Ω]
  [IsScalarTower K L Ω] [IsScalarTower K M Ω]

/-- Exact original-object consumer of `numberField_unramified_compositum`. -/
theorem actual_number_field_unramified_compositum_numberField_unramified_compositum_source (a : 𝓞 K) (ha : a ≠ 0)
    (hL : ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1)
    (hM : ∀ w : HeightOneSpectrum (𝓞 M), algebraMap (𝓞 K) (𝓞 M) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1)
    (htop : (algebraMap L Ω).fieldRange ⊔ (algebraMap M Ω).fieldRange = ⊤) :
    ∀ w : HeightOneSpectrum (𝓞 Ω), algebraMap (𝓞 K) (𝓞 Ω) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 :=
  numberField_unramified_compositum a ha hL hM htop

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- Exact original-object consumer of `finiteIntermediateField_le_directed_stage`. -/
theorem actual_finite_subextension_directed_descent_finiteIntermediateField_le_directed_stage_source
    {ι : Type*} [Nonempty ι] (F : ι → IntermediateField K Ω)
    (hdir : Directed (· ≤ ·) F)
    (E : IntermediateField K Ω) [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (hE : E ≤ ⨆ i, F i) : ∃ i, E ≤ F i :=
  finiteIntermediateField_le_directed_stage F hdir E hE

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


/-- Exact original-object consumer of `heightOnePrimes_containing_nonzero_finite`. -/
theorem actual_finite_exceptional_integer_primes_heightOnePrimes_containing_nonzero_finite_source
    {R : Type*} [CommRing R] [IsDedekindDomain R] (a : R) (ha : a ≠ 0) :
    {v : HeightOneSpectrum R | a ∈ v.asIdeal}.Finite :=
  heightOnePrimes_containing_nonzero_finite a ha

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- Exact original-object consumer of `intermediateField_sup_inclusion_ranges`. -/
theorem actual_intermediate_field_sup_embeddings_intermediateField_sup_inclusion_ranges_source (E F : IntermediateField K Ω) :
    (IntermediateField.inclusion (show E ≤ E ⊔ F from le_sup_left)).toRingHom.fieldRange ⊔
      (IntermediateField.inclusion (show F ≤ E ⊔ F from le_sup_right)).toRingHom.fieldRange =
        ⊤ :=
  intermediateField_sup_inclusion_ranges E F

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Exact original-object consumer of `finiteGalois_sup_unramified`. -/
theorem actual_finite_galois_unramified_sup_finiteGalois_sup_unramified_source (a : 𝓞 K) (ha : a ≠ 0)
    (F G : FiniteGaloisIntermediateField K Ω)
    (hF : ∀ w : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1)
    (hG : ∀ w : HeightOneSpectrum (𝓞 G), algebraMap (𝓞 K) (𝓞 G) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1) :
    ∀ w : HeightOneSpectrum (𝓞 (F ⊔ G : FiniteGaloisIntermediateField K Ω)),
      algebraMap (𝓞 K) (𝓞 (F ⊔ G : FiniteGaloisIntermediateField K Ω)) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 :=
  finiteGalois_sup_unramified a ha F G hF hG

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Exact original-object consumer of `originalUnramifiedGaloisUnion_isGalois`. -/
theorem actual_unramified_galois_stage_union_originalUnramifiedGaloisUnion_isGalois_source (a : 𝓞 K) :
    IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  originalUnramifiedGaloisUnion_isGalois a

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- Exact original-object consumer of `originalUnramifiedGaloisStage_nonempty`. -/
theorem actual_unramified_galois_stage_nonempty_originalUnramifiedGaloisStage_nonempty_source (a : 𝓞 K) :
    Nonempty (OriginalUnramifiedGaloisStage (Ω := Ω) a) :=
  originalUnramifiedGaloisStage_nonempty a

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Exact original-object consumer of `originalUnramifiedUnion_finite_subextension_embeds_stage`. -/
theorem actual_unramified_union_finite_stage_originalUnramifiedUnion_finite_subextension_embeds_stage_source
    (a : 𝓞 K) (ha : a ≠ 0)
    (E : IntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    [FiniteDimensional K E] :
    ∃ (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : E →ₐ[K] F.val),
      ∀ x : E, (i x : Ω) = (x.val : Ω) :=
  originalUnramifiedUnion_finite_subextension_embeds_stage a ha E

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Exact original-object consumer of `originalUnramifiedUnion_finiteGalois_unramified`. -/
theorem actual_unramified_union_finite_ramification_originalUnramifiedUnion_finiteGalois_unramified_source
    (a : 𝓞 K) (ha : a ≠ 0)
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (v : HeightOneSpectrum (𝓞 K)) (hv : a ∉ v.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
      v.asIdeal.ramificationIdx w.asIdeal = 1 :=
  originalUnramifiedUnion_finiteGalois_unramified a ha F v hv

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Exact original-object consumer of `originalUnramifiedUnion_prime_characters_finite`. -/
theorem actual_unramified_union_prime_characters_originalUnramifiedUnion_prime_characters_finite_source
    (a : 𝓞 K) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Finite (Gal((originalUnramifiedGaloisUnion (Ω := Ω) a)/K) →ₜ*
      Multiplicative (ZMod p)) :=
  originalUnramifiedUnion_prime_characters_finite a ha p hp hζ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {F : Type*} [Field F] [NumberField F]

/-- Exact original-object consumer of `rationalCyclotomic_originalBase_ramificationIdx_one`. -/
theorem actual_rational_cyclotomic_ramification_rationalCyclotomic_originalBase_ramificationIdx_one_source
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} ℚ F]
    (w : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ w.asIdeal) :
    (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1 :=
  rationalCyclotomic_originalBase_ramificationIdx_one m w hm

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {Ω : Type*} [Field Ω] [CharZero Ω] [Algebra ℚ Ω]

/-- Exact original-object consumer of `originalQUnramifiedUnion_exists_primitiveRoot`. -/
theorem actual_unramified_union_cyclotomic_roots_originalQUnramifiedUnion_exists_primitiveRoot_source [IsSepClosed Ω]
    (a : 𝓞 ℚ) (m : ℕ) [NeZero m] (hma : (m : 𝓞 ℚ) ∣ a) :
    ∃ ζ : originalUnramifiedGaloisUnion (Ω := Ω) a, IsPrimitiveRoot ζ m :=
  originalQUnramifiedUnion_exists_primitiveRoot a m hma

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]
  [IsGalois K Ω]

/-- Exact original-object consumer of `unramified_prime_characters_finite_of_ambient_root`. -/
theorem actual_unramified_cyclotomic_character_descent_unramified_prime_characters_finite_of_ambient_root_source
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (hunram : ∀ F : FiniteGaloisIntermediateField K Ω,
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
          v.asIdeal.ramificationIdx w.asIdeal = 1)
    (p : ℕ) (hp : p.Prime) {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) :
    Finite (Gal(Ω/K) →ₜ* Multiplicative (ZMod p)) :=
  unramified_prime_characters_finite_of_ambient_root S hS hunram p hp hζ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {Ω : Type*} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]

/-- Exact original-object consumer of `originalQUnramifiedUnion_finiteBase_prime_characters_finite`. -/
theorem actual_unramified_union_finite_base_characters_originalQUnramifiedUnion_finiteBase_prime_characters_finite_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a) :
    (let U := originalUnramifiedGaloisUnion (Ω := Ω) a
     letI : Algebra ℚ U := U.algebra'
     ∀ E : IntermediateField ℚ U,
       letI : Algebra ℚ E := E.algebra'
       ∀ [FiniteDimensional ℚ E], Finite (Gal(U/E) →ₜ* Multiplicative (ZMod p))) :=
  originalQUnramifiedUnion_finiteBase_prime_characters_finite a ha p hp hpa

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {Ω : Type*} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]

/-- Exact original-object consumer of `originalQUnramifiedUnion_openSubgroup_prime_characters_finite`. -/
theorem actual_unramified_union_open_subgroup_characters_originalQUnramifiedUnion_openSubgroup_prime_characters_finite_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a) :
    (let U := originalUnramifiedGaloisUnion (Ω := Ω) a
     letI : Algebra ℚ U := U.algebra'
     ∀ H : OpenSubgroup Gal(U/ℚ), Finite (H →ₜ* Multiplicative (ZMod p))) :=
  originalQUnramifiedUnion_openSubgroup_prime_characters_finite a ha p hp hpa

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {Ω ι R : Type*} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
  [Fintype ι] [DecidableEq ι] [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

/-- Exact original-object consumer of `originalArithmeticMatrixKernel_prime_characters_finite`. -/
theorem actual_arithmetic_residual_kernel_characters_originalArithmeticMatrixKernel_prime_characters_finite_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a) :
    (let U := originalUnramifiedGaloisUnion (Ω := Ω) a
     letI : Algebra ℚ U := U.algebra'
     ∀ (ρ : Gal(U/ℚ) →* GeneralLinearGroup ι R), Continuous ρ →
       Finite (ρ.ker →ₜ* Multiplicative (ZMod p))) :=
  originalArithmeticMatrixKernel_prime_characters_finite a ha p hp hpa

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Exact original-object consumer of `originalUnramifiedUnion_finiteGalois_le_iff`. -/
theorem actual_unramified_union_finite_field_criterion_originalUnramifiedUnion_finiteGalois_le_iff_source
    (a : 𝓞 K) (ha : a ≠ 0) (F : FiniteGaloisIntermediateField K Ω) :
    F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ↔
      ∀ w : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 :=
  originalUnramifiedUnion_finiteGalois_le_iff a ha F

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors




/-- Exact original-object consumer of `rationalArithmeticGaloisGroup_openSubgroup_prime_characters_finite`. -/
theorem actual_rational_arithmetic_galois_group_rationalArithmeticGaloisGroup_openSubgroup_prime_characters_finite_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (H : OpenSubgroup (rationalArithmeticGaloisGroup a)) :
    Finite (H →ₜ* Multiplicative (ZMod p)) :=
  rationalArithmeticGaloisGroup_openSubgroup_prime_characters_finite a ha p hp hpa H

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [DiscreteTopology R]

/-- Exact original-object consumer of `rationalArithmeticResidual_has_profinite_presentation`. -/
theorem actual_arithmetic_residual_profinite_presentation_rationalArithmeticResidual_has_profinite_presentation_source
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) :
    (let hK := ρ.ker.isClosed_of_isOpen (continuousMatrixRepresentation_isOpen_ker ρ hρ)
     ∃ S : Finset (fixedResidualProfiniteQuotient p (rationalArithmeticGaloisGroup a) ρ.ker hK),
       Function.Surjective (profiniteGeneratorPresentation
         (fixedResidualProfiniteQuotient p (rationalArithmeticGaloisGroup a) ρ.ker hK) S)) :=
  rationalArithmeticResidual_has_profinite_presentation a ha p hp hpa ρ hρ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

variable [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `originalFramedFiberFixedQuotientEquiv_mk`. -/
theorem actual_original_residual_framed_fibers_originalFramedFiberFixedQuotientEquiv_mk_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (f : OriginalContinuousFramedFiber e H σ) (h : H) :
    (originalFramedFiberFixedQuotientEquiv hA e p hp H σ hσ f).val
      (QuotientGroup.mk' (fixedResidualProPKernel p H σ.ker
        (originalResidualMatrixKernel_isClosed H σ hσ)) h) = f.val h :=
  originalFramedFiberFixedQuotientEquiv_mk hA e p hp H σ hσ f h

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors


variable {O A : Type*} [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- Exact original-object consumer of `localCoefficientReduction_continuous`. -/
theorem actual_local_coefficient_reduction_topology_localCoefficientReduction_continuous_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :
    Continuous (localCoefficientReduction e) :=
  localCoefficientReduction_continuous hA e

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

omit [Group.FG G] [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Exact original-object consumer of `presentedFramedResidual_iff_whole`. -/
theorem actual_original_presented_framed_fibers_presentedFramedResidual_iff_whole_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (f : H →ₜ* GeneralLinearGroup ι A) :
    (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction (f.comp q)) =
        (σ.toMonoidHom.comp q.toMonoidHom).comp
          (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom ↔
    (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      f.toMonoidHom = σ.toMonoidHom :=
  presentedFramedResidual_iff_whole hA e H q hq σ f

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G ι O : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `originalPresentedCoefficientRing_localData`. -/
theorem actual_original_presented_coefficient_ring_originalPresentedCoefficientRing_localData_source
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (letI := originalPresentedCoefficientRing_isLocal H q σ
     IsNoetherianRing (OriginalPresentedCoefficientRing H q σ) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (OriginalPresentedCoefficientRing H q σ))
         (OriginalPresentedCoefficientRing H q σ) ∧
       (inferInstance : TopologicalSpace (OriginalPresentedCoefficientRing H q σ)) =
         (IsLocalRing.maximalIdeal (OriginalPresentedCoefficientRing H q σ)).adicTopology ∧
       ∀ r : ResidualRepresentationCompletion (originalPresentedResidualRestriction H q σ),
         localCoefficientReduction (completedPresentationResidueEquiv
           (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker)
           (Ideal.Quotient.mk (completedPresentationRelationIdeal
             (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker) r) =
               completedResidualRepresentationEvaluation (originalPresentedResidualRestriction H q σ) r) :=
  originalPresentedCoefficientRing_localData H q σ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Exact original-object consumer of `originalPresentedFramedFiberEquiv_evaluation`. -/
theorem actual_original_coefficient_framed_equivalence_originalPresentedFramedFiberEquiv_evaluation_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (letI := originalPresentedCoefficientRing_isLocal H q σ
     ∀ (f : OriginalContinuousCoefficientFiber (completedPresentationResidueEquiv
       (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker) eA) (h : H),
       (originalPresentedFramedFiberEquiv hA eA H q hq σ f).val h =
         GeneralLinearGroup.map (n := ι) f.val.toRingHom
           (completedPresentationRepresentation
             (originalPresentedResidualRestriction H q σ) H q hq h)) :=
  originalPresentedFramedFiberEquiv_evaluation hA eA H q hq σ

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {O A B : Type u} [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A]
  [CommRing B] [IsLocalRing B] [Algebra O B]

variable {G ι : Type u} [Group G] [Group.FG G] [Fintype ι] [DecidableEq ι]
  [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [WithIdeal A] [WithIdeal B]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- Exact original-object consumer of `originalPresentedFramedFiberEquiv_natural`. -/
theorem actual_original_framed_fiber_naturality_originalPresentedFramedFiberEquiv_natural_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    (letI := originalPresentedCoefficientRing_isLocal H q σ
     ∀ f : OriginalContinuousCoefficientFiber (completedPresentationResidueEquiv
       (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker) eA,
       originalPresentedFramedFiberEquiv hB eB H q hq σ
         (originalCoefficientFiberPostcomp _ eA eB k hk hres f) =
           originalFramedFiberPostcomp eA eB H σ.toMonoidHom k hk hres
             (originalPresentedFramedFiberEquiv hA eA H q hq σ f)) :=
  originalPresentedFramedFiberEquiv_natural hA hB eA eB H q hq σ k hk hres

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]

/-- Exact original-object consumer of `fixedResidualFramedCoefficientRing_localData`. -/
theorem actual_fixed_residual_framed_coefficient_ring_fixedResidualFramedCoefficientRing_localData_source
    (p : ℕ) (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ)) :
    (letI := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
     IsNoetherianRing (FixedResidualFramedCoefficientRing p H σ hσ S) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (FixedResidualFramedCoefficientRing p H σ hσ S))
         (FixedResidualFramedCoefficientRing p H σ hσ S) ∧
       (inferInstance : TopologicalSpace (FixedResidualFramedCoefficientRing p H σ hσ S)) =
         (IsLocalRing.maximalIdeal (FixedResidualFramedCoefficientRing p H σ hσ S)).adicTopology) :=
  fixedResidualFramedCoefficientRing_localData p H σ hσ S

end


section

open IsDedekindDomain Matrix Module
open scoped TensorProduct NumberField nonZeroDivisors

universe u

variable {ι O : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

variable {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- Exact original-object consumer of `fixedResidualFramedFiberEquiv_natural`. -/
theorem actual_fixed_residual_framed_universality_fixedResidualFramedFiberEquiv_natural_source
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S))
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    (letI := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
     ∀ f : OriginalContinuousCoefficientFiber
       (fixedResidualFramedCoefficientResidueEquiv p H σ hσ S) eA,
       fixedResidualFramedFiberEquiv hB eB p hp H σ hσ S hS
         (originalCoefficientFiberPostcomp _ eA eB k hk hres f) =
           originalFramedFiberPostcomp eA eB H σ k hk hres
             (fixedResidualFramedFiberEquiv hA eA p hp H σ hσ S hS f)) :=
  fixedResidualFramedFiberEquiv_natural hA hB eA eB p hp H σ hσ S hS k hk hres

end


end Dubon2026.SemanticRegression
