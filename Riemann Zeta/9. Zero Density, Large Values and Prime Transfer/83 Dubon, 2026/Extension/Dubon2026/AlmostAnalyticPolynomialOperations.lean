import Dubon2026.AlmostAnalyticPolynomialDivision

/-! # Analytic coefficient operations used in the Euclidean procedure -/

namespace Dubon2026

open Filter Set MeasureTheory Polynomial
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V]

theorem ae_polynomial_mul_coeff_analytic (μ : Measure V) {P Q : V → ℝ[X]} {s : Set V}
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y)
    (hQ : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (Q z).coeff k) y) (k : ℕ) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z * Q z).coeff k) y := by
  have hPa : ∀ᵐ y ∂μ.restrict s, ∀ j, AnalyticAt ℝ (fun z => (P z).coeff j) y :=
    ae_all_iff.mpr hP
  have hQa : ∀ᵐ y ∂μ.restrict s, ∀ j, AnalyticAt ℝ (fun z => (Q z).coeff j) y :=
    ae_all_iff.mpr hQ
  filter_upwards [hPa, hQa] with y hy hqy
  simp only [Polynomial.coeff_mul]
  apply Finset.analyticAt_fun_sum
  intro ij _
  exact (hy ij.1).mul (hqy ij.2)

theorem ae_polynomial_sub_coeff_analytic (μ : Measure V) {P Q : V → ℝ[X]} {s : Set V}
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y)
    (hQ : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (Q z).coeff k) y) (k : ℕ) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z - Q z).coeff k) y := by
  filter_upwards [hP k, hQ k] with y hy hqy
  simpa only [Polynomial.coeff_sub] using hy.sub hqy

theorem ae_polynomial_derivative_coeff_analytic (μ : Measure V) {P : V → ℝ[X]} {s : Set V}
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) (k : ℕ) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).derivative.coeff k) y := by
  filter_upwards [hP (k + 1)] with y hy
  simpa only [Polynomial.coeff_derivative] using hy.mul (analyticAt_const (v := (k + 1 : ℝ)))

variable [BorelSpace V] [FiniteDimensional ℝ V]

theorem ae_polynomial_mod_coeff_analytic (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {P Q : V → ℝ[X]} {s : Set V} {d e : ℕ}
    (hd : ∀ y, (P y).natDegree ≤ d) (he : ∀ y, (Q y).natDegree ≤ e)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y)
    (hQ : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (Q z).coeff k) y) (k : ℕ) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z % Q z).coeff k) y := by
  have hdiv := ae_polynomial_div_coeff_analytic μ hd he hP hQ
  have hmul := ae_polynomial_mul_coeff_analytic μ hQ hdiv
  simpa only [EuclideanDomain.mod_eq_sub_mul_div] using
    ae_polynomial_sub_coeff_analytic μ hP hmul k

theorem polynomial_normalize_eq_mul_inv_leadingCoeff (P : ℝ[X]) :
    normalize P = P * C P.leadingCoeff⁻¹ := by
  by_cases hp : P = 0
  · simp only [hp, normalize_zero, zero_mul]
  · rw [normalize_apply, Polynomial.coe_normUnit_of_ne_zero hp]

theorem ae_polynomial_normalize_coeff_analytic (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {P : V → ℝ[X]} {s : Set V} {d : ℕ} (hd : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) (k : ℕ) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (normalize (P z)).coeff k) y := by
  have hL := ae_polynomial_leadingCoeff_analytic μ hd hP
  simpa only [polynomial_normalize_eq_mul_inv_leadingCoeff, Polynomial.coeff_mul_C,
    div_eq_mul_inv] using ae_analyticAt_div μ (hP k) hL

theorem polynomial_natDegree_mod_le_left (P Q : ℝ[X]) : (P % Q).natDegree ≤ P.natDegree := by
  apply Polynomial.natDegree_le_natDegree
  rw [Polynomial.mod_def]
  exact Polynomial.degree_modByMonic_le_left

theorem polynomial_gcd_eq_normalize_euclidean (P Q : ℝ[X]) :
    gcd P Q = normalize (EuclideanDomain.gcd P Q) := by
  apply gcd_eq_normalize
  · exact EuclideanDomain.dvd_gcd (gcd_dvd_left P Q) (gcd_dvd_right P Q)
  · exact dvd_gcd (EuclideanDomain.gcd_dvd_left P Q) (EuclideanDomain.gcd_dvd_right P Q)

end Dubon2026
