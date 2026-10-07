import Dubon2026.AlmostAnalyticPolynomialDegree

/-! # Almost-everywhere analytic coefficients of actual polynomial division -/

namespace Dubon2026

open Filter Set MeasureTheory Polynomial
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

theorem ae_polynomial_div_coeff_analytic (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {P Q : V → ℝ[X]} {s : Set V} {d e : ℕ}
    (hd : ∀ y, (P y).natDegree ≤ d) (he : ∀ y, (Q y).natDegree ≤ e)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y)
    (hQ : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (Q z).coeff k) y) (k : ℕ) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z / Q z).coeff k) y := by
  let R : V → ℝ[X] := fun y => Q y * C (Q y).leadingCoeff⁻¹
  have hL := ae_polynomial_leadingCoeff_analytic μ he hQ
  have hR : ∀ j, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (R z).coeff j) y := by
    intro j
    have hj := ae_analyticAt_div μ (hQ j) hL
    simpa only [R, Polynomial.coeff_mul_C, div_eq_mul_inv] using hj
  have hRd : ∀ y, (R y).natDegree ≤ e := by
    intro y
    exact (Polynomial.natDegree_mul_le (p := Q y) (q := C (Q y).leadingCoeff⁻¹)).trans
      (by simpa using he y)
  have hPa : ∀ᵐ y ∂μ.restrict s, ∀ j, AnalyticAt ℝ (fun z => (P z).coeff j) y :=
    ae_all_iff.mpr hP
  have hRa : ∀ᵐ y ∂μ.restrict s, ∀ j, AnalyticAt ℝ (fun z => (R z).coeff j) y :=
    ae_all_iff.mpr hR
  filter_upwards [hPa, hRa, hL, ae_polynomial_natDegree_locally_constant μ hRd hR,
    ae_polynomial_zero_test_locally_constant μ he hQ] with y hPy hRy hLy hdeg hzero
  by_cases hy : Q y = 0
  · apply (show AnalyticAt ℝ (fun _ : V => (0 : ℝ)) y from analyticAt_const).congr
    filter_upwards [hzero] with z hz
    simp only [hz.mpr hy, EuclideanDomain.div_zero, Polynomial.coeff_zero]
  · have hnear : ∀ᶠ z in 𝓝 y,
        (P z).natDegree < d + 1 ∧ (R z).Monic ∧ (R z).natDegree = (R y).natDegree := by
      filter_upwards [hdeg, hzero] with z hdz hzz
      exact ⟨Nat.lt_succ_of_le (hd z),
        Polynomial.monic_mul_leadingCoeff_inv (fun hz => hy (hzz.mp hz)), hdz⟩
    have hdiv := analyticAt_monic_division_coeff hPy hRy hnear k
    have hli := hLy.inv (Polynomial.leadingCoeff_ne_zero.mpr hy)
    simpa only [Polynomial.div_def, Polynomial.coeff_C_mul, R] using hli.mul hdiv

end Dubon2026
