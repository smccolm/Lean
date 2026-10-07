import Dubon2026.UniversalMonicDivision

/-! # Generic local constancy of polynomial degrees -/

namespace Dubon2026

open Filter Set MeasureTheory Polynomial
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

theorem ae_polynomial_natDegree_locally_constant (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {P : V → ℝ[X]} {s : Set V} {d : ℕ} (hd : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) :
    ∀ᵐ y ∂μ.restrict s, ∀ᶠ z in 𝓝 y, (P z).natDegree = (P y).natDegree := by
  have hs : ∀ᵐ y ∂μ.restrict s, ∀ j : Fin (d + 1),
      ∀ᶠ z in 𝓝 y, SignType.sign ((P z).coeff j.val) = SignType.sign ((P y).coeff j.val) :=
    ae_all_iff.mpr (fun j => ae_analytic_sign_locally_constant μ (hP j.val))
  filter_upwards [hs] with y hy
  have hall : ∀ᶠ z in 𝓝 y, ∀ j : Fin (d + 1),
      SignType.sign ((P z).coeff j.val) = SignType.sign ((P y).coeff j.val) :=
    Filter.eventually_all.mpr hy
  filter_upwards [hall] with z hz
  apply Polynomial.natDegree_eq_of_degree_eq
  have he : (P z).support = (P y).support := by
    ext k
    simp only [Polynomial.mem_support_iff]
    by_cases hk : k ≤ d
    · apply not_congr
      rw [← sign_eq_zero_iff (a := (P z).coeff k),
        ← sign_eq_zero_iff (a := (P y).coeff k), hz ⟨k, Nat.lt_succ_of_le hk⟩]
    · have hk' : d < k := lt_of_not_ge hk
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hd z).trans_lt hk'),
        Polynomial.coeff_eq_zero_of_natDegree_lt ((hd y).trans_lt hk')]
  unfold Polynomial.degree
  rw [he]

theorem ae_polynomial_leadingCoeff_analytic (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {P : V → ℝ[X]} {s : Set V} {d : ℕ} (hd : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).leadingCoeff) y :=
  ae_analyticAt_nat_index μ hP (ae_polynomial_natDegree_locally_constant μ hd hP)

theorem ae_polynomial_zero_test_locally_constant (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {P : V → ℝ[X]} {s : Set V} {d : ℕ} (hd : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) :
    ∀ᵐ y ∂μ.restrict s, ∀ᶠ z in 𝓝 y, P z = 0 ↔ P y = 0 := by
  have hs := ae_analytic_sign_locally_constant μ (ae_polynomial_leadingCoeff_analytic μ hd hP)
  filter_upwards [hs] with y hy
  filter_upwards [hy] with z hz
  rw [← Polynomial.leadingCoeff_eq_zero, ← Polynomial.leadingCoeff_eq_zero,
    ← sign_eq_zero_iff (a := (P z).leadingCoeff),
    ← sign_eq_zero_iff (a := (P y).leadingCoeff), hz]

end Dubon2026
