import Dubon2026.AlmostAnalyticSturmSigns

/-! # Almost-everywhere local constancy of multiplicity-weighted real root counts -/

namespace Dubon2026

open Filter Set MeasureTheory Polynomial
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

theorem ae_sturmOpenCount_locally_constant (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {P : V → ℝ[X]} {s : Set V} {d : ℕ} (hdP : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) (l u : ℝ) :
    ∀ᵐ y ∂μ.restrict s, ∀ᶠ z in 𝓝 y, sturmOpenCount (P z) l u = sturmOpenCount (P y) l u := by
  have hD := ae_polynomial_derivative_coeff_analytic μ hP
  have hdD : ∀ y, (P y).derivative.natDegree ≤ d := fun y =>
    ((Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)).trans (hdP y)
  filter_upwards [ae_sturmVar_locally_constant μ hdP hP l,
    ae_sturmVar_locally_constant μ hdP hP u,
    ae_polynomial_zero_test_locally_constant μ hdD hD,
    ae_analytic_sign_locally_constant μ (ae_polynomial_eval_analytic μ hdP hP u)]
    with y hly huy hdy hsy
  filter_upwards [hly, huy, hdy, hsy] with z hlz huz hdz hsz
  have he : (P z).eval u = 0 ↔ (P y).eval u = 0 := by
    rw [← sign_eq_zero_iff (a := (P z).eval u), ← sign_eq_zero_iff (a := (P y).eval u), hsz]
  simp only [sturmOpenCount, hdz, hlz, huz, he]

theorem ae_sturmMultiplicityCount_locally_constant (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {P : V → ℝ[X]} {s : Set V} {d : ℕ} (hdP : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) (l u : ℝ) :
    ∀ᵐ y ∂μ.restrict s, ∀ᶠ z in 𝓝 y,
      sturmMultiplicityCount (P z) l u = sturmMultiplicityCount (P y) l u := by
  have hlayers : ∀ᵐ y ∂μ.restrict s, ∀ n, ∀ᶠ z in 𝓝 y,
      sturmOpenCount (derivativeRootQuotient (derivativeGcdLayer (P z) n)) l u =
        sturmOpenCount (derivativeRootQuotient (derivativeGcdLayer (P y) n)) l u := by
    apply ae_all_iff.mpr
    intro n
    have hdn : ∀ y, (derivativeGcdLayer (P y) n).natDegree ≤ d :=
      fun y => (derivativeGcdLayer_natDegree_le (P y) n).trans (hdP y)
    have hqn : ∀ y, (derivativeRootQuotient (derivativeGcdLayer (P y) n)).natDegree ≤ d :=
      fun y => (derivativeRootQuotient_natDegree_le _).trans (hdn y)
    exact ae_sturmOpenCount_locally_constant μ hqn
      (ae_derivativeRootQuotient_coeff_analytic μ hdn
        (ae_derivativeGcdLayer_coeff_analytic μ n hdP hP)) l u
  filter_upwards [hlayers, ae_polynomial_natDegree_locally_constant μ hdP hP] with y hy hdy
  have hall : ∀ᶠ z in 𝓝 y, ∀ n ∈ Finset.range (P y).natDegree,
      sturmOpenCount (derivativeRootQuotient (derivativeGcdLayer (P z) n)) l u =
        sturmOpenCount (derivativeRootQuotient (derivativeGcdLayer (P y) n)) l u :=
    (Finset.range (P y).natDegree).eventually_all.mpr (fun n _ => hy n)
  filter_upwards [hall, hdy] with z hz hdz
  simp only [sturmMultiplicityCount, hdz]
  exact Finset.sum_congr rfl hz

theorem sturmMultiplicityCount_eq_root_count_all (P : ℝ[X]) (l u : ℝ) :
    sturmMultiplicityCount P l u = realPolynomialRootCount P l u := by
  by_cases hp : P = 0
  · simp only [hp, sturmMultiplicityCount, Polynomial.natDegree_zero, Finset.range_zero,
      Finset.sum_empty, realPolynomialRootCount, Polynomial.roots_zero, Multiset.filter_zero,
      Multiset.card_zero]
  · exact sturmMultiplicityCount_eq_root_count hp l u

/-- The actual algebraic root count, with multiplicity, is locally constant almost everywhere. -/
theorem ae_realPolynomialRootCount_locally_constant (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {P : V → ℝ[X]} {s : Set V} {d : ℕ} (hdP : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) (l u : ℝ) :
    ∀ᵐ y ∂μ.restrict s, ∀ᶠ z in 𝓝 y,
      realPolynomialRootCount (P z) l u = realPolynomialRootCount (P y) l u := by
  simpa only [sturmMultiplicityCount_eq_root_count_all] using
    ae_sturmMultiplicityCount_locally_constant μ hdP hP l u

/-- Coefficient analyticity at one parameter yields a neighborhood with generic root-count constancy. -/
theorem analytic_polynomial_root_count_locally_ae_constant (μ : Measure V)
    [Measure.IsAddHaarMeasure μ] {P : V → ℝ[X]} {x : V} {d : ℕ}
    (hdP : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, AnalyticAt ℝ (fun z => (P z).coeff k) x) (l u : ℝ) :
    ∃ r > 0, ∀ᵐ y ∂μ.restrict (Metric.ball x r), ∀ᶠ z in 𝓝 y,
      realPolynomialRootCount (P z) l u = realPolynomialRootCount (P y) l u := by
  have he : ∀ᶠ y in 𝓝 x, ∀ j : Fin (d + 1), AnalyticAt ℝ (fun z => (P z).coeff j.val) y :=
    Filter.eventually_all.mpr (fun j => (hP j.val).eventually_analyticAt)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r, hr, ae_realPolynomialRootCount_locally_constant μ hdP ?_ l u⟩
  intro k
  by_cases hk : k ≤ d
  · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hball hy ⟨k, Nat.lt_succ_of_le hk⟩
  · have hzero : (fun z => (P z).coeff k) = (fun _ => (0 : ℝ)) := by
      funext z
      exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hdP z).trans_lt (lt_of_not_ge hk))
    rw [hzero]
    exact Filter.Eventually.of_forall (fun _ => analyticAt_const)

end Dubon2026
