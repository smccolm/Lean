import Dubon2026.AlmostAnalyticGcd

/-! # Analytic coefficients of the repeated-root layers and squarefree quotients -/

namespace Dubon2026

open Filter Set MeasureTheory Polynomial
open scoped Topology

theorem polynomial_gcd_natDegree_le {P Q : ℝ[X]} {d : ℕ}
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d) : (gcd P Q).natDegree ≤ d := by
  rw [polynomial_gcd_eq_normalize_bounded hP]
  have he := Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_normalize (p := boundedEuclideanGcd P Q (d + 1)))
  rw [he]
  exact boundedEuclideanGcd_natDegree_le _ hP hQ

theorem derivativeGcdLayer_natDegree_le (P : ℝ[X]) (n : ℕ) :
    (derivativeGcdLayer P n).natDegree ≤ P.natDegree := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    apply polynomial_gcd_natDegree_le ih
    exact ((Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)).trans ih

theorem derivativeRootQuotient_natDegree_le (P : ℝ[X]) :
    (derivativeRootQuotient P).natDegree ≤ P.natDegree :=
  Polynomial.natDegree_le_natDegree (Polynomial.degree_div_le P _)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

theorem ae_derivativeGcdLayer_coeff_analytic (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    (n : ℕ) {P : V → ℝ[X]} {s : Set V} {d : ℕ}
    (hd : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) (k : ℕ) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (derivativeGcdLayer (P z) n).coeff k) y := by
  induction n generalizing k with
  | zero => exact hP k
  | succ n ih =>
    have hdn : ∀ y, (derivativeGcdLayer (P y) n).natDegree ≤ d :=
      fun y => (derivativeGcdLayer_natDegree_le (P y) n).trans (hd y)
    have hdd : ∀ y, (derivativeGcdLayer (P y) n).derivative.natDegree ≤ d := fun y =>
      ((Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)).trans (hdn y)
    exact ae_polynomial_gcd_coeff_analytic μ hdn hdd ih
      (ae_polynomial_derivative_coeff_analytic μ ih) k

theorem ae_derivativeRootQuotient_coeff_analytic (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {P : V → ℝ[X]} {s : Set V} {d : ℕ}
    (hd : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) (k : ℕ) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (derivativeRootQuotient (P z)).coeff k) y := by
  have hdd : ∀ y, (P y).derivative.natDegree ≤ d := fun y =>
    ((Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)).trans (hd y)
  have hg := ae_polynomial_gcd_coeff_analytic μ hd hdd hP
    (ae_polynomial_derivative_coeff_analytic μ hP)
  have hgd : ∀ y, (gcd (P y) (P y).derivative).natDegree ≤ d :=
    fun y => polynomial_gcd_natDegree_le (hd y) (hdd y)
  exact ae_polynomial_div_coeff_analytic μ hd hgd hP hg k

omit [BorelSpace V] [FiniteDimensional ℝ V] in
theorem ae_polynomial_eval_analytic (μ : Measure V) {P : V → ℝ[X]} {s : Set V} {d : ℕ}
    (hd : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) (t : ℝ) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).eval t) y := by
  have hall : ∀ᵐ y ∂μ.restrict s, ∀ k, AnalyticAt ℝ (fun z => (P z).coeff k) y :=
    ae_all_iff.mpr hP
  filter_upwards [hall] with y hy
  have ha : AnalyticAt ℝ (fun z => ∑ k ∈ Finset.range (d + 1), (P z).coeff k * t ^ k) y := by
    apply Finset.analyticAt_fun_sum
    intro k _
    exact (hy k).mul analyticAt_const
  apply ha.congr
  apply Filter.Eventually.of_forall
  intro z
  have he := congrArg (Polynomial.eval t)
    ((P z).as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le (hd z)))
  simpa only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] using he.symm

end Dubon2026
