import Dubon2026.BoundedEuclideanGcd

/-! # Almost-everywhere analyticity of the actual polynomial GCD coefficients -/

namespace Dubon2026

open Filter Set MeasureTheory Polynomial
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

theorem ae_boundedEuclideanGcd_coeff_analytic (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    (n : ℕ) {P Q : V → ℝ[X]} {s : Set V} {d : ℕ}
    (hdP : ∀ y, (P y).natDegree ≤ d) (hdQ : ∀ y, (Q y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y)
    (hQ : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (Q z).coeff k) y) (k : ℕ) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (boundedEuclideanGcd (P z) (Q z) n).coeff k) y := by
  induction n generalizing P Q with
  | zero => exact hQ k
  | succ n ih =>
    have hm := ae_polynomial_mod_coeff_analytic μ hdQ hdP hQ hP
    have hmd : ∀ y, (Q y % P y).natDegree ≤ d :=
      fun y => (polynomial_natDegree_mod_le_left (Q y) (P y)).trans (hdQ y)
    have hr := ih hmd hdP hm hP
    filter_upwards [hP k, hQ k, hr, ae_polynomial_natDegree_locally_constant μ hdP hP,
      ae_polynomial_zero_test_locally_constant μ hdP hP] with y hPy hQy hry hdeg hzero
    by_cases hp : P y = 0
    · apply hQy.congr
      filter_upwards [hzero] with z hz
      simp only [boundedEuclideanGcd, if_pos (hz.mpr hp)]
    · by_cases hd : (P y).natDegree = 0
      · apply hPy.congr
        filter_upwards [hzero, hdeg] with z hz hdz
        simp only [boundedEuclideanGcd, if_neg (fun he => hp (hz.mp he)), hdz, if_pos hd]
      · apply hry.congr
        filter_upwards [hzero, hdeg] with z hz hdz
        simp only [boundedEuclideanGcd, if_neg (fun he => hp (hz.mp he)), hdz, if_neg hd]

theorem ae_polynomial_gcd_coeff_analytic (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {P Q : V → ℝ[X]} {s : Set V} {d : ℕ}
    (hdP : ∀ y, (P y).natDegree ≤ d) (hdQ : ∀ y, (Q y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y)
    (hQ : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (Q z).coeff k) y) (k : ℕ) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (gcd (P z) (Q z)).coeff k) y := by
  have hg := ae_boundedEuclideanGcd_coeff_analytic μ (d + 1) hdP hdQ hP hQ
  have hgd : ∀ y, (boundedEuclideanGcd (P y) (Q y) (d + 1)).natDegree ≤ d :=
    fun y => boundedEuclideanGcd_natDegree_le _ (hdP y) (hdQ y)
  have hn := ae_polynomial_normalize_coeff_analytic μ hgd hg k
  have heq : (fun z => (gcd (P z) (Q z)).coeff k) =
      (fun z => (normalize (boundedEuclideanGcd (P z) (Q z) (d + 1))).coeff k) := by
    funext z
    rw [polynomial_gcd_eq_normalize_bounded (hdP z)]
  rw [heq]
  exact hn

end Dubon2026
