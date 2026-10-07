import Dubon2026.ZeroPolynomialNewton

/-! # Local constant degree and analytic coefficients of the actual phase zero polynomial -/

namespace Dubon2026

open Filter Complex Polynomial
open scoped Topology

noncomputable section

/-- The actual monic zero polynomial for complex phase parameters. -/
def complexPhaseZeroPolynomial (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T : ℝ) (x : PrimeCoordinate N → ℂ) : ℂ[X] :=
  rectangleZeroPolynomial (complexPhaseCoefficients a N x) N hN
    (by rwa [complexPhaseCoefficients_one]) l u T

theorem eventually_eq_complexPhaseZero_count {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : PrimeCoordinate N → ℂ)
    {l u T : ℝ} (hlu : l ≤ u) (hT : 0 ≤ T)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      complexPhaseFamily a N (x, s) ≠ 0) :
    ∀ᶠ y in 𝓝 x,
      verticalZeroCount (complexPhaseCoefficients a N y) N hN
        (by rwa [complexPhaseCoefficients_one]) l u T =
      verticalZeroCount (complexPhaseCoefficients a N x) N hN
        (by rwa [complexPhaseCoefficients_one]) l u T := by
  have hc := (analyticAt_complexPhaseZeroPowerSum hN ha x hlu hT hn 0).continuousAt
  have hd := Metric.tendsto_nhds.mp hc 1 zero_lt_one
  filter_upwards [hd] with y hy
  rw [complexPhaseZeroPowerSum_zero, complexPhaseZeroPowerSum_zero, dist_eq_norm] at hy
  have hr := (abs_re_le_norm _).trans_lt hy
  simp only [Complex.sub_re, Complex.natCast_re] at hr
  have hi : |(verticalZeroCount (complexPhaseCoefficients a N y) N hN
      (by rwa [complexPhaseCoefficients_one]) l u T : ℤ) -
    (verticalZeroCount (complexPhaseCoefficients a N x) N hN
      (by rwa [complexPhaseCoefficients_one]) l u T : ℤ)| < 1 := by exact_mod_cast hr
  obtain ⟨h₁, h₂⟩ := abs_lt.mp hi
  omega

theorem analyticAt_complexPhaseZeroPolynomial_coeff {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : PrimeCoordinate N → ℂ)
    {l u T : ℝ} (hlu : l ≤ u) (hT : 0 ≤ T)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      complexPhaseFamily a N (x, s) ≠ 0) (k : ℕ) :
    AnalyticAt ℂ (fun y => (complexPhaseZeroPolynomial a N hN ha l u T y).coeff k) x := by
  let d := verticalZeroCount (complexPhaseCoefficients a N x) N hN
    (by rwa [complexPhaseCoefficients_one]) l u T
  have he := eventually_eq_complexPhaseZero_count hN ha x hlu hT hn
  by_cases hk : k ≤ d
  · have haE := analyticAt_complexPhaseZero_esymm hN ha x hlu hT hn (d - k)
    apply (analyticAt_const (v := (-1 : ℂ) ^ (d - k)) |>.mul haE).congr
    filter_upwards [he] with y hy
    have hcard : (rectangleZeroMultiset (complexPhaseCoefficients a N y) N hN
        (by rwa [complexPhaseCoefficients_one]) l u T).card = d := by
      rw [rectangleZeroMultiset_card]
      exact hy
    symm
    dsimp only [complexPhaseZeroPolynomial, rectangleZeroPolynomial]
    rw [Multiset.prod_X_sub_C_coeff _ (by simpa only [hcard] using hk), hcard]
    rfl
  · apply (analyticAt_const (v := (0 : ℂ))).congr
    filter_upwards [he] with y hy
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [complexPhaseZeroPolynomial, rectangleZeroPolynomial_natDegree, hy]
    exact Nat.lt_of_not_ge hk

end

end Dubon2026
