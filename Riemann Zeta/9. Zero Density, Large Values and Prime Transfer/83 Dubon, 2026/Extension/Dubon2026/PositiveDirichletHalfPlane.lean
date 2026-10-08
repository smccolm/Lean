import Dubon2026.PositiveDirichletTails

/-! # Holomorphy on a half-plane forces convergence of actual nonnegative Dirichlet coefficients -/

namespace Dubon2026

noncomputable section
open scoped ComplexOrder

/-- Every original finite Dirichlet prefix is bounded by its actual holomorphic continuation
at real points in the continued half-plane. Positivity is proved on a genuine Taylor disk. -/
theorem positive_dirichlet_partial_sum_le {a : ℕ → ℂ} (ha : 0 ≤ a)
    {F : ℂ → ℂ} {σ₀ A : ℝ} (hF : DifferentiableOn ℂ F {s : ℂ | σ₀ < s.re})
    (hA : LSeries.abscissaOfAbsConv a ≤ A)
    (hmatch : Set.EqOn F (LSeries a) {s : ℂ | A < s.re})
    {x : ℝ} (hx : σ₀ < x) (N : ℕ) :
    (∑ n ∈ Finset.range N, LSeries.term a (x : ℂ) n) ≤ F (x : ℂ) := by
  let c : ℝ := max A x + 1
  have hcA : A < c := lt_of_le_of_lt (le_max_left A x) (lt_add_one _)
  have hcx : x < c := lt_of_le_of_lt (le_max_right A x) (lt_add_one _)
  have hball : Metric.ball (c : ℂ) (c - σ₀) ⊆ {s : ℂ | σ₀ < s.re} := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hr := (abs_le.mp (Complex.abs_re_le_norm (z - (c : ℂ)))).1
    simp only [Complex.sub_re, Complex.ofReal_re] at hr
    change σ₀ < z.re
    linarith
  let G : ℂ → ℂ := fun s => F s - LSeries (dirichletCoefficientHead a N) s
  have hG : DifferentiableOn ℂ G (Metric.ball (c : ℂ) (c - σ₀)) :=
    (hF.mono hball).sub (dirichletCoefficientHead_differentiable a N).differentiableOn
  have he : Set.EqOn G (LSeries (a - dirichletCoefficientHead a N)) {s : ℂ | A < s.re} := by
    intro s hs
    have hs' : LSeriesSummable a s :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (hA.trans_lt (by exact_mod_cast hs))
    dsimp only [G]
    rw [hmatch hs, LSeries_sub hs' (dirichletCoefficientHead_hasSum a N s).summable]
  have hc : LSeries.abscissaOfAbsConv (a - dirichletCoefficientHead a N) < c := by
    rw [dirichletCoefficientTail_abscissa]
    exact hA.trans_lt (by exact_mod_cast hcA)
  have hd (n : ℕ) : 0 ≤ (-1) ^ n * iteratedDeriv n G (c : ℂ) := by
    rw [he.iteratedDeriv_of_isOpen (isOpen_lt continuous_const Complex.continuous_re) n
      (by simpa only [Set.mem_setOf_eq, Complex.ofReal_re] using hcA)]
    exact LSeries.iteratedDeriv_alternating (dirichletCoefficientTail_nonneg ha N) hc n
  have hxball : (x : ℂ) ∈ Metric.ball (c : ℂ) (c - σ₀) := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hcx.le)]
    linarith
  have hp := nonneg_of_iteratedDeriv_alternating_on_ball hG hd
    (by exact_mod_cast hcx.le : (x : ℂ) ≤ (c : ℂ)) hxball
  simpa only [G, dirichletCoefficientHead_LSeries] using sub_nonneg.mp hp

/-- A genuine nonnegative-coefficient Dirichlet series is absolutely convergent at every real
point of an open half-plane where its actual continuation is holomorphic. -/
theorem positive_dirichlet_summable_of_holomorphic {a : ℕ → ℂ} (ha : 0 ≤ a)
    {F : ℂ → ℂ} {σ₀ A : ℝ} (hF : DifferentiableOn ℂ F {s : ℂ | σ₀ < s.re})
    (hA : LSeries.abscissaOfAbsConv a ≤ A)
    (hmatch : Set.EqOn F (LSeries a) {s : ℂ | A < s.re})
    {x : ℝ} (hx : σ₀ < x) : LSeriesSummable a (x : ℂ) := by
  apply Summable.of_norm
  apply summable_of_sum_range_le (fun n => norm_nonneg _) (c := (F (x : ℂ)).re)
  intro N
  have hle := (Complex.le_def.mp (positive_dirichlet_partial_sum_le ha hF hA hmatch hx N)).1
  calc
    _ = ∑ n ∈ Finset.range N, (LSeries.term a (x : ℂ) n).re := by
      apply Finset.sum_congr rfl
      intro n _
      exact (Complex.re_eq_norm.mpr (LSeries.term_nonneg (ha n) x)).symm
    _ = (∑ n ∈ Finset.range N, LSeries.term a (x : ℂ) n).re := by simp
    _ ≤ _ := hle

/-- Landau's abscissa consequence, proved from actual finite prefixes and their Taylor positivity. -/
theorem positive_dirichlet_abscissa_le_of_holomorphic {a : ℕ → ℂ} (ha : 0 ≤ a)
    {F : ℂ → ℂ} {σ₀ A : ℝ} (hF : DifferentiableOn ℂ F {s : ℂ | σ₀ < s.re})
    (hA : LSeries.abscissaOfAbsConv a ≤ A)
    (hmatch : Set.EqOn F (LSeries a) {s : ℂ | A < s.re}) :
    LSeries.abscissaOfAbsConv a ≤ σ₀ := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro x hx
  exact positive_dirichlet_summable_of_holomorphic ha hF hA hmatch hx

end
end Dubon2026
