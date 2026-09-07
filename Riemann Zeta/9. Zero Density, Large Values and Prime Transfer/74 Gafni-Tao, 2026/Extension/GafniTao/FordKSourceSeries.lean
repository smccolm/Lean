import GafniTao.FordKRightLine

/-!
# Ford's source Dirichlet series

This file identifies the inverse-Laplace output of the right contour with
Ford's literal `K(s)` and the `f(0) ζ'/ζ(s)` correction.  The indices `0`
and `1` remain in the Lean `tsum`, but their von Mangoldt coefficients vanish,
so this is exactly the paper's sum over `n ≥ 1`.
-/

open Complex Set Filter MeasureTheory
open scoped BigOperators Topology

namespace GafniTao

noncomputable section

/-- Ford's literal von Mangoldt summand. -/
noncomputable def fordKDirichletTerm
    (f : ℝ → ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) *
    Complex.exp (-s * (Real.log n : ℂ)) * (f (Real.log n) : ℂ)

/-- Ford's literal `K(s)`. -/
noncomputable def fordKDirichlet (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, fordKDirichletTerm f s n

/-- The pole-subtracted summand delivered by inverse Laplace inversion. -/
noncomputable def fordKCorrectionTerm
    (f : ℝ → ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) *
    Complex.exp (-s * (Real.log n : ℂ)) *
      fordLaplaceRemainder f (Real.log n)

/-- The elementary exponential von Mangoldt term is exactly Mathlib's
`LSeries.term` on the positive half-plane. -/
theorem ford_vonMangoldt_exp_term_eq_LSeries_term
    (s : ℂ) (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (-s * (Real.log n : ℂ)) =
      LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_def]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [ford_exp_neg_mul_log_eq_cpow_neg hnpos]
    rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg]
    norm_num [div_eq_mul_inv]

/-- Absolute summability of the elementary von Mangoldt series for
`Re s > 1`. -/
theorem summable_ford_vonMangoldt_exp_term
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      Complex.exp (-s * (Real.log n : ℂ))) := by
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).congr
    (fun n => (ford_vonMangoldt_exp_term_eq_LSeries_term s n).symm)

/-- The elementary series is `-ζ'/ζ`, with the sign convention used in
Ford's contour integrand. -/
theorem tsum_ford_vonMangoldt_exp_term
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
      Complex.exp (-s * (Real.log n : ℂ))) =
      -deriv riemannZeta s / riemannZeta s := by
  calc
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (-s * (Real.log n : ℂ))) =
      LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s := by
        rw [LSeries]
        apply tsum_congr
        exact ford_vonMangoldt_exp_term_eq_LSeries_term s
    _ = -deriv riemannZeta s / riemannZeta s := by
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]

/-- The pole-subtracted source series is absolutely summable.  This is a
consequence of the same height-independent envelope used in the proved
Tannery passage, together with the actual termwise inversion limit. -/
theorem summable_fordKCorrectionTerm
    {f : ℝ → ℝ} {s : ℂ} {alpha D eta : ℝ}
    (halpha : 1 < alpha) (ha : alpha < s.re) (hD : 0 ≤ D)
    (heta : eta ≤ s.re - alpha)
    (hfcont : ContinuousOn f (Set.Ioi 0))
    (hfdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ f y)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (fordLaplaceF0 f) z)
    (hAbs : ∀ z : ℂ, 0 < z.re → IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0))
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖fordLaplaceF0 f z‖ ≤ D / ‖z‖ ^ 2) :
    Summable (fordKCorrectionTerm f s) := by
  let C : ℝ := (1 / (2 * Real.pi)) * D *
    ∫ u : ℝ, fordKRightEnvelope s alpha u
  let B : ℕ → ℝ := fun n =>
    ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (alpha : ℂ) n‖ * C
  have hSeries : LSeriesSummable
      (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (alpha : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using halpha)
  have hB : Summable B := hSeries.norm.mul_right C
  apply hB.of_norm_bounded
  intro n
  have hlim := tendsto_vonMangoldt_mul_fordJTrunc_F0
    ha heta hfcont hfdiff hFdiff hAbs hF₀ n
  have hnormlim := tendsto_norm.comp hlim
  apply le_of_tendsto hnormlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have hbound := norm_vonMangoldt_mul_fordJTrunc_le
    ha hD heta hR hFdiff hF₀ n
  dsimp only [fordKCorrectionTerm, B, C]
  convert hbound using 1
  all_goals ring

theorem fordKCorrectionTerm_add_pole_eq
    (f : ℝ → ℝ) (s : ℂ) (n : ℕ) :
    fordKCorrectionTerm f s n + (f 0 : ℂ) *
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          Complex.exp (-s * (Real.log n : ℂ))) =
      fordKDirichletTerm f s n := by
  by_cases hn : 1 < n
  · rw [fordKCorrectionTerm, fordKDirichletTerm,
      fordLaplaceRemainder_log_nat f hn]
    push_cast
    ring
  · have hnle : n ≤ 1 := Nat.le_of_not_gt hn
    interval_cases n <;> simp [fordKCorrectionTerm, fordKDirichletTerm]

/-- Ford's equation `(I1)` at the series level: the inverse-transform
series is `K(s) + f(0) ζ'(s)/ζ(s)`. -/
theorem tsum_fordKCorrectionTerm_eq
    {f : ℝ → ℝ} {s : ℂ} {alpha D eta : ℝ}
    (hs : 1 < s.re) (halpha : 1 < alpha) (ha : alpha < s.re)
    (hD : 0 ≤ D) (heta : eta ≤ s.re - alpha)
    (hfcont : ContinuousOn f (Set.Ioi 0))
    (hfdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ f y)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (fordLaplaceF0 f) z)
    (hAbs : ∀ z : ℂ, 0 < z.re → IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0))
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖fordLaplaceF0 f z‖ ≤ D / ‖z‖ ^ 2) :
    (∑' n : ℕ, fordKCorrectionTerm f s n) =
      fordKDirichlet f s + (f 0 : ℂ) *
        (deriv riemannZeta s / riemannZeta s) := by
  have hc := summable_fordKCorrectionTerm
    halpha ha hD heta hfcont hfdiff hFdiff hAbs hF₀
  have hb := summable_ford_vonMangoldt_exp_term hs
  have hbp := hb.mul_left (f 0 : ℂ)
  have hKid : fordKDirichlet f s =
      (∑' n : ℕ, fordKCorrectionTerm f s n) +
        (f 0 : ℂ) *
          (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
            Complex.exp (-s * (Real.log n : ℂ))) := by
    rw [fordKDirichlet]
    calc
      (∑' n : ℕ, fordKDirichletTerm f s n) =
          ∑' n : ℕ, (fordKCorrectionTerm f s n +
            (f 0 : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℂ) *
              Complex.exp (-s * (Real.log n : ℂ)))) := by
        apply tsum_congr
        exact fun n => (fordKCorrectionTerm_add_pole_eq f s n).symm
      _ = (∑' n : ℕ, fordKCorrectionTerm f s n) +
          ∑' n : ℕ, (f 0 : ℂ) *
            ((ArithmeticFunction.vonMangoldt n : ℂ) *
              Complex.exp (-s * (Real.log n : ℂ))) := by
        rw [hc.tsum_add hbp]
      _ = _ := by rw [hb.tsum_mul_left]
  rw [hKid, tsum_ford_vonMangoldt_exp_term hs]
  ring

/-- Ford's equation `(I1)` in its contour form: the complete right vertical
integral equals `K(s) + f(0) ζ'(s)/ζ(s)`. -/
theorem tendsto_fordK_rightLine_eq_K_add_logDeriv
    {f : ℝ → ℝ} {s : ℂ} {alpha D eta : ℝ}
    (hs : 1 < s.re) (halpha : 1 < alpha) (ha : alpha < s.re)
    (hD : 0 ≤ D) (heta : eta ≤ s.re - alpha)
    (hfcont : ContinuousOn f (Set.Ioi 0))
    (hfdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ f y)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (fordLaplaceF0 f) z)
    (hAbs : ∀ z : ℂ, 0 < z.re → IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0))
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖fordLaplaceF0 f z‖ ≤ D / ‖z‖ ^ 2) :
    Tendsto
      (fun R : ℝ => VIntegral'
        (fordKSurrogateIntegrand s (fordLaplaceF0 f)) alpha (-R) R)
      atTop
      (𝓝 (fordKDirichlet f s + (f 0 : ℂ) *
        (deriv riemannZeta s / riemannZeta s))) := by
  have hright := tendsto_fordK_rightLine_F0
    halpha ha hD heta hfcont hfdiff hFdiff hAbs hF₀
  have hsum := tsum_fordKCorrectionTerm_eq
    hs halpha ha hD heta hfcont hfdiff hFdiff hAbs hF₀
  rw [show (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
      Complex.exp (-s * (Real.log n : ℂ)) *
        fordLaplaceRemainder f (Real.log n)) =
      ∑' n : ℕ, fordKCorrectionTerm f s n by rfl] at hright
  rwa [hsum] at hright

end

end GafniTao
