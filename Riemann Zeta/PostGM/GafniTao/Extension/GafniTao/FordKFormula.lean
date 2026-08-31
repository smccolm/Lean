import GafniTao.FordKLeftBound

/-!
# Ford's complete `K(s)` explicit formula

This is the first public consumer of the infinite rectangle.  It exposes the
pole, multiplicity-weighted nontrivial-zero series, and the complete left-line
error, then gives the uniform logarithmic error estimate needed downstream.
-/

open Complex MeasureTheory

namespace GafniTao

noncomputable section

/-- Ford's `K(s)` formula after the complete contour shift.  The zero term is
the absolutely convergent, analytic-multiplicity-weighted series defined by
unit height shells. -/
theorem fordK_formula_native
    {f : ℝ → ℝ} {s : ℂ} {alpha D eta : ℝ}
    (hs : 1 < s.re) (halpha : 1 < alpha) (ha : alpha < s.re)
    (ht : 0 ≤ s.im) (hD : 0 ≤ D)
    (hetaUpper : eta ≤ 3 / 2) (hetaRight : eta ≤ s.re - alpha)
    (hfcont : ContinuousOn f (Set.Ioi 0))
    (hfdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ f y)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (fordLaplaceF0 f) z)
    (hAbs : ∀ z : ℂ, 0 < z.re → IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0))
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖fordLaplaceF0 f z‖ ≤ D / ‖z‖ ^ 2) :
    fordKDirichlet f s =
      -(f 0 : ℂ) * (deriv riemannZeta s / riemannZeta s) -
        fordKZeroSeries (fordLaplaceF0 f) s +
        fordLaplaceF0 f (s - 1) +
        fordKLeftLineIntegral s (fordLaplaceF0 f) := by
  have h := fordK_infinite_rectangle_native hs halpha ha ht hD hetaUpper
    hetaRight hfcont hfdiff hFdiff hAbs hF₀
  linear_combination h

/-- Exact named error term in Ford's `K(s)` formula. -/
noncomputable def fordKFormulaError (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  fordKLeftLineIntegral s (fordLaplaceF0 f)

/-- The first Ford `K(s)` lemma with a proved uniform logarithmic error.
The unspecified constant is existential but its construction is explicit in
`FordKLeftBound`: it depends only on fixed left-line Cauchy masses and the
proved global zeta logarithmic-derivative constant, never on `f,s,D,eta`. -/
theorem fordK_formula_with_log_error_native :
    ∃ C : ℝ, 0 < C ∧
      ∀ {f : ℝ → ℝ} {s : ℂ} {alpha D eta : ℝ},
        1 < s.re → 1 < alpha → alpha < s.re → 0 ≤ s.im → 0 ≤ D →
        eta ≤ 3 / 2 → eta ≤ s.re - alpha →
        ContinuousOn f (Set.Ioi 0) →
        (∀ y : ℝ, 0 < y → DifferentiableAt ℝ f y) →
        (∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (fordLaplaceF0 f) z) →
        (∀ z : ℂ, 0 < z.re → IntegrableOn (fun y : ℝ =>
          Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0)) →
        (∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
          ‖fordLaplaceF0 f z‖ ≤ D / ‖z‖ ^ 2) →
        fordKDirichlet f s =
          -(f 0 : ℂ) * (deriv riemannZeta s / riemannZeta s) -
            fordKZeroSeries (fordLaplaceF0 f) s +
            fordLaplaceF0 f (s - 1) + fordKFormulaError f s ∧
        ‖fordKFormulaError f s‖ ≤ C * D * (1 + Real.log (|s.im| + 2)) := by
  obtain ⟨C₀, hC₀, hlog⟩ := exists_norm_riemannZeta_logDeriv_ford_leftLine_le
  let C : ℝ := C₀ * (fordLeftLogMass + fordLeftCauchyMass + 1) /
    (2 * Real.pi)
  have hmass : 0 < fordLeftLogMass + fordLeftCauchyMass + 1 := by
    linarith [fordLeftLogMass_nonneg, fordLeftCauchyMass_nonneg]
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f s alpha D eta hs halpha ha ht hD hetaUpper hetaRight
    hfcont hfdiff hFdiff hAbs hF₀
  constructor
  · simpa only [fordKFormulaError] using
      fordK_formula_native hs halpha ha ht hD hetaUpper hetaRight
        hfcont hfdiff hFdiff hAbs hF₀
  · have hbase := norm_fordKLeftLineIntegral_le_masses hs hD hetaUpper hF₀
      (by simpa [fordLeftLinePoint] using hlog) hC₀.le
    have hL : 0 ≤ Real.log (|s.im| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg s.im])
    have hm0 := fordLeftLogMass_nonneg
    have hm1 := fordLeftCauchyMass_nonneg
    dsimp [fordKFormulaError]
    calc
      ‖fordKLeftLineIntegral s (fordLaplaceF0 f)‖ ≤
          (C₀ * D / (2 * Real.pi)) *
            (fordLeftLogMass + Real.log (|s.im| + 2) * fordLeftCauchyMass) := hbase
      _ ≤ C * D * (1 + Real.log (|s.im| + 2)) := by
        dsimp [C]
        have hpi : 0 < 2 * Real.pi := by positivity
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
        rw [div_le_iff₀ hpi]
        field_simp [ne_of_gt hpi]
        nlinarith [mul_nonneg hm1 hL, mul_nonneg hm0 hL,
          mul_nonneg hC₀.le hD]

end

end GafniTao
