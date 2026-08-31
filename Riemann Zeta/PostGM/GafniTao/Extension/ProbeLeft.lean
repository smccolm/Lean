import GafniTao.FordKZeroSeries

open Complex Filter Set MeasureTheory

open GafniTao

example {F₀ : ℂ → ℂ} {s : ℂ}
    (hs : 1 < s.re)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z) :
    Continuous (fun u : ℝ =>
      (-deriv riemannZeta (fordLeftLinePoint u) /
          riemannZeta (fordLeftLinePoint u)) *
        F₀ (s - fordLeftLinePoint u)) := by
  have hp : Continuous fordLeftLinePoint := by
    unfold fordLeftLinePoint
    fun_prop
  have hpOne : ∀ u : ℝ, fordLeftLinePoint u ≠ 1 := by
    intro u h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hz : Continuous (fun u : ℝ => riemannZeta (fordLeftLinePoint u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (analyticAt_riemannZeta (hpOne u)).continuousAt.comp_of_eq
      hp.continuousAt rfl
  have hdz : Continuous (fun u : ℝ => deriv riemannZeta (fordLeftLinePoint u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (differentiableAt_deriv_riemannZeta (hpOne u)).continuousAt.comp_of_eq
      hp.continuousAt rfl
  have hF : Continuous (fun u : ℝ => F₀ (s - fordLeftLinePoint u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hre : 0 < (s - fordLeftLinePoint u).re := by simp; linarith
    exact (hFdiff _ hre).continuousAt.comp_of_eq
      (continuousAt_const.sub hp.continuousAt) rfl
  exact (hdz.neg.div hz (fun u => ford_leftLine_zeta_ne_zero u)).mul hF
