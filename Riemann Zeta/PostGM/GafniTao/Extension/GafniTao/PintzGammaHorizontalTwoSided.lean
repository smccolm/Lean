import GafniTao.PintzGammaHorizontalSharp
import GafniTao.PintzDigammaLowerSharp

/-!
# Two-sided sharp horizontal Gamma displacement

The lower real-part estimate for digamma gives the missing reverse
displacement inequality.  Its logarithmic coefficient is exactly `-d`, so
the polynomial powers cancel when numerator and denominator Gamma factors
are compared on different horizontal lines.
-/

open Complex Set

namespace GafniTao

noncomputable section

private theorem real_inner_self_mul_lower (x y : ℂ) :
    inner ℝ x (x * y) = ‖x‖ ^ 2 * y.re := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  rw [show starRingEnd ℂ x * (x * y) =
      (starRingEnd ℂ x * x) * y by ring]
  rw [Complex.conj_mul']
  change (((↑‖x‖ : ℂ) ^ 2) * y).re = ‖x‖ ^ 2 * y.re
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]

set_option maxHeartbeats 800000 in
/-- Squared-norm reverse displacement.  Moving Gamma left by `d` costs
`exp(2*(D-log height)*d)`, with coefficient exactly minus two on the
height logarithm. -/
theorem exists_norm_Gamma_sq_left_displacement_le {a b : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 < D ∧ ∀ (z : ℂ) (d : ℝ),
      a ≤ z.re - d → z.re ≤ b → 0 ≤ d →
      ‖Complex.Gamma (z - (d : ℂ))‖ ^ 2 ≤
        ‖Complex.Gamma z‖ ^ 2 *
          Real.exp (2 * (D - Real.log (|z.im| + 2)) * d) := by
  obtain ⟨D, hD, hdigamma⟩ := exists_log_sub_le_re_digamma (a := a) (b := b) ha
  refine ⟨D, hD, ?_⟩
  intro z d hza hzdb hd
  let f : ℝ → ℂ := fun x => Complex.Gamma (z - (x : ℂ))
  let f' : ℝ → ℂ := fun x =>
    -(Complex.Gamma (z - (x : ℂ)) * Complex.digamma (z - (x : ℂ)))
  let g : ℝ → ℝ := fun x => ‖f x‖ ^ 2
  let g' : ℝ → ℝ := fun x =>
    -(2 * ‖f x‖ ^ 2 * (Complex.digamma (z - (x : ℂ))).re)
  let K : ℝ := 2 * (D - Real.log (|z.im| + 2))
  have hzpos (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      0 < (z - (x : ℂ)).re := by
    simp only [sub_re, ofReal_re]
    linarith [hx.2]
  have hfderiv (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      HasDerivAt f (f' x) x := by
    have houter :=
      RiemannZeta.GuthMaynard.hasDerivAt_Gamma_eq_mul_digamma_of_re_pos
        (hzpos x hx)
    have hshift : HasDerivAt (fun w : ℂ => z - w) (-1) (x : ℂ) := by
      simpa using
        (hasDerivAt_const (x := (x : ℂ)) z).sub (hasDerivAt_id (x : ℂ))
    convert (houter.comp (x : ℂ) hshift).comp_ofReal using 1
    all_goals simp only [f']
    all_goals ring
  have hgderiv (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      HasDerivAt g (g' x) x := by
    have h := (hfderiv x hx).norm_sq
    convert h using 1
    simp only [g', f, f']
    rw [inner_neg_right]
    rw [real_inner_self_mul_lower]
    ring
  have hgcont : ContinuousOn g (Set.Icc 0 d) := by
    intro x hx
    exact (hgderiv x hx).continuousAt.continuousWithinAt
  have hgwithin : ∀ x ∈ Set.Ico 0 d,
      HasDerivWithinAt g (g' x) (Set.Ici x) x := by
    intro x hx
    exact (hgderiv x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico 0 d, g' x ≤ K * g x + 0 := by
    intro x hx
    have hxLower : a ≤ (z - (x : ℂ)).re := by
      simp only [sub_re, ofReal_re]
      linarith [hx.2.le]
    have hxUpper : (z - (x : ℂ)).re ≤ b := by
      simp only [sub_re, ofReal_re]
      linarith [hx.1]
    have him : (z - (x : ℂ)).im = z.im := by simp
    have hpsi := hdigamma (z - (x : ℂ)) hxLower hxUpper
    rw [him] at hpsi
    dsimp only [g', K, g]
    have hsq : 0 ≤ ‖f x‖ ^ 2 := sq_nonneg _
    nlinarith
  have hgronwall := le_gronwallBound_of_liminf_deriv_right_le
    hgcont
    (fun x hx _r hr => (hgwithin x hx).liminf_right_slope_le hr)
    (show g 0 ≤ g 0 by rfl) hbound d
    (show d ∈ Set.Icc 0 d from ⟨hd, le_rfl⟩)
  rw [gronwallBound_ε0, sub_zero] at hgronwall
  change ‖Complex.Gamma (z - (d : ℂ))‖ ^ 2 ≤
    ‖Complex.Gamma z‖ ^ 2 *
      Real.exp (2 * (D - Real.log (|z.im| + 2)) * d)
  convert hgronwall using 1
  all_goals simp only [g, f, ofReal_zero, sub_zero, K]

/-- Norm form of the reverse sharp Gamma displacement. -/
theorem exists_norm_Gamma_left_displacement_le {a b : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 < D ∧ ∀ (z : ℂ) (d : ℝ),
      a ≤ z.re - d → z.re ≤ b → 0 ≤ d →
      ‖Complex.Gamma (z - (d : ℂ))‖ ≤
        ‖Complex.Gamma z‖ *
          Real.exp ((D - Real.log (|z.im| + 2)) * d) := by
  obtain ⟨D, hD, hsquared⟩ :=
    exists_norm_Gamma_sq_left_displacement_le (a := a) (b := b) ha
  refine ⟨D, hD, ?_⟩
  intro z d hza hzdb hd
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)).mp
  calc
    ‖Complex.Gamma (z - (d : ℂ))‖ ^ 2 ≤
        ‖Complex.Gamma z‖ ^ 2 *
          Real.exp (2 * (D - Real.log (|z.im| + 2)) * d) :=
      hsquared z d hza hzdb hd
    _ = (‖Complex.Gamma z‖ *
          Real.exp ((D - Real.log (|z.im| + 2)) * d)) ^ 2 := by
      rw [mul_pow]
      congr 1
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

#print axioms exists_norm_Gamma_sq_left_displacement_le
#print axioms exists_norm_Gamma_left_displacement_le

end

end GafniTao
