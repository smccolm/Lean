import GafniTao.PintzDigammaSharp
import RiemannZeta.GuthMaynard.HughesYoungSmallContourTail
import Mathlib.Analysis.ODE.Gronwall

/-!
# Sharp horizontal Gamma displacement

The logarithmic derivative of the squared Gamma norm is twice the real part
of digamma.  Combining that identity with the coefficient-one estimate in
`PintzDigammaSharp` preserves the physical conductor exponent in Pintz's
single-zeta approximate functional equation.
-/

open Complex Set

namespace GafniTao

noncomputable section

private theorem real_inner_self_mul (x y : ℂ) :
    inner ℝ x (x * y) = ‖x‖ ^ 2 * y.re := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  rw [show starRingEnd ℂ x * (x * y) =
      (starRingEnd ℂ x * x) * y by ring]
  rw [Complex.conj_mul']
  change (((↑‖x‖ : ℂ) ^ 2) * y).re = ‖x‖ ^ 2 * y.re
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]

/-- Squared-norm form of the sharp horizontal Gamma estimate.  Unlike a
bound obtained from `‖digamma‖`, the logarithmic height occurs with coefficient
exactly `2*d` before taking the square root. -/
theorem exists_norm_Gamma_sq_right_displacement_le {a b : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 < D ∧ ∀ (z : ℂ) (d : ℝ),
      a ≤ z.re → z.re + d ≤ b → 0 ≤ d →
      ‖Complex.Gamma (z + (d : ℂ))‖ ^ 2 ≤
        ‖Complex.Gamma z‖ ^ 2 *
          Real.exp (2 * (Real.log (|z.im| + 2) + D) * d) := by
  obtain ⟨D, hD, hdigamma⟩ := exists_re_digamma_le_log_add (a := a) (b := b) ha
  refine ⟨D, hD, ?_⟩
  intro z d hza hzdb hd
  let f : ℝ → ℂ := fun x => Complex.Gamma (z + (x : ℂ))
  let f' : ℝ → ℂ := fun x =>
    Complex.Gamma (z + (x : ℂ)) * Complex.digamma (z + (x : ℂ))
  let g : ℝ → ℝ := fun x => ‖f x‖ ^ 2
  let g' : ℝ → ℝ := fun x =>
    2 * ‖f x‖ ^ 2 * (Complex.digamma (z + (x : ℂ))).re
  let K : ℝ := 2 * (Real.log (|z.im| + 2) + D)
  have hlog : 0 ≤ Real.log (|z.im| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg z.im])
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hzpos (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      0 < (z + (x : ℂ)).re := by
    simp only [add_re, ofReal_re]
    linarith [hx.1]
  have hfderiv (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      HasDerivAt f (f' x) x := by
    have houter :=
      RiemannZeta.GuthMaynard.hasDerivAt_Gamma_eq_mul_digamma_of_re_pos
        (hzpos x hx)
    have hshift : HasDerivAt (fun w : ℂ => z + w) 1 (x : ℂ) :=
      (hasDerivAt_id (x : ℂ)).const_add z
    convert (houter.comp (x : ℂ) hshift).comp_ofReal using 1
    all_goals simp only [f']
    all_goals ring
  have hgderiv (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      HasDerivAt g (g' x) x := by
    have h := (hfderiv x hx).norm_sq
    convert h using 1
    simp only [g', f, f']
    rw [real_inner_self_mul]
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
    have hxLower : a ≤ (z + (x : ℂ)).re := by
      simp only [add_re, ofReal_re]
      linarith [hx.1]
    have hxUpper : (z + (x : ℂ)).re ≤ b := by
      simp only [add_re, ofReal_re]
      linarith [hx.2.le]
    have him : (z + (x : ℂ)).im = z.im := by simp
    have hpsi := hdigamma (z + (x : ℂ)) hxLower hxUpper
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
  change ‖Complex.Gamma (z + (d : ℂ))‖ ^ 2 ≤
    ‖Complex.Gamma z‖ ^ 2 *
      Real.exp (2 * (Real.log (|z.im| + 2) + D) * d)
  convert hgronwall using 1
  all_goals simp only [g, f, ofReal_zero, add_zero, K]

#print axioms exists_norm_Gamma_sq_right_displacement_le

/-- Norm form of the sharp horizontal Gamma estimate. -/
theorem exists_norm_Gamma_right_displacement_le {a b : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 < D ∧ ∀ (z : ℂ) (d : ℝ),
      a ≤ z.re → z.re + d ≤ b → 0 ≤ d →
      ‖Complex.Gamma (z + (d : ℂ))‖ ≤
        ‖Complex.Gamma z‖ *
          Real.exp ((Real.log (|z.im| + 2) + D) * d) := by
  obtain ⟨D, hD, hsquared⟩ :=
    exists_norm_Gamma_sq_right_displacement_le (a := a) (b := b) ha
  refine ⟨D, hD, ?_⟩
  intro z d hza hzdb hd
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)).mp
  calc
    ‖Complex.Gamma (z + (d : ℂ))‖ ^ 2 ≤
        ‖Complex.Gamma z‖ ^ 2 *
          Real.exp (2 * (Real.log (|z.im| + 2) + D) * d) :=
      hsquared z d hza hzdb hd
    _ = (‖Complex.Gamma z‖ *
          Real.exp ((Real.log (|z.im| + 2) + D) * d)) ^ 2 := by
      rw [mul_pow]
      congr 1
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

#print axioms exists_norm_Gamma_right_displacement_le

end

end GafniTao
