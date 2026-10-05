import DhimanKadiriQuesadaHerrera2026.MonotoneAmplitude

/-! # Gaussian damping and uniform Fresnel tails

Adapted from node 63 TaoTrudgianYang2025/FresnelDampedTails.lean,
SHA-256 e932d8ad7e1d85ed131fe96212d0899a43770db95228886627b544c1804914b7.
The original has no separate license header and remains unchanged.
The damping kernel and normalization are retained. The derivative/primitive
arguments now consume this project's proved first-derivative and amplitude
lemmas, avoiding the unrelated Atkinson import closure.
-/

noncomputable section

open Complex MeasureTheory Set

namespace DhimanKadiriQuesadaHerrera2026

/-- The actual quadratic kernel with a real nonnegative damping parameter. -/
def fresnelDampedKernel (ε c x : ℝ) : ℂ :=
  Complex.exp (-((ε : ℂ) + 2 * Real.pi * c * I) * (x : ℂ) ^ 2)

/-- The quadratic oscillatory integral on the symmetric finite window. -/
def quadraticWindow (c H : ℝ) : ℂ :=
  ∫ z in (-H)..H, Complex.exp (((-2 * Real.pi * c * z ^ 2 : ℝ) : ℂ) * I)

/-- Damping preserves continuity of the actual kernel. -/
theorem continuous_fresnelDampedKernel (ε c : ℝ) : Continuous (fresnelDampedKernel ε c) := by
  unfold fresnelDampedKernel
  fun_prop

/-- The damped kernel factors into its real amplitude and quadratic phase. -/
theorem fresnelDampedKernel_eq_weighted (ε c x : ℝ) :
    fresnelDampedKernel ε c x = (Real.exp (-ε * x ^ 2) : ℂ) *
      Complex.exp (I * ((-2 * Real.pi * c * x ^ 2 : ℝ) : ℂ)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  unfold fresnelDampedKernel
  congr 1
  push_cast
  ring

/-- The actual kernel is even. -/
theorem fresnelDampedKernel_neg (ε c x : ℝ) :
    fresnelDampedKernel ε c (-x) = fresnelDampedKernel ε c x := by
  simp only [fresnelDampedKernel, Complex.ofReal_neg, neg_sq]

/-- The unit quadratic phase has the sharp reciprocal-slope finite-tail bound. -/
theorem norm_fresnelPhase_integral_le {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, Complex.exp (I * ((-2 * Real.pi * c * x ^ 2 : ℝ) : ℂ))‖ ≤
      1 / (2 * c * a * Real.pi) := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp only [intervalIntegral.integral_same, norm_zero]
    positivity
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => -2 * Real.pi * c * y ^ 2)
      (-4 * Real.pi * c * x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul (-2 * Real.pi * c)) using 1
    dsimp
    ring
  have hp (x : ℝ) (hx : x ∈ Icc a b) : 0 < x := ha.trans_le hx.1
  have hq (x : ℝ) (hx : x ∈ Icc a b) :
      |1 / (-4 * Real.pi * c * x)| = 1 / (4 * Real.pi * c * x) := by
    rw [abs_div, abs_one, abs_of_neg (by nlinarith [mul_pos (mul_pos Real.pi_pos hc) (hp x hx)])]
    congr 1
    ring
  have h := first_derivative_test_antitone hab (fun x _ => hd x)
    (by fun_prop) (g := fun _ => 1) continuousOn_const
    (fun x hx => by have hxpos := hp x hx; positivity)
    (by
      intro x hx y hy hxy
      have hxpos := hp x hx
      dsimp only
      rw [hq x hx, hq y hy]
      exact one_div_le_one_div_of_le (by positivity : 0 < 4 * Real.pi * c * x)
        (mul_le_mul_of_nonneg_left hxy (by positivity)))
  simp only [Complex.ofReal_one, one_mul] at h
  rw [hq a (left_mem_Icc.mpr hab.le)] at h
  apply h.trans_eq
  field_simp
  ring

/-- The damping-uniform estimate is derived from the actual decreasing Gaussian amplitude. -/
theorem norm_integral_fresnelDampedKernel_le {ε c a b : ℝ}
    (hε : 0 ≤ ε) (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, fresnelDampedKernel ε c x‖ ≤ 1 / (c * a * Real.pi) := by
  let K : ℝ → ℂ := fun x => Complex.exp (I * ((-2 * Real.pi * c * x ^ 2 : ℝ) : ℂ))
  have hK : Continuous K := by dsimp [K]; fun_prop
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-ε * y ^ 2))
      (Real.exp (-ε * x ^ 2) * (-2 * ε * x)) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul (-ε)).exp using 1
    dsimp
    ring
  have h := norm_integral_mul_le_of_primitive_bound hab
    (g := fun x => Real.exp (-ε * x ^ 2))
    (g' := fun x => Real.exp (-ε * x ^ 2) * (-2 * ε * x))
    (F := fun x => ∫ y in a..x, K y)
    (fun x _ => hd x)
    (fun x _ => intervalIntegral.integral_hasDerivAt_right (hK.intervalIntegrable a x)
      hK.stronglyMeasurable.stronglyMeasurableAtFilter hK.continuousAt)
    (by fun_prop) hK.continuousOn (Real.exp_pos _).le
    (by
      intro x hx
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hx0 : 0 ≤ x := ha.le.trans hx.1
      nlinarith [mul_nonneg hε hx0])
    (by simp)
    (fun x hx => norm_fresnelPhase_integral_le hc ha hx.1)
  have hg : Real.exp (-ε * a ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by
    nlinarith [mul_nonneg hε (sq_nonneg a)])
  simp_rw [fresnelDampedKernel_eq_weighted]
  apply h.trans
  calc
    _ ≤ 1 * (1 / (2 * c * a * Real.pi)) :=
      mul_le_mul_of_nonneg_right hg (by positivity)
    _ ≤ 1 / (c * a * Real.pi) := by
      rw [one_mul]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [mul_pos (mul_pos hc ha) Real.pi_pos]

end DhimanKadiriQuesadaHerrera2026

