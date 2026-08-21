import RiemannZeta.GuthMaynard.HughesYoungCentralContour

open Complex Filter MeasureTheory Set Topology
open scoped Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative bounds for the pole-cancelled Hughes--Young contour

These estimates supply the analytic bounds needed to move the exact
equation-(84) contour from the small positive line to `Re w = 1`.
-/

/-- Euler's integral bounds `Gamma` uniformly in the height on any compact
positive real-part strip. -/
theorem exists_uniform_norm_Gamma_vertical_strip
    {a b : ℝ} (ha : 0 < a) :
    ∃ G : ℝ, 0 < G ∧ ∀ (x y : ℝ), x ∈ Set.Icc a b →
      ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ ≤ G := by
  let gammaMajor : ℝ → ℝ := fun x => Real.Gamma x
  have hgammaCont : ContinuousOn gammaMajor (Set.Icc a b) := by
    exact Real.differentiableOn_Gamma_Ioi.continuousOn.mono (by
      intro x hx
      exact ha.trans_le hx.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hgammaCont
  refine ⟨max 1 C, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro x y hx
  have hspos : 0 < (((x : ℂ) + (y : ℂ) * I)).re := by
    simpa using ha.trans_le hx.1
  have hbound := norm_Gamma_le_realGamma_re hspos
  have hmajor : gammaMajor x ≤ C := hC ⟨x, hx, rfl⟩
  have hbound' : ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ ≤ gammaMajor x := by
    simpa only [gammaMajor, add_re, ofReal_re, mul_re, I_re, I_im,
      ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] using hbound
  exact hbound'.trans (hmajor.trans (le_max_right 1 C))

/-- A deliberately coarse elementary bound for complex sine.  Its quadratic
exponential form is convenient because the Gaussian `exp (100 w^2)` has far
stronger decay on horizontal contour edges. -/
theorem norm_complex_sin_le_two_mul_exp_sq_im (z : ℂ) :
    ‖Complex.sin z‖ ≤
      2 * Real.exp ((z.im ^ 2 + 1) / 2) := by
  have htwo : 2 * ‖Complex.sin z‖ = ‖(2 : ℂ) * Complex.sin z‖ := by
    simp
  have hraw : ‖(2 : ℂ) * Complex.sin z‖ ≤
      Real.exp z.im + Real.exp (-z.im) := by
    rw [Complex.two_sin]
    calc
      ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I‖ =
          ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ := by simp
      _ ≤ ‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖ := norm_sub_le _ _
      _ = Real.exp z.im + Real.exp (-z.im) := by
        rw [Complex.norm_exp, Complex.norm_exp]
        simp
  have hplus : Real.exp z.im ≤ Real.exp ((z.im ^ 2 + 1) / 2) := by
    rw [Real.exp_le_exp]
    nlinarith [sq_nonneg (z.im - 1)]
  have hminus : Real.exp (-z.im) ≤ Real.exp ((z.im ^ 2 + 1) / 2) := by
    rw [Real.exp_le_exp]
    nlinarith [sq_nonneg (z.im + 1)]
  have htwice : 2 * ‖Complex.sin z‖ ≤
      2 * Real.exp ((z.im ^ 2 + 1) / 2) := by
    rw [htwo]
    exact hraw.trans (by linarith)
  have hnonneg : 0 ≤ Real.exp ((z.im ^ 2 + 1) / 2) := (Real.exp_pos _).le
  linarith [norm_nonneg (Complex.sin z)]

/-- Reflection followed by two Gamma recurrences expresses reciprocal Gamma
using a Gamma factor in a positive translated strip.  The nonreal hypothesis
is exactly what excludes all poles and sine zeros on the horizontal edges. -/
theorem one_div_Gamma_eq_Gamma_three_sub_mul_sin
    {p : ℂ} (hpim : p.im ≠ 0) :
    (Complex.Gamma p)⁻¹ =
      Complex.Gamma (3 - p) * Complex.sin ((Real.pi : ℂ) * p) /
        ((Real.pi : ℂ) * (2 - p) * (1 - p)) := by
  have hpoles : ∀ n : ℕ, p ≠ -(n : ℂ) := by
    intro n hn
    apply hpim
    have him := congrArg Complex.im hn
    simpa using him
  have hGp : Complex.Gamma p ≠ 0 := Complex.Gamma_ne_zero hpoles
  have hsin : Complex.sin ((Real.pi : ℂ) * p) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    apply hpim
    have him := congrArg Complex.im hk
    simp at him
    exact him
  have hOne : (1 : ℂ) - p ≠ 0 := by
    intro h
    apply hpim
    have him := congrArg Complex.im h
    simpa using him
  have hTwo : (2 : ℂ) - p ≠ 0 := by
    intro h
    apply hpim
    have him := congrArg Complex.im h
    simpa using him
  have hrecOne := Complex.Gamma_add_one ((1 : ℂ) - p) hOne
  have hrecTwo := Complex.Gamma_add_one ((2 : ℂ) - p) hTwo
  have hrecOne' : Complex.Gamma (2 - p) =
      (1 - p) * Complex.Gamma (1 - p) := by
    rw [show (2 : ℂ) - p = (1 - p) + 1 by ring]
    exact hrecOne
  have hrecTwo' : Complex.Gamma (3 - p) =
      (2 - p) * Complex.Gamma (2 - p) := by
    rw [show (3 : ℂ) - p = (2 - p) + 1 by ring]
    exact hrecTwo
  have hrec : Complex.Gamma (3 - p) =
      (2 - p) * (1 - p) * Complex.Gamma (1 - p) := by
    rw [hrecTwo', hrecOne']
    ring
  have href := Complex.Gamma_mul_Gamma_one_sub p
  have hsin' : Complex.sin (p * (Real.pi : ℂ)) ≠ 0 := by
    simpa only [mul_comm] using hsin
  rw [hrec]
  field_simp [hGp, hsin, hOne, hTwo, Real.pi_ne_zero] at href ⊢
  rw [href]

/-- Reciprocal Gamma has at most a coarse quadratic-exponential growth on
the horizontal sides of the Hughes--Young rectangle.  This estimate is
intentionally weaker than Stirling, but the `exp (100 w^2)` factor still
dominates it by a wide margin. -/
theorem exists_norm_inv_Gamma_critical_horizontal_far_le
    {c₀ c₁ : ℝ} (hc₁ : c₁ < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t y : ℝ), 1 ≤ |t + y| →
      ∀ x ∈ Set.Icc c₀ c₁,
        ‖(Complex.Gamma
            (afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I)))⁻¹‖ ≤
          C * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) := by
  have ha : 0 < (5 / 2 : ℝ) - c₁ := by linarith
  obtain ⟨G, hGpos, hG⟩ :=
    exists_uniform_norm_Gamma_vertical_strip
      (a := (5 / 2 : ℝ) - c₁) (b := (5 / 2 : ℝ) - c₀) ha
  let C : ℝ := 2 * G / Real.pi
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t y hy x hx
  let p : ℂ := afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I)
  have hpim : p.im ≠ 0 := by
    have hpimEq : p.im = t + y := by simp [p, afeCriticalPoint]
    rw [hpimEq]
    exact abs_ne_zero.mp (ne_of_gt (zero_lt_one.trans_le hy))
  have hthree : 3 - p =
      ((((5 / 2 : ℝ) - x : ℝ) : ℂ) + ((-(t + y) : ℝ) : ℂ) * I) := by
    dsimp [p, afeCriticalPoint]
    push_cast
    ring
  have hxstrip : (5 / 2 : ℝ) - x ∈
      Set.Icc ((5 / 2 : ℝ) - c₁) ((5 / 2 : ℝ) - c₀) := by
    constructor <;> linarith [hx.1, hx.2]
  have hGamma : ‖Complex.Gamma (3 - p)‖ ≤ G := by
    rw [hthree]
    exact hG ((5 / 2 : ℝ) - x) (-(t + y)) hxstrip
  have hpimAbs : |p.im| = |t + y| := by simp [p, afeCriticalPoint]
  have hOne : 1 ≤ ‖1 - p‖ := by
    have him := Complex.abs_im_le_norm (1 - p)
    have himEq : |(1 - p).im| = |t + y| := by
      rw [show (1 - p).im = -p.im by simp, abs_neg, hpimAbs]
    rw [himEq] at him
    exact hy.trans him
  have hTwo : 1 ≤ ‖2 - p‖ := by
    have him := Complex.abs_im_le_norm (2 - p)
    have himEq : |(2 - p).im| = |t + y| := by
      rw [show (2 - p).im = -p.im by norm_num, abs_neg, hpimAbs]
    rw [himEq] at him
    exact hy.trans him
  have hsin := norm_complex_sin_le_two_mul_exp_sq_im
    ((Real.pi : ℂ) * p)
  have hsin' : ‖Complex.sin ((Real.pi : ℂ) * p)‖ ≤
      2 * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) := by
    have himEq : (((Real.pi : ℂ) * p).im) = Real.pi * (t + y) := by
      simp [p, afeCriticalPoint]
    simpa only [himEq] using hsin
  rw [one_div_Gamma_eq_Gamma_three_sub_mul_sin hpim]
  rw [norm_div, norm_mul]
  have hden : Real.pi ≤
      ‖((Real.pi : ℂ) * (2 - p) * (1 - p))‖ := by
    simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    calc
      Real.pi ≤ Real.pi * ‖2 - p‖ := by
        nlinarith [Real.pi_pos, hTwo]
      _ ≤ Real.pi * ‖2 - p‖ * ‖1 - p‖ := by
        exact le_mul_of_one_le_right (by positivity) hOne
  apply (div_le_iff₀ (lt_of_lt_of_le Real.pi_pos hden)).2
  calc
    ‖Complex.Gamma (3 - p)‖ *
          ‖Complex.sin ((Real.pi : ℂ) * p)‖ ≤
        G * (2 * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2)) := by
      gcongr
    _ = C * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) * Real.pi := by
      dsimp [C]
      field_simp [Real.pi_ne_zero]
    _ ≤ C * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) *
          ‖((Real.pi : ℂ) * (2 - p) * (1 - p))‖ := by
      gcongr

/-- Reciprocal Gamma admits the same coarse quadratic-exponential majorant
on the whole horizontal strip.  The bounded-height part is obtained from
compactness of the entire reciprocal-Gamma function; the unbounded part is
the reflection-formula estimate above. -/
theorem exists_norm_inv_Gamma_critical_horizontal_le
    {c₀ c₁ : ℝ} (hc₁ : c₁ < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t y : ℝ),
      ∀ x ∈ Set.Icc c₀ c₁,
        ‖(Complex.Gamma
            (afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I)))⁻¹‖ ≤
          C * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) := by
  obtain ⟨Cfar, hCfar, hfar⟩ :=
    exists_norm_inv_Gamma_critical_horizontal_far_le
      (c₀ := c₀) (c₁ := c₁) hc₁
  let f : ℝ × ℝ → ℝ := fun z =>
    ‖(Complex.Gamma
      ((((1 / 2 : ℝ) + z.1 : ℝ) : ℂ) + (z.2 : ℂ) * I))⁻¹‖
  have harg : Continuous (fun z : ℝ × ℝ =>
      ((((1 / 2 : ℝ) + z.1 : ℝ) : ℂ) + (z.2 : ℂ) * I)) := by
    fun_prop
  have hf : Continuous f := by
    exact (Complex.differentiable_one_div_Gamma.continuous.comp harg).norm
  have hcompact : IsCompact (Set.Icc c₀ c₁ ×ˢ Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨Csmall, hCsmall⟩ := hcompact.bddAbove_image hf.continuousOn
  let C : ℝ := max Cfar (max 1 Csmall)
  have hC : 0 < C := hCfar.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro t y x hx
  let v : ℝ := t + y
  by_cases hv : 1 ≤ |v|
  · have h := hfar t y (by simpa only [v] using hv) x hx
    exact h.trans <| mul_le_mul_of_nonneg_right
      (le_max_left Cfar (max 1 Csmall)) (Real.exp_pos _).le
  · have hvabs : |v| ≤ 1 := le_of_lt (lt_of_not_ge hv)
    have hvMem : v ∈ Set.Icc (-1 : ℝ) 1 := (abs_le.mp hvabs)
    have hsmall : f (x, v) ≤ Csmall :=
      hCsmall ⟨(x, v), ⟨hx, hvMem⟩, rfl⟩
    have hnorm :
        ‖(Complex.Gamma
          (afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I)))⁻¹‖ = f (x, v) := by
      dsimp only [f, v, afeCriticalPoint]
      congr 3
      push_cast
      ring
    rw [hnorm]
    calc
      f (x, v) ≤ Csmall := hsmall
      _ ≤ C := (le_max_right 1 Csmall).trans (le_max_right Cfar (max 1 Csmall))
      _ ≤ C * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) := by
        have hexp : 1 ≤ Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) := by
          rw [← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          positivity
        exact le_mul_of_one_le_right hC.le hexp

/-- A linear majorant for digamma on a compact positive real-part strip.
The logarithmic source estimate is retained in the proof, while this weaker
form is more convenient for the final Gaussian domination. -/
theorem exists_uniform_norm_digamma_vertical_strip_linear
    {a b : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 < D ∧ ∀ (x y : ℝ), x ∈ Set.Icc a b →
      ‖Complex.digamma ((x : ℂ) + (y : ℂ) * I)‖ ≤
        D * (|y| + 2) := by
  obtain ⟨D, hD, hbound⟩ :=
    Complex.exists_norm_digamma_le_log (a := a) (b := b) ha
  refine ⟨D, hD, ?_⟩
  intro x y hx
  have hraw := hbound ((x : ℂ) + (y : ℂ) * I)
    (by simpa using hx.1) (by simpa using hx.2)
  have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
  rw [him] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (Real.log_le_self (by positivity)) hD.le)

/-- The two pole-cancelled Gamma factors in equation (84) have uniform
polynomial growth across the full contour-shift strip. -/
theorem exists_norm_hughesYoungRegularizedGamma_pair_horizontal_le
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2)
    (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t y x : ℝ), x ∈ Set.Icc c₀ c₁ →
      let z := afeCriticalPoint t - ((x : ℂ) + (y : ℂ) * I)
      let R := 2 + |t| + c₁ + |y|
      ‖hughesYoungRegularizedGamma z‖ ≤ C * R ∧
        ‖hughesYoungRegularizedGammaDigamma z‖ ≤ C * R ^ 2 := by
  have ha : 0 < (3 / 2 : ℝ) - c₁ := by linarith
  obtain ⟨G, hG, hGamma⟩ := exists_uniform_norm_Gamma_vertical_strip
    (a := (3 / 2 : ℝ) - c₁) (b := (3 / 2 : ℝ) - c₀) ha
  obtain ⟨D, hD, hDigamma⟩ :=
    exists_uniform_norm_digamma_vertical_strip_linear
      (a := (3 / 2 : ℝ) - c₁) (b := (3 / 2 : ℝ) - c₀) ha
  let C : ℝ := G * (D + 1)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t y x hx
  dsimp only
  let z : ℂ := afeCriticalPoint t - ((x : ℂ) + (y : ℂ) * I)
  let R : ℝ := 2 + |t| + c₁ + |y|
  have hc₁0 : 0 ≤ c₁ := hc₀.le.trans hc
  have hR1 : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg t, abs_nonneg y]
  have hzNorm : ‖z‖ ≤ R := by
    have hxmem : -x ∈ Set.uIcc (-c₁) c₁ := by
      rw [uIcc_of_le (by linarith)]
      exact ⟨by linarith [hx.2], by linarith [hx.1, hc₀]⟩
    have h := one_add_norm_afeCriticalPoint_add_horizontal_abs_le
      t c₁ (-y) (-x) hc₁0 hxmem
    have hzEq : z =
        afeCriticalPoint t + (((-x : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      dsimp [z]
      push_cast
      ring
    rw [hzEq]
    simp only [abs_neg] at h
    linarith
  have hzOne : z + 1 =
      ((((3 / 2 : ℝ) - x : ℝ) : ℂ) + ((t - y : ℝ) : ℂ) * I) := by
    dsimp [z, afeCriticalPoint]
    push_cast
    ring
  have hxstrip : (3 / 2 : ℝ) - x ∈
      Set.Icc ((3 / 2 : ℝ) - c₁) ((3 / 2 : ℝ) - c₀) := by
    constructor <;> linarith [hx.1, hx.2]
  have hGammaZ : ‖Complex.Gamma (z + 1)‖ ≤ G := by
    rw [hzOne]
    exact hGamma ((3 / 2 : ℝ) - x) (t - y) hxstrip
  have hty : |t - y| + 2 ≤ R := by
    dsimp [R]
    have htri : |t - y| ≤ |t| + |y| := by
      rw [sub_eq_add_neg]
      simpa only [abs_neg] using abs_add_le t (-y)
    linarith
  have hDigammaZ : ‖Complex.digamma (z + 1)‖ ≤ D * R := by
    rw [hzOne]
    exact (hDigamma ((3 / 2 : ℝ) - x) (t - y) hxstrip).trans
      (mul_le_mul_of_nonneg_left hty hD.le)
  constructor
  · unfold hughesYoungRegularizedGamma
    rw [norm_mul]
    calc
      ‖z‖ * ‖Complex.Gamma (z + 1)‖ ≤ R * G := by gcongr
      _ ≤ C * R := by
        dsimp [C]
        calc
          R * G = G * R := by ring
          _ ≤ G * (D + 1) * R := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_left (by linarith) (by linarith)) hG.le
  · unfold hughesYoungRegularizedGammaDigamma
    rw [norm_mul]
    calc
      ‖Complex.Gamma (z + 1)‖ *
          ‖z * Complex.digamma (z + 1) - 1‖ ≤
          G * (‖z‖ * ‖Complex.digamma (z + 1)‖ + 1) := by
        gcongr
        simpa only [norm_mul, norm_one] using
          norm_sub_le (z * Complex.digamma (z + 1)) 1
      _ ≤ G * (R * (D * R) + 1) := by gcongr
      _ ≤ C * R ^ 2 := by
        dsimp [C]
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hG.le
        nlinarith [sq_nonneg R, mul_self_le_mul_self (by linarith) hR1]

/-- Uniform boundedness of the trigamma series on the horizontal edges of
a positive strip. -/
theorem exists_uniform_norm_hughesYoungPolygamma_one_horizontal_far_le
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) :
    ∃ P : ℝ, 0 < P ∧ ∀ (y x : ℝ), 1 ≤ |y| →
      x ∈ Set.Icc c₀ c₁ →
      ‖hughesYoungPolygammaSeries 1
          (2 * ((x : ℂ) + (y : ℂ) * I))‖ ≤ P := by
  let a : ℝ := min (2 * c₀) 1
  let P : ℝ := 3 + a⁻¹ ^ 2
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min (by positivity) one_pos
  have hP : 0 < P := by
    dsimp [P]
    positivity
  refine ⟨P, hP, ?_⟩
  intro y x hy hx
  let w : ℂ := 2 * ((x : ℂ) + (y : ℂ) * I)
  have hwre : w.re = 2 * x := by simp [w]
  have hwim : w.im = 2 * y := by simp [w]
  have hwpos : 0 < w.re := by rw [hwre]; nlinarith [hc₀, hx.1]
  have hwimOne : 1 ≤ |w.im| := by
    rw [hwim, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hraw := norm_hughesYoungPolygammaSeries_le hwpos
    (j := 1) (by norm_num) hwimOne
  have hmin : a ≤ min w.re 1 := by
    dsimp [a]
    rw [hwre]
    exact min_le_min (by linarith [hx.1]) le_rfl
  have hinv : (min w.re 1)⁻¹ ≤ a⁻¹ := by
    exact (inv_le_inv₀ (lt_of_lt_of_le ha hmin) ha).2 hmin
  have himInv : |w.im|⁻¹ ≤ 1 :=
    (inv_le_one₀ (zero_lt_one.trans_le hwimOne)).2 hwimOne
  calc
    ‖hughesYoungPolygammaSeries 1 w‖ ≤
        (3 + (min w.re 1)⁻¹ ^ (1 + 1)) * |w.im|⁻¹ ^ 1 := hraw
    _ ≤ (3 + a⁻¹ ^ 2) * 1 := by
      gcongr
      simpa using himInv
    _ = P := by simp [P]

/-- The trigamma factor is uniformly bounded on the entire horizontal strip.
For small ordinate this is compactness of the holomorphic polygamma series;
for large ordinate it is the explicit series estimate above. -/
theorem exists_uniform_norm_hughesYoungPolygamma_one_horizontal_le
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) :
    ∃ P : ℝ, 0 < P ∧ ∀ (y x : ℝ),
      x ∈ Set.Icc c₀ c₁ →
      ‖hughesYoungPolygammaSeries 1
          (2 * ((x : ℂ) + (y : ℂ) * I))‖ ≤ P := by
  obtain ⟨Pfar, hPfar, hfar⟩ :=
    exists_uniform_norm_hughesYoungPolygamma_one_horizontal_far_le
      (c₀ := c₀) (c₁ := c₁) hc₀
  let arg : ℝ × ℝ → ℂ := fun z =>
    2 * ((z.1 : ℂ) + (z.2 : ℂ) * I)
  let f : ℝ × ℝ → ℝ := fun z =>
    ‖hughesYoungPolygammaSeries 1 (arg z)‖
  have harg : Continuous arg := by
    dsimp only [arg]
    fun_prop
  have hf : ContinuousOn f (Set.Icc c₀ c₁ ×ˢ Set.Icc (-1 : ℝ) 1) := by
    intro z hz
    have hzre : 0 < (arg z).re := by
      dsimp only [arg]
      norm_num [mul_re, add_re]
      nlinarith [hc₀, hz.1.1]
    have hseries :=
      (hasDerivAt_hughesYoungPolygammaSeries 1 (by norm_num) hzre).continuousAt
    exact ((hseries.comp harg.continuousAt).norm).continuousWithinAt
  have hcompact : IsCompact (Set.Icc c₀ c₁ ×ˢ Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨Psmall, hPsmall⟩ := hcompact.bddAbove_image hf
  let P : ℝ := max Pfar (max 1 Psmall)
  have hP : 0 < P := hPfar.trans_le (le_max_left _ _)
  refine ⟨P, hP, ?_⟩
  intro y x hx
  by_cases hy : 1 ≤ |y|
  · exact (hfar y x hy hx).trans (le_max_left _ _)
  · have hyMem : y ∈ Set.Icc (-1 : ℝ) 1 :=
      abs_le.mp (le_of_lt (lt_of_not_ge hy))
    have hsmall : f (x, y) ≤ Psmall :=
      hPsmall ⟨(x, y), ⟨hx, hyMem⟩, rfl⟩
    exact hsmall.trans <|
      (le_max_right 1 Psmall).trans (le_max_right Pfar (max 1 Psmall))

set_option maxHeartbeats 1000000 in
/-- Uniform horizontal growth bound for the complete pole-cancelled beta
factor in equation (84). -/
theorem exists_norm_hughesYoungEquation84RegularizedBetaKernel_horizontal_le
    (CX COne : ℂ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t y : ℝ),
      ∀ x ∈ Set.Icc c₀ c₁,
        ‖hughesYoungEquation84RegularizedBetaKernel t
            ((x : ℂ) + (y : ℂ) * I) CX COne‖ ≤
          C * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) *
            (2 + |t| + c₁ + |y|) ^ 3 := by
  obtain ⟨G₂, hG₂, hGamma₂⟩ := exists_uniform_norm_Gamma_vertical_strip
    (a := 2 * c₀) (b := 2 * c₁) (by positivity)
  obtain ⟨J, hJ, hInv⟩ :=
    exists_norm_inv_Gamma_critical_horizontal_le
      (c₀ := c₀) (c₁ := c₁) hc₁
  obtain ⟨Dₚ, hDₚ, hDigammaP⟩ :=
    exists_uniform_norm_digamma_vertical_strip_linear
      (a := (1 / 2 : ℝ) + c₀) (b := (1 / 2 : ℝ) + c₁) (by linarith)
  obtain ⟨D₂, hD₂, hDigamma₂⟩ :=
    exists_uniform_norm_digamma_vertical_strip_linear
      (a := 2 * c₀) (b := 2 * c₁) (by positivity)
  obtain ⟨P, hP, hPoly⟩ :=
    exists_uniform_norm_hughesYoungPolygamma_one_horizontal_le
      (c₀ := c₀) (c₁ := c₁) hc₀
  obtain ⟨Gᵣ, hGᵣ, hReg⟩ :=
    exists_norm_hughesYoungRegularizedGamma_pair_horizontal_le
      hc₀ hc₁ hc
  let K : ℝ := Dₚ + 2 * D₂ + ‖CX‖ + ‖COne‖ + 1
  let B : ℝ := Gᵣ * (K + K ^ 2 + P)
  let C : ℝ := G₂ * J * B
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t y x hx
  let w : ℂ := (x : ℂ) + (y : ℂ) * I
  let p : ℂ := afeCriticalPoint t + w
  let z : ℂ := afeCriticalPoint t - w
  let R : ℝ := 2 + |t| + c₁ + |y|
  have hc₁0 : 0 ≤ c₁ := hc₀.le.trans hc
  have hR1 : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg t, abs_nonneg y]
  have hyR : 2 * |y| + 2 ≤ 2 * R := by
    dsimp [R]
    linarith [abs_nonneg t, abs_nonneg y]
  have htyR : |t + y| + 2 ≤ R := by
    dsimp [R]
    have htri : |t + y| ≤ |t| + |y| := abs_add_le t y
    linarith
  have hGamma₂w : ‖Complex.Gamma (2 * w)‖ ≤ G₂ := by
    have hEq : 2 * w = ((2 * x : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I := by
      dsimp [w]
      push_cast
      ring
    rw [hEq]
    exact hGamma₂ (2 * x) (2 * y) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hInvP : ‖(Complex.Gamma p)⁻¹‖ ≤
      J * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) := by
    dsimp [p, w]
    exact hInv t y x hx
  have hDigP : ‖Complex.digamma p‖ ≤ Dₚ * R := by
    have hpEq : p = (((1 / 2 : ℝ) + x : ℝ) : ℂ) +
        ((t + y : ℝ) : ℂ) * I := by
      dsimp [p, w, afeCriticalPoint]
      push_cast
      ring
    rw [hpEq]
    exact (hDigammaP ((1 / 2 : ℝ) + x) (t + y)
      ⟨by linarith [hx.1], by linarith [hx.2]⟩).trans
        (mul_le_mul_of_nonneg_left htyR hDₚ.le)
  have hDig₂w : ‖Complex.digamma (2 * w)‖ ≤ 2 * D₂ * R := by
    have hEq : 2 * w = ((2 * x : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I := by
      dsimp [w]
      push_cast
      ring
    rw [hEq]
    calc
      ‖Complex.digamma (((2 * x : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I)‖ ≤
          D₂ * (|2 * y| + 2) :=
        hDigamma₂ (2 * x) (2 * y) ⟨by linarith [hx.1], by linarith [hx.2]⟩
      _ ≤ D₂ * (2 * R) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
      _ = 2 * D₂ * R := by ring
  have hRegPair := hReg t y x hx
  dsimp only [z, R] at hRegPair
  have hRegGamma : ‖hughesYoungRegularizedGamma z‖ ≤ Gᵣ * R := by
    simpa only [z, R] using hRegPair.1
  have hRegDigamma : ‖hughesYoungRegularizedGammaDigamma z‖ ≤
      Gᵣ * R ^ 2 := by
    simpa only [z, R] using hRegPair.2
  have hTrigamma : ‖hughesYoungPolygammaSeries 1 (2 * w)‖ ≤ P := by
    dsimp [w]
    exact hPoly y x hx
  let U : ℂ := -Complex.digamma (2 * w) + CX
  let V : ℂ := Complex.digamma p - Complex.digamma (2 * w) + COne
  have hU : ‖U‖ ≤ K * R := by
    calc
      ‖U‖ = ‖-Complex.digamma (2 * w) + CX‖ := by rfl
      _ ≤ ‖-Complex.digamma (2 * w)‖ + ‖CX‖ := norm_add_le _ _
      _ = ‖Complex.digamma (2 * w)‖ + ‖CX‖ := by rw [norm_neg]
      _ ≤ 2 * D₂ * R + ‖CX‖ := by gcongr
      _ ≤ K * R := by
        dsimp [K]
        nlinarith [hDₚ, hD₂, hR1, norm_nonneg CX, norm_nonneg COne]
  have hV : ‖V‖ ≤ K * R := by
    have hsub : ‖Complex.digamma p - Complex.digamma (2 * w)‖ ≤
        ‖Complex.digamma p‖ + ‖Complex.digamma (2 * w)‖ := norm_sub_le _ _
    calc
      ‖V‖ = ‖(Complex.digamma p - Complex.digamma (2 * w)) + COne‖ := by rfl
      _ ≤ ‖Complex.digamma p - Complex.digamma (2 * w)‖ + ‖COne‖ :=
        norm_add_le _ _
      _ ≤ (‖Complex.digamma p‖ + ‖Complex.digamma (2 * w)‖) +
          ‖COne‖ := by linarith
      _ ≤ Dₚ * R + 2 * D₂ * R + ‖COne‖ := by
        exact add_le_add (add_le_add hDigP hDig₂w) le_rfl
      _ ≤ K * R := by
        dsimp [K]
        nlinarith [hDₚ, hD₂, hR1, norm_nonneg CX, norm_nonneg COne]
  have hInside :
      ‖hughesYoungRegularizedGammaDigamma z * V +
          hughesYoungRegularizedGamma z *
            (U * V + hughesYoungPolygammaSeries 1 (2 * w))‖ ≤
        B * R ^ 3 := by
    calc
      _ ≤ ‖hughesYoungRegularizedGammaDigamma z‖ * ‖V‖ +
          ‖hughesYoungRegularizedGamma z‖ *
            (‖U‖ * ‖V‖ + ‖hughesYoungPolygammaSeries 1 (2 * w)‖) := by
        calc
          _ ≤ ‖hughesYoungRegularizedGammaDigamma z * V‖ +
              ‖hughesYoungRegularizedGamma z *
                (U * V + hughesYoungPolygammaSeries 1 (2 * w))‖ := norm_add_le _ _
          _ = ‖hughesYoungRegularizedGammaDigamma z‖ * ‖V‖ +
              ‖hughesYoungRegularizedGamma z‖ *
                ‖U * V + hughesYoungPolygammaSeries 1 (2 * w)‖ := by
            rw [norm_mul, norm_mul]
          _ ≤ _ := by
            gcongr
            calc
              ‖U * V + hughesYoungPolygammaSeries 1 (2 * w)‖ ≤
                  ‖U * V‖ + ‖hughesYoungPolygammaSeries 1 (2 * w)‖ :=
                norm_add_le _ _
              _ = ‖U‖ * ‖V‖ + ‖hughesYoungPolygammaSeries 1 (2 * w)‖ := by
                rw [norm_mul]
      _ ≤ (Gᵣ * R ^ 2) * (K * R) +
          (Gᵣ * R) * ((K * R) * (K * R) + P) := by gcongr
      _ ≤ B * R ^ 3 := by
        dsimp [B]
        have hR2 : 1 ≤ R ^ 2 := by nlinarith [sq_nonneg R]
        have hR3 : R ≤ R ^ 3 := by
          calc
            R ≤ R * R ^ 2 := le_mul_of_one_le_right (by linarith) hR2
            _ = R ^ 3 := by ring
        have hPR : P * R ≤ P * R ^ 3 :=
          mul_le_mul_of_nonneg_left hR3 hP.le
        ring_nf at hPR ⊢
        nlinarith
  change ‖Complex.Gamma (2 * w) / Complex.Gamma p *
      (hughesYoungRegularizedGammaDigamma z * V +
        hughesYoungRegularizedGamma z *
          (U * V + hughesYoungPolygammaSeries 1 (2 * w)))‖ ≤
    C * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) * R ^ 3
  simp only [div_eq_mul_inv, norm_mul]
  calc
    ‖Complex.Gamma (2 * w)‖ * ‖(Complex.Gamma p)⁻¹‖ *
          ‖hughesYoungRegularizedGammaDigamma z * V +
            hughesYoungRegularizedGamma z *
              (U * V + hughesYoungPolygammaSeries 1 (2 * w))‖ ≤
        G₂ * (J * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2)) *
          (B * R ^ 3) := by gcongr
    _ = C * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) * R ^ 3 := by
      dsimp [C]
      ring

/-- The polynomial part of the regularized equation-(84) core has degree six
in a common norm majorant. -/
theorem norm_hughesYoungEquation84CorePolynomial_le
    {p q : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hp : ‖p‖ ≤ R) (hOneP : ‖1 - p‖ ≤ R) (hq : ‖q‖ ≤ R) :
    ‖(p * (1 - p)) ^ 2 * q ^ 2‖ ≤ R ^ 6 := by
  simp only [norm_mul, norm_pow]
  calc
    (‖p‖ * ‖1 - p‖) ^ 2 * ‖q‖ ^ 2 ≤ (R * R) ^ 2 * R ^ 2 := by
      gcongr
    _ = R ^ 6 := by ring

set_option maxHeartbeats 1000000 in
/-- The analytic core of the regularized equation-(84) archimedean kernel
decays Gaussianly on both horizontal sides of the contour rectangle. -/
theorem exists_norm_hughesYoungEquation84RegularizedContourKernelCore_horizontal_le
    (t : ℝ) (CX COne : ℂ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ), 1 ≤ |y| → |t| + 1 ≤ |y| →
      ∀ x ∈ Set.Icc c₀ c₁,
        ‖hughesYoungEquation84RegularizedContourKernelCore t
            ((x : ℂ) + (y : ℂ) * I) CX COne‖ ≤
          C * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
            (2 + |t| + c₁ + |y|) ^ 9 := by
  obtain ⟨B, hB, hBeta⟩ :=
    exists_norm_hughesYoungEquation84RegularizedBetaKernel_horizontal_le
      CX COne hc₀ hc₁ hc
  obtain ⟨G, hG, hGammaR⟩ :=
    exists_uniform_norm_GammaR_vertical_strip
      (c₀ := c₀) (c₁ := c₁) hc₀
  let A : ℝ := ‖(afePoleNormalization t)⁻¹‖ *
    ‖(afeGammaNormalization t)⁻¹‖
  let C : ℝ := G ^ 4 * A * B * Real.exp (1 / 2)
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos
      (norm_pos_iff.mpr (inv_ne_zero (afePoleNormalization_ne_zero t)))
      (norm_pos_iff.mpr (inv_ne_zero (afeGammaNormalization_ne_zero t)))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro y hy hty x hx
  let w : ℂ := (x : ℂ) + (y : ℂ) * I
  let p : ℂ := afeCriticalPoint t + w
  let q : ℂ := afeCriticalPoint (-t) + w
  let R : ℝ := 2 + |t| + c₁ + |y|
  have hc₁0 : 0 ≤ c₁ := hc₀.le.trans hc
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have hx0 : 0 ≤ x := hc₀.le.trans hx.1
  have hpNorm : ‖p‖ ≤ R := by
    have hxmem : x ∈ Set.uIcc (-c₁) c₁ := by
      rw [uIcc_of_le (by linarith)]
      exact ⟨by linarith, hx.2⟩
    have h := one_add_norm_afeCriticalPoint_add_horizontal_abs_le
      t c₁ y x hc₁0 hxmem
    dsimp [p, w, R]
    linarith
  have hqNorm : ‖q‖ ≤ R := by
    have hxmem : x ∈ Set.uIcc (-c₁) c₁ := by
      rw [uIcc_of_le (by linarith)]
      exact ⟨by linarith, hx.2⟩
    have h := one_add_norm_afeCriticalPoint_add_horizontal_abs_le
      (-t) c₁ y x hc₁0 hxmem
    simp only [abs_neg] at h
    dsimp [q, w, R]
    linarith
  have hOneP : ‖1 - p‖ ≤ R := by
    calc
      ‖1 - p‖ ≤ 1 + ‖p‖ := by simpa using norm_sub_le (1 : ℂ) p
      _ ≤ R := by
        have hxmem : x ∈ Set.uIcc (-c₁) c₁ := by
          rw [uIcc_of_le (by linarith)]
          exact ⟨by linarith, hx.2⟩
        simpa only [p, w, R] using
          one_add_norm_afeCriticalPoint_add_horizontal_abs_le
            t c₁ y x hc₁0 hxmem
  have hGammaP : ‖Complex.Gammaℝ p‖ ≤ G := by
    have hpEq : p = (((1 / 2 : ℝ) + x : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I := by
      dsimp [p, w, afeCriticalPoint]
      push_cast
      ring
    rw [hpEq]
    exact hGammaR x (t + y) hx
  have hGammaQ : ‖Complex.Gammaℝ q‖ ≤ G := by
    have hqEq : q = (((1 / 2 : ℝ) + x : ℝ) : ℂ) + ((-t + y : ℝ) : ℂ) * I := by
      dsimp [q, w, afeCriticalPoint]
      push_cast
      ring
    rw [hqEq]
    exact hGammaR x (-t + y) hx
  have hwNorm : 1 ≤ ‖w‖ := by
    have him := Complex.abs_im_le_norm w
    have himEq : |w.im| = |y| := by simp [w]
    rw [himEq] at him
    exact hy.trans him
  have hwInv : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (zero_lt_one.trans_le hwNorm)).2 hwNorm
  have hGauss : ‖Complex.exp (100 * w ^ 2)‖ ≤
      Real.exp (100 * c₁ ^ 2 - 100 * y ^ 2) := by
    dsimp [w]
    exact norm_hughesYoungGaussian_horizontal_le hx0 hx.2
  have hPoly : ‖(p * (1 - p)) ^ 2 * q ^ 2‖ ≤ R ^ 6 := by
    exact norm_hughesYoungEquation84CorePolynomial_le hR0 hpNorm hOneP hqNorm
  have htyOne : 1 ≤ |t + y| := by
    have hrev : |y| ≤ |t + y| + |t| := by
      have hraw := abs_add_le (t + y) (-t)
      rw [show t + y + -t = y by ring, abs_neg] at hraw
      exact hraw
    linarith
  have hBetaTerm :
      ‖hughesYoungEquation84RegularizedBetaKernel t w CX COne‖ ≤
        B * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) * R ^ 3 := by
    dsimp [w, R]
    exact hBeta t y x hx
  have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
  have htPlus : |t + y| ≤ 2 * |y| := by
    calc
      |t + y| ≤ |t| + |y| := abs_add_le _ _
      _ ≤ 2 * |y| := by linarith
  have hexponent : ((Real.pi * (t + y)) ^ 2 + 1) / 2 ≤
      40 * y ^ 2 + 1 / 2 := by
    have habs : |Real.pi * (t + y)| ≤ 8 * |y| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      calc
        Real.pi * |t + y| ≤ 4 * (2 * |y|) := by gcongr
        _ = 8 * |y| := by ring
    have hsq := mul_self_le_mul_self
      (abs_nonneg (Real.pi * (t + y))) habs
    have hleft : |Real.pi * (t + y)| * |Real.pi * (t + y)| =
        (Real.pi * (t + y)) ^ 2 := by
      calc
        |Real.pi * (t + y)| * |Real.pi * (t + y)| =
            |Real.pi * (t + y)| ^ 2 := by ring
        _ = (Real.pi * (t + y)) ^ 2 := sq_abs _
    have hright : 8 * |y| * (8 * |y|) = 64 * y ^ 2 := by
      calc
        8 * |y| * (8 * |y|) = 64 * |y| ^ 2 := by ring
        _ = 64 * y ^ 2 := by rw [sq_abs]
    rw [hleft, hright] at hsq
    calc
      ((Real.pi * (t + y)) ^ 2 + 1) / 2 ≤ (64 * y ^ 2 + 1) / 2 := by
        gcongr
      _ ≤ 40 * y ^ 2 + 1 / 2 := by nlinarith [sq_nonneg y]
  have hExpProduct :
      Real.exp (100 * c₁ ^ 2 - 100 * y ^ 2) *
          Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) ≤
        Real.exp (1 / 2) * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  rw [hughesYoungEquation84RegularizedContourKernelCore_eq_expanded]
  simp only [div_eq_mul_inv, norm_mul, norm_pow]
  have hGauss' :
      ‖Complex.exp (100 * (((x : ℂ) + (y : ℂ) * I) ^ 2))‖ ≤
        Real.exp (100 * c₁ ^ 2 - 100 * y ^ 2) := by
    simpa only [w] using hGauss
  have hPoly' :
      (‖afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I)‖ *
          ‖1 - (afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I))‖) ^ 2 *
        ‖afeCriticalPoint (-t) + ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤
        R ^ 6 := by
    simpa only [p, q, w, norm_mul, norm_pow] using hPoly
  have hGammaP' :
      ‖Complex.Gammaℝ (afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I))‖ ≤ G := by
    simpa only [p, w] using hGammaP
  have hGammaQ' :
      ‖Complex.Gammaℝ (afeCriticalPoint (-t) + ((x : ℂ) + (y : ℂ) * I))‖ ≤ G := by
    simpa only [q, w] using hGammaQ
  have hwInv' : ‖((x : ℂ) + (y : ℂ) * I)⁻¹‖ ≤ 1 := by
    simpa only [w] using hwInv
  have hBetaTerm' :
      ‖hughesYoungEquation84RegularizedBetaKernel t
          ((x : ℂ) + (y : ℂ) * I) CX COne‖ ≤
        B * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) * R ^ 3 := by
    simpa only [w] using hBetaTerm
  have hGaussPoly' :
      (‖Complex.exp (100 * (((x : ℂ) + (y : ℂ) * I) ^ 2))‖ *
          (‖afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I)‖ *
            ‖1 - (afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I))‖) ^ 2) *
          ‖afeCriticalPoint (-t) + ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤
        Real.exp (100 * c₁ ^ 2 - 100 * y ^ 2) * R ^ 6 := by
    rw [mul_assoc]
    exact mul_le_mul hGauss' hPoly' (by positivity) (Real.exp_pos _).le
  have hRest :
      ‖Complex.Gammaℝ (afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I))‖ ^ 2 *
          ‖Complex.Gammaℝ (afeCriticalPoint (-t) + ((x : ℂ) + (y : ℂ) * I))‖ ^ 2 *
          ‖(afePoleNormalization t)⁻¹‖ *
          ‖((x : ℂ) + (y : ℂ) * I)⁻¹‖ *
          ‖(afeGammaNormalization t)⁻¹‖ *
          ‖hughesYoungEquation84RegularizedBetaKernel t
            ((x : ℂ) + (y : ℂ) * I) CX COne‖ ≤
        G ^ 2 * G ^ 2 * ‖(afePoleNormalization t)⁻¹‖ * 1 *
          ‖(afeGammaNormalization t)⁻¹‖ *
          (B * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) * R ^ 3) := by
    gcongr
  calc
    _ = ((‖Complex.exp (100 * (((x : ℂ) + (y : ℂ) * I) ^ 2))‖ *
          (‖afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I)‖ *
            ‖1 - (afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I))‖) ^ 2) *
          ‖afeCriticalPoint (-t) + ((x : ℂ) + (y : ℂ) * I)‖ ^ 2) *
        (‖Complex.Gammaℝ (afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I))‖ ^ 2 *
          ‖Complex.Gammaℝ (afeCriticalPoint (-t) + ((x : ℂ) + (y : ℂ) * I))‖ ^ 2 *
          ‖(afePoleNormalization t)⁻¹‖ *
          ‖((x : ℂ) + (y : ℂ) * I)⁻¹‖ *
          ‖(afeGammaNormalization t)⁻¹‖ *
          ‖hughesYoungEquation84RegularizedBetaKernel t
            ((x : ℂ) + (y : ℂ) * I) CX COne‖) := by ac_rfl
    _ ≤ (Real.exp (100 * c₁ ^ 2 - 100 * y ^ 2) * R ^ 6) *
        (G ^ 2 * G ^ 2 * ‖(afePoleNormalization t)⁻¹‖ * 1 *
          ‖(afeGammaNormalization t)⁻¹‖ *
          (B * Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2) * R ^ 3)) := by
      exact mul_le_mul hGaussPoly' hRest (by positivity) (by positivity)
    _ = G ^ 4 * A * B *
        (Real.exp (100 * c₁ ^ 2 - 100 * y ^ 2) *
          Real.exp (((Real.pi * (t + y)) ^ 2 + 1) / 2)) * R ^ 9 := by
      dsimp [A]
      ring
    _ ≤ G ^ 4 * A * B *
        (Real.exp (1 / 2) * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2)) *
          R ^ 9 := by gcongr
    _ = C * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) * R ^ 9 := by
      dsimp [C]
      ring

/-- Combining an eighth-degree auxiliary factor with a ninth-degree analytic
core produces the seventeenth-degree horizontal envelope. -/
theorem mul_le_hughesYoung_degree_seventeen
    {a b C E R : ℝ}
    (ha : a ≤ 625 * R ^ 8) (hb : b ≤ C * E * R ^ 9)
    (hb0 : 0 ≤ b) :
    a * b ≤ (625 * C) * E * R ^ 17 := by
  calc
    a * b ≤ (625 * R ^ 8) * (C * E * R ^ 9) :=
      mul_le_mul ha hb hb0 (by positivity)
    _ = (625 * C) * E * R ^ 17 := by ring

/-- The complete regularized equation-(84) kernel is the analytic core times
the prescribed degree-eight auxiliary zero, hence has the same Gaussian decay
with polynomial degree seventeen. -/
theorem exists_norm_hughesYoungEquation84RegularizedContourKernel_horizontal_le
    (t : ℝ) (CX COne : ℂ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ), 1 ≤ |y| → |t| + 1 ≤ |y| →
      ∀ x ∈ Set.Icc c₀ c₁,
        ‖hughesYoungEquation84RegularizedContourKernel t
            ((x : ℂ) + (y : ℂ) * I) CX COne‖ ≤
          C * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
            (2 + |t| + c₁ + |y|) ^ 17 := by
  obtain ⟨C, hC, hCore⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernelCore_horizontal_le
      t CX COne hc₀ hc₁ hc
  refine ⟨625 * C, by positivity, ?_⟩
  intro y hy hty x hx
  let w : ℂ := (x : ℂ) + (y : ℂ) * I
  let R : ℝ := 2 + |t| + c₁ + |y|
  have hx0 : 0 ≤ x := hc₀.le.trans hx.1
  have hR1 : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg t, abs_nonneg y, hc₀.le.trans hc]
  have hwNormUpper : ‖w‖ ≤ R := by
    calc
      ‖w‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * I‖ := by
        dsimp [w]
        exact norm_add_le _ _
      _ = |x| + |y| := by simp [Real.norm_eq_abs]
      _ = x + |y| := by rw [abs_of_nonneg hx0]
      _ ≤ c₁ + |y| := by
        simpa [add_comm] using add_le_add_right hx.2 |y|
      _ ≤ R := by
        dsimp [R]
        linarith [abs_nonneg t]
  have hAux : ‖hughesYoungAuxiliaryZero w‖ ≤ 625 * R ^ 8 :=
    norm_hughesYoungAuxiliaryZero_le_polynomial hR1 hwNormUpper
  have hAux' :
      ‖hughesYoungAuxiliaryZero ((x : ℂ) + (y : ℂ) * I)‖ ≤
        625 * (2 + |t| + c₁ + |y|) ^ 8 := by
    simpa only [w, R] using hAux
  have hCore' :
      ‖hughesYoungEquation84RegularizedContourKernelCore t
          ((x : ℂ) + (y : ℂ) * I) CX COne‖ ≤
        C * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
          (2 + |t| + c₁ + |y|) ^ 9 := hCore y hy hty x hx
  rw [hughesYoungEquation84RegularizedContourKernel_eq_auxiliary_mul_core,
    norm_mul]
  exact mul_le_hughesYoung_degree_seventeen
    hAux' hCore' (norm_nonneg _)

/-- The non-archimedean and reduced Mellin factors outside the regularized
beta kernel have height-independent norm on a fixed compact real-part
interval. -/
theorem exists_uniform_norm_hughesYoungCentralOuterFactor
    (T t : ℝ) (h k r : ℕ) (A : ℂ) {c₀ c₁ : ℝ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (y x : ℝ), x ∈ Set.Icc c₀ c₁ →
      ‖A * (hughesYoungReducedMellinStaticComplex T t h k
          ((x : ℂ) + (y : ℂ) * I) *
        hughesYoungCentralShiftPower r ((x : ℂ) + (y : ℂ) * I))‖ ≤ C := by
  let F : ℝ → ℝ := fun x =>
    ‖A * (hughesYoungReducedMellinStaticComplex T t h k (x : ℂ) *
      hughesYoungCentralShiftPower r (x : ℂ))‖
  have hFcont : Continuous F := by
    dsimp [F, hughesYoungReducedMellinStaticComplex,
      hughesYoungCentralShiftPower]
    fun_prop
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hFcont.continuousOn
  refine ⟨max 1 M, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro y x hx
  have hheight :
      ‖A * (hughesYoungReducedMellinStaticComplex T t h k
          ((x : ℂ) + (y : ℂ) * I) *
        hughesYoungCentralShiftPower r ((x : ℂ) + (y : ℂ) * I))‖ = F x := by
    have hexp (s : ℂ) (L : ℝ) :
        ‖Complex.exp ((s + ((x : ℂ) + (y : ℂ) * I)) * (L : ℂ))‖ =
          ‖Complex.exp ((s + (x : ℂ)) * (L : ℂ))‖ := by
      simp only [Complex.norm_exp]
      congr 1
      simp
    have hshift :
        ‖Complex.exp ((-2 * ((x : ℂ) + (y : ℂ) * I)) *
          (Real.log (r : ℝ) : ℂ))‖ =
          ‖Complex.exp ((-2 * (x : ℂ)) *
            (Real.log (r : ℝ) : ℂ))‖ := by
      rw [Complex.natCast_log]
      have hlogr : (Complex.log (r : ℂ)).im = 0 := by
        rw [Complex.log_im]
        exact Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg r)
      simp [Complex.norm_exp, hlogr]
    dsimp [F, hughesYoungReducedMellinStaticComplex,
      hughesYoungCentralShiftPower]
    simp only [norm_mul]
    rw [hexp (afeCriticalPoint t)
      (Real.log (hughesYoungReducedLeft h k : ℝ))]
    rw [hexp (afeCriticalPoint (-t))
      (Real.log (hughesYoungReducedRight h k : ℝ))]
    rw [hshift]
  rw [hheight]
  exact (hM ⟨x, hx, rfl⟩).trans (le_max_right 1 M)

set_option maxHeartbeats 1000000 in
/-- Each positive equation-(84) modulus summand has a uniform
Gaussian-polynomial horizontal bound. -/
theorem exists_norm_hughesYoungEquation84PositiveContourTerm_horizontal_le
    (T t : ℝ) (h k a b r q : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ), 1 ≤ |y| → |t| + 1 ≤ |y| →
      ∀ x ∈ Set.Icc c₀ c₁,
        ‖hughesYoungEquation84PositiveContourTerm T t h k a b r q
            ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
            (2 + |t| + c₁ + |y|) ^ 17 := by
  let CX : ℂ := (Real.log r : ℂ) +
    dfiEquation27LogConstant b (dfiReducedDenominator b q)
  let COne : ℂ := (Real.log r : ℂ) +
    dfiEquation27LogConstant a (dfiReducedDenominator a q)
  let A : ℂ := ((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q
  obtain ⟨K, hK, hOuter⟩ := exists_uniform_norm_hughesYoungCentralOuterFactor
    T t h k r A (c₀ := c₀) (c₁ := c₁)
  obtain ⟨B, hB, hKernel⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_horizontal_le
      t CX COne hc₀ hc₁ hc
  refine ⟨K * B, mul_pos hK hB, ?_⟩
  intro y hy hty x hx
  have hO := hOuter y x hx
  have hA := hKernel y hy hty x hx
  have hO' :
      ‖(((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b r q) *
          (hughesYoungReducedMellinStaticComplex T t h k
              ((x : ℂ) + (y : ℂ) * I) *
            hughesYoungCentralShiftPower r ((x : ℂ) + (y : ℂ) * I))‖ ≤ K := by
    simpa only [A] using hO
  have hA' :
      ‖hughesYoungEquation84RegularizedContourKernel t
          ((x : ℂ) + (y : ℂ) * I)
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q))
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q))‖ ≤
        B * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
          (2 + |t| + c₁ + |y|) ^ 17 := by
    simpa only [CX, COne] using hA
  rw [hughesYoungEquation84PositiveContourTerm_eq_outer_mul_kernel, norm_mul]
  calc
    _ ≤ K * (B * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
        (2 + |t| + c₁ + |y|) ^ 17) :=
      mul_le_mul hO' hA' (by positivity) hK.le
    _ = (K * B) * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
        (2 + |t| + c₁ + |y|) ^ 17 := by ac_rfl

set_option maxHeartbeats 1000000 in
/-- The coordinate-swapped negative equation-(84) summand satisfies the
same horizontal envelope. -/
theorem exists_norm_hughesYoungEquation84NegativeContourTerm_horizontal_le
    (T t : ℝ) (h k a b r q : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ), 1 ≤ |y| → |t| + 1 ≤ |y| →
      ∀ x ∈ Set.Icc c₀ c₁,
        ‖hughesYoungEquation84NegativeContourTerm T t h k a b r q
            ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
            (2 + |t| + c₁ + |y|) ^ 17 := by
  let CX : ℂ := (Real.log r : ℂ) +
    dfiEquation27LogConstant a (dfiReducedDenominator a q)
  let COne : ℂ := (Real.log r : ℂ) +
    dfiEquation27LogConstant b (dfiReducedDenominator b q)
  let A : ℂ := ((b : ℂ) * a)⁻¹ *
    dfiEquation27ArithmeticCoefficient b a r q
  obtain ⟨K, hK, hOuter⟩ := exists_uniform_norm_hughesYoungCentralOuterFactor
    T t h k r A (c₀ := c₀) (c₁ := c₁)
  obtain ⟨B, hB, hKernel⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_horizontal_le
      (-t) CX COne hc₀ hc₁ hc
  refine ⟨K * B, mul_pos hK hB, ?_⟩
  intro y hy hty x hx
  have hO := hOuter y x hx
  have hA :
      ‖hughesYoungEquation84RegularizedContourKernel (-t)
          ((x : ℂ) + (y : ℂ) * I) CX COne‖ ≤
        B * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
          (2 + |t| + c₁ + |y|) ^ 17 := by
    simpa only [abs_neg] using
      hKernel y hy (by simpa only [abs_neg] using hty) x hx
  have hO' :
      ‖(((b : ℂ) * a)⁻¹ * dfiEquation27ArithmeticCoefficient b a r q) *
          (hughesYoungReducedMellinStaticComplex T t h k
              ((x : ℂ) + (y : ℂ) * I) *
            hughesYoungCentralShiftPower r ((x : ℂ) + (y : ℂ) * I))‖ ≤ K := by
    simpa only [A] using hO
  have hA' :
      ‖hughesYoungEquation84RegularizedContourKernel (-t)
          ((x : ℂ) + (y : ℂ) * I)
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q))
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q))‖ ≤
        B * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
          (2 + |t| + c₁ + |y|) ^ 17 := by
    simpa only [CX, COne] using hA
  rw [hughesYoungEquation84NegativeContourTerm_eq_outer_mul_kernel, norm_mul]
  calc
    _ ≤ K * (B * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
        (2 + |t| + c₁ + |y|) ^ 17) := by
      exact mul_le_mul hO' hA' (by positivity) hK.le
    _ = (K * B) * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
        (2 + |t| + c₁ + |y|) ^ 17 := by ac_rfl

/-- A seventeenth-degree polynomial cannot overcome the Gaussian supplied by
the completed-zeta test factor. -/
theorem tendsto_const_mul_exp_sub_sixty_sq_mul_shift_pow_seventeen
    (C A B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    Tendsto (fun H : ℝ =>
      C * Real.exp (A - 60 * H ^ 2) * (B + H) ^ 17) atTop (nhds 0) := by
  have hExp : Tendsto (fun H : ℝ => Real.exp (-(1 / 2 : ℝ) * H))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg
        (by norm_num : (-(1 / 2 : ℝ)) < 0))
  have hbaseRpow : Tendsto (fun H : ℝ =>
      H ^ (17 : ℝ) * Real.exp (-60 * H ^ 2)) atTop (nhds 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
      (by norm_num : (0 : ℝ) < 60) 17).tendsto_zero_of_tendsto hExp
  have hbase : Tendsto (fun H : ℝ =>
      H ^ 17 * Real.exp (-60 * H ^ 2)) atTop (nhds 0) := by
    simpa only [← Real.rpow_natCast] using hbaseRpow
  let D : ℝ := C * Real.exp A * 131072
  have hmajor : Tendsto (fun H : ℝ =>
      D * (H ^ 17 * Real.exp (-60 * H ^ 2))) atTop (nhds 0) := by
    simpa only [mul_zero] using hbase.const_mul D
  apply squeeze_zero'
    (show ∀ᶠ H : ℝ in atTop,
      0 ≤ C * Real.exp (A - 60 * H ^ 2) * (B + H) ^ 17 by
      filter_upwards [eventually_ge_atTop (max 1 B)] with H hH
      have hH0 : 0 ≤ H := zero_le_one.trans ((le_max_left 1 B).trans hH)
      exact mul_nonneg (mul_nonneg hC (Real.exp_pos _).le)
        (pow_nonneg (add_nonneg hB hH0) 17))
    (show ∀ᶠ H : ℝ in atTop,
      C * Real.exp (A - 60 * H ^ 2) * (B + H) ^ 17 ≤
        D * (H ^ 17 * Real.exp (-60 * H ^ 2)) by
      filter_upwards [eventually_ge_atTop (max 1 B)] with H hH
      have hH1 : 1 ≤ H := (le_max_left 1 B).trans hH
      have hHB : B ≤ H := (le_max_right 1 B).trans hH
      have hH0 : 0 ≤ H := zero_le_one.trans hH1
      have hshift : B + H ≤ 2 * H := by linarith
      have hpow : (B + H) ^ 17 ≤ 131072 * H ^ 17 := by
        calc
          (B + H) ^ 17 ≤ (2 * H) ^ 17 := by gcongr
          _ = 131072 * H ^ 17 := by ring
      have hexp : Real.exp (A - 60 * H ^ 2) =
          Real.exp A * Real.exp (-60 * H ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      dsimp [D]
      calc
        C * (Real.exp A * Real.exp (-60 * H ^ 2)) * (B + H) ^ 17 ≤
            C * (Real.exp A * Real.exp (-60 * H ^ 2)) *
              (131072 * H ^ 17) := by gcongr
        _ = C * Real.exp A * 131072 *
              (H ^ 17 * Real.exp (-60 * H ^ 2)) := by ring)
  exact hmajor

/-- A common horizontal bound with absolute height makes the upper edge
of a finite rectangle vanish. -/
theorem tendsto_HIntegral_top_zero_of_central_horizontal_bound
    (f : ℂ → ℂ) (t c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ),
      1 ≤ |y| → |t| + 1 ≤ |y| → ∀ x ∈ Set.Icc c₀ c₁,
        ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
            (2 + |t| + c₁ + |y|) ^ 17) :
    Tendsto (fun H : ℝ => HIntegral f c₀ c₁ H) atTop (nhds 0) := by
  obtain ⟨C, hC, hCbound⟩ := hbound
  let envelope : ℝ → ℝ := fun H =>
    C * Real.exp (100 * c₁ ^ 2 - 60 * H ^ 2) *
      (2 + |t| + c₁ + H) ^ 17
  have henv : Tendsto envelope atTop (nhds 0) :=
    tendsto_const_mul_exp_sub_sixty_sq_mul_shift_pow_seventeen
      C (100 * c₁ ^ 2) (2 + |t| + c₁) hC.le (by
        have hc₁ : 0 < c₁ := hc₀.trans_le hc
        positivity)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ H : ℝ in atTop,
      ‖HIntegral f c₀ c₁ H‖ ≤ envelope H * |c₁ - c₀| by
      filter_upwards [eventually_ge_atTop (max 1 (|t| + 1))] with H hH
      have hH1 : 1 ≤ H := (le_max_left _ _).trans hH
      have hHt : |t| + 1 ≤ H := (le_max_right _ _).trans hH
      have hH0 : 0 ≤ H := zero_le_one.trans hH1
      unfold HIntegral
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Set.Icc c₀ c₁ := by
        rw [← uIcc_of_le hc]
        exact Set.uIoc_subset_uIcc hx
      have hpoint := hCbound H (by simpa [abs_of_nonneg hH0] using hH1)
        (by simpa [abs_of_nonneg hH0] using hHt) x hx'
      simpa [envelope, abs_of_nonneg hH0, add_assoc] using hpoint)
  simpa using henv.mul_const |c₁ - c₀|

/-- The same absolute-height bound makes the lower rectangle edge vanish. -/
theorem tendsto_HIntegral_bottom_zero_of_central_horizontal_bound
    (f : ℂ → ℂ) (t c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ),
      1 ≤ |y| → |t| + 1 ≤ |y| → ∀ x ∈ Set.Icc c₀ c₁,
        ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
            (2 + |t| + c₁ + |y|) ^ 17) :
    Tendsto (fun H : ℝ => HIntegral f c₀ c₁ (-H)) atTop (nhds 0) := by
  obtain ⟨C, hC, hCbound⟩ := hbound
  let envelope : ℝ → ℝ := fun H =>
    C * Real.exp (100 * c₁ ^ 2 - 60 * H ^ 2) *
      (2 + |t| + c₁ + H) ^ 17
  have henv : Tendsto envelope atTop (nhds 0) :=
    tendsto_const_mul_exp_sub_sixty_sq_mul_shift_pow_seventeen
      C (100 * c₁ ^ 2) (2 + |t| + c₁) hC.le (by
        have hc₁ : 0 < c₁ := hc₀.trans_le hc
        positivity)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ H : ℝ in atTop,
      ‖HIntegral f c₀ c₁ (-H)‖ ≤ envelope H * |c₁ - c₀| by
      filter_upwards [eventually_ge_atTop (max 1 (|t| + 1))] with H hH
      have hH1 : 1 ≤ H := (le_max_left _ _).trans hH
      have hHt : |t| + 1 ≤ H := (le_max_right _ _).trans hH
      have hH0 : 0 ≤ H := zero_le_one.trans hH1
      unfold HIntegral
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Set.Icc c₀ c₁ := by
        rw [← uIcc_of_le hc]
        exact Set.uIoc_subset_uIcc hx
      have hpoint := hCbound (-H)
        (by simpa [abs_of_nonneg hH0] using hH1)
        (by simpa [abs_of_nonneg hH0] using hHt) x hx'
      simpa [envelope, abs_of_nonneg hH0, add_assoc] using hpoint)
  simpa using henv.mul_const |c₁ - c₀|

/-- The positive equation-(84) horizontal edges vanish. -/
theorem tendsto_hIntegral_hughesYoungEquation84Positive_top_zero
    (T t : ℝ) (h k a b r q : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ => HIntegral
      (hughesYoungEquation84PositiveContourTerm T t h k a b r q)
      c₀ c₁ H) atTop (nhds 0) :=
  tendsto_HIntegral_top_zero_of_central_horizontal_bound
    _ t c₀ c₁ hc₀ hc
      (exists_norm_hughesYoungEquation84PositiveContourTerm_horizontal_le
        T t h k a b r q hc₀ hc₁ hc)

/-- The lower positive equation-(84) horizontal edge vanishes. -/
theorem tendsto_hIntegral_hughesYoungEquation84Positive_bottom_zero
    (T t : ℝ) (h k a b r q : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ => HIntegral
      (hughesYoungEquation84PositiveContourTerm T t h k a b r q)
      c₀ c₁ (-H)) atTop (nhds 0) :=
  tendsto_HIntegral_bottom_zero_of_central_horizontal_bound
    _ t c₀ c₁ hc₀ hc
      (exists_norm_hughesYoungEquation84PositiveContourTerm_horizontal_le
        T t h k a b r q hc₀ hc₁ hc)

/-- The negative equation-(84) horizontal edges vanish. -/
theorem tendsto_hIntegral_hughesYoungEquation84Negative_top_zero
    (T t : ℝ) (h k a b r q : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ => HIntegral
      (hughesYoungEquation84NegativeContourTerm T t h k a b r q)
      c₀ c₁ H) atTop (nhds 0) :=
  tendsto_HIntegral_top_zero_of_central_horizontal_bound
    _ t c₀ c₁ hc₀ hc
      (exists_norm_hughesYoungEquation84NegativeContourTerm_horizontal_le
        T t h k a b r q hc₀ hc₁ hc)

/-- The lower negative equation-(84) horizontal edge vanishes. -/
theorem tendsto_hIntegral_hughesYoungEquation84Negative_bottom_zero
    (T t : ℝ) (h k a b r q : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ => HIntegral
      (hughesYoungEquation84NegativeContourTerm T t h k a b r q)
      c₀ c₁ (-H)) atTop (nhds 0) :=
  tendsto_HIntegral_bottom_zero_of_central_horizontal_bound
    _ t c₀ c₁ hc₀ hc
      (exists_norm_hughesYoungEquation84NegativeContourTerm_horizontal_le
        T t h k a b r q hc₀ hc₁ hc)

/-- The abstract rectangle identity plus vanishing horizontal edges gives
equality of the two symmetric vertical contour limits. -/
theorem tendsto_vertical_sub_zero_of_boundaryRect
    (f : ℂ → ℂ) (c₀ c₁ : ℝ)
    (hrect : ∀ H : ℝ,
      (∫ x : ℝ in c₀..c₁, f ((x : ℂ) + (-H : ℂ) * I)) -
        (∫ x : ℝ in c₀..c₁, f ((x : ℂ) + (H : ℂ) * I)) +
        I • (∫ y : ℝ in -H..H, f ((c₁ : ℂ) + (y : ℂ) * I)) -
        I • (∫ y : ℝ in -H..H, f ((c₀ : ℂ) + (y : ℂ) * I)) = 0)
    (htop : Tendsto (fun H : ℝ => HIntegral f c₀ c₁ H)
      atTop (nhds 0))
    (hbottom : Tendsto (fun H : ℝ => HIntegral f c₀ c₁ (-H))
      atTop (nhds 0)) :
    Tendsto (fun H : ℝ =>
      (∫ u in -H..H, f ((c₁ : ℂ) + (u : ℂ) * I)) -
      (∫ u in -H..H, f ((c₀ : ℂ) + (u : ℂ) * I)))
      atTop (nhds 0) := by
  have hhorizontal : Tendsto (fun H : ℝ =>
      (-I) * (HIntegral f c₀ c₁ H - HIntegral f c₀ c₁ (-H)))
      atTop (nhds 0) := by
    simpa only [sub_zero, mul_zero] using (htop.sub hbottom).const_mul (-I)
  apply hhorizontal.congr'
  exact Eventually.of_forall fun H => by
    have hr := hrect H
    unfold HIntegral
    rw [smul_eq_mul, smul_eq_mul] at hr
    have hI :
        I * ((∫ u in -H..H, f ((c₁ : ℂ) + (u : ℂ) * I)) -
          (∫ u in -H..H, f ((c₀ : ℂ) + (u : ℂ) * I))) =
          (∫ x in c₀..c₁, f ((x : ℂ) + (H : ℂ) * I)) -
          (∫ x in c₀..c₁, f ((x : ℂ) + (-H : ℂ) * I)) := by
      linear_combination hr
    push_cast
    rw [← hI, ← mul_assoc]
    have hnegI : (-I : ℂ) * I = 1 := by
      rw [neg_mul, I_mul_I]
      simp
    rw [hnegI, one_mul]

/-- Exact termwise positive Eq. (84) shift from the opening line to any
larger line below `3/2`, in the symmetric-integral limit. -/
theorem tendsto_hughesYoungEquation84Positive_vertical_sub_zero
    (T t : ℝ) (h k a b r q : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ =>
      (∫ u in -H..H, hughesYoungEquation84PositiveContourTerm
        T t h k a b r q ((c₁ : ℂ) + (u : ℂ) * I)) -
      (∫ u in -H..H, hughesYoungEquation84PositiveContourTerm
        T t h k a b r q ((c₀ : ℂ) + (u : ℂ) * I)))
      atTop (nhds 0) := by
  exact tendsto_vertical_sub_zero_of_boundaryRect _ c₀ c₁
    (fun H => hughesYoungEquation84PositiveContourTerm_boundaryRect_zero
      T t h k a b r q hc₀ hc hc₁ (H := H))
    (tendsto_hIntegral_hughesYoungEquation84Positive_top_zero
      T t h k a b r q hc₀ hc₁ hc)
    (tendsto_hIntegral_hughesYoungEquation84Positive_bottom_zero
      T t h k a b r q hc₀ hc₁ hc)

/-- Exact termwise negative Eq. (84) shift in the symmetric-integral
limit. -/
theorem tendsto_hughesYoungEquation84Negative_vertical_sub_zero
    (T t : ℝ) (h k a b r q : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ =>
      (∫ u in -H..H, hughesYoungEquation84NegativeContourTerm
        T t h k a b r q ((c₁ : ℂ) + (u : ℂ) * I)) -
      (∫ u in -H..H, hughesYoungEquation84NegativeContourTerm
        T t h k a b r q ((c₀ : ℂ) + (u : ℂ) * I)))
      atTop (nhds 0) := by
  exact tendsto_vertical_sub_zero_of_boundaryRect _ c₀ c₁
    (fun H => hughesYoungEquation84NegativeContourTerm_boundaryRect_zero
      T t h k a b r q hc₀ hc hc₁ (H := H))
    (tendsto_hIntegral_hughesYoungEquation84Negative_top_zero
      T t h k a b r q hc₀ hc₁ hc)
    (tendsto_hIntegral_hughesYoungEquation84Negative_bottom_zero
      T t h k a b r q hc₀ hc₁ hc)

end RiemannZeta.GuthMaynard
