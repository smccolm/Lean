import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import RiemannZeta.GuthMaynard.HughesYoungShiftWeight

open Complex Filter MeasureTheory Set Topology
open scoped Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Moving the opened Hughes--Young terms to the source line

The divisor series is opened on `Re w > 1/2`, but Hughes--Young equation
(70) applies DFI after moving each individual Mellin term to `Re w = ε`.
This file gives the holomorphic term on the whole open right half-plane.
The finite-rectangle and infinite-height contour shifts are built from this
object, so the small positive line is connected to the already proved AFE
rather than introduced as an independent weight.
-/

/-- The non-arithmetic Hughes--Young contour factor as a function of the
complex Mellin variable. -/
noncomputable def hughesYoungRightContourWeightComplex
    (t : ℝ) (w : ℂ) : ℂ :=
  let s₁ : ℂ := afeCriticalPoint t + w
  let s₂ : ℂ := afeCriticalPoint (-t) + w
  Complex.exp (100 * w ^ 2) *
    hughesYoungAuxiliaryZero w *
    (s₁ * (1 - s₁)) ^ 2 * (s₂ * (1 - s₂)) ^ 2 *
    Complex.Gammaℝ s₁ ^ 2 * Complex.Gammaℝ s₂ ^ 2 /
    afePoleNormalization t / w / afeGammaNormalization t

theorem hughesYoungRightContourWeightComplex_vertical
    (t c u : ℝ) :
    hughesYoungRightContourWeightComplex t ((c : ℂ) + (u : ℂ) * I) =
      hughesYoungRightContourWeight t c u := by
  rfl

/-- One opened positive-index divisor term, holomorphic throughout the
right half-plane.  Logarithmic powers are used so complex differentiability
in `w` is literal. -/
noncomputable def hughesYoungPairContourTerm
    (t : ℝ) (p : ℕ × ℕ) (w : ℂ) : ℂ :=
  hughesYoungRightContourWeightComplex t w *
    divisorWeight p.1 * hughesYoungLogPower (afeCriticalPoint t + w) p.1 *
    divisorWeight p.2 * hughesYoungLogPower (afeCriticalPoint (-t) + w) p.2

/-- On a vertical line, the holomorphic term is exactly the term used in
the opened right-contour AFE. -/
theorem hughesYoungPairContourTerm_vertical
    (t c u : ℝ) {p : ℕ × ℕ} (hp₁ : 0 < p.1) (hp₂ : 0 < p.2) :
    hughesYoungPairContourTerm t p ((c : ℂ) + (u : ℂ) * I) =
      hughesYoungRightPairTerm t c u p := by
  rw [hughesYoungPairContourTerm, hughesYoungRightPairTerm,
    hughesYoungRightContourWeightComplex_vertical]
  rw [divisorDirichletTerm_eq_divisorWeight_mul_cpow,
    divisorDirichletTerm_eq_divisorWeight_mul_cpow]
  have hp₁R : (0 : ℝ) < p.1 := by exact_mod_cast hp₁
  have hp₂R : (0 : ℝ) < p.2 := by exact_mod_cast hp₂
  rw [hughesYoungLogPower_eq_cpow hp₁R,
    hughesYoungLogPower_eq_cpow hp₂R]
  simp only [Complex.ofReal_natCast]
  ring_nf

/-- Deligne's real Gamma factor is complex differentiable at every point
of the open right half-plane. -/
theorem differentiableAt_GammaR_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  unfold Complex.Gammaℝ
  letI : NeZero (Real.pi : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr Real.pi_ne_zero⟩
  have hpow : DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    (differentiable_const_cpow_of_neZero (Real.pi : ℂ)).differentiableAt.comp s
      ((differentiableAt_id.neg.div_const 2))
  have hgamma : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
    have hnot : ∀ m : ℕ, s / 2 ≠ -m := by
      intro m hm
      have hre := congrArg Complex.re hm
      simp at hre
      linarith
    exact (Complex.differentiableAt_Gamma (s / 2) hnot).comp s
      (differentiableAt_id.div_const 2)
  exact hpow.mul hgamma

/-- Euler's integral gives a height-uniform bound for `Gamma` on every
positive vertical line.  This elementary inequality is the input that lets
the Gaussian in the Hughes--Young Mellin kernel kill the horizontal sides
without invoking Stirling asymptotics. -/
theorem norm_Gamma_le_realGamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs]
  calc
    ‖∫ x in Set.Ioi (0 : ℝ),
        ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
        ∫ x in Set.Ioi (0 : ℝ),
          ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-x) * x ^ (s.re - 1) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.sub_re, Complex.one_re]
      simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Height-uniform majorant for Deligne's real Gamma factor on a positive
vertical line. -/
theorem norm_GammaR_le_realGamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gammaℝ s‖ ≤
      Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2) := by
  rw [Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hreHalf : (s / 2).re = s.re / 2 := by
    norm_num [Complex.div_re, Complex.normSq]
  have hhalf : 0 < (s / 2).re := by
    rw [hreHalf]
    linarith
  have hGamma := norm_Gamma_le_realGamma_re hhalf
  have hre : (-s / 2).re = -s.re / 2 := by
    norm_num [Complex.div_re, Complex.normSq]
  rw [hre]
  rw [hreHalf] at hGamma
  exact mul_le_mul_of_nonneg_left hGamma (by positivity)

/-- On a compact positive real-part strip, `Gammaℝ` is bounded uniformly
in the imaginary coordinate. -/
theorem exists_uniform_norm_GammaR_vertical_strip
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) :
    ∃ G : ℝ, 0 < G ∧ ∀ (x y : ℝ), x ∈ Set.Icc c₀ c₁ →
      ‖Complex.Gammaℝ ((1 / 2 + x : ℝ) + (y : ℂ) * I)‖ ≤ G := by
  let a : ℝ → ℝ := fun x => (1 / 2 + x) / 2
  let gammaMajor : ℝ → ℝ := fun x =>
    Real.pi ^ (-(1 / 2 + x) / 2) * Real.Gamma (a x)
  have haCont : Continuous a := by
    dsimp [a]
    fun_prop
  have haPos : Set.MapsTo a (Set.Icc c₀ c₁) (Set.Ioi 0) := by
    intro x hx
    change 0 < (1 / 2 + x) / 2
    have hx0 : 0 < x := hc₀.trans_le hx.1
    positivity
  have hgammaCont : ContinuousOn (fun x => Real.Gamma (a x)) (Set.Icc c₀ c₁) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp haCont.continuousOn haPos
  have hpowCont : Continuous (fun x : ℝ => Real.pi ^ (-(1 / 2 + x) / 2)) :=
    (Real.continuous_const_rpow Real.pi_ne_zero).comp (by fun_prop)
  have hmajorCont : ContinuousOn gammaMajor (Set.Icc c₀ c₁) := by
    exact hpowCont.continuousOn.mul hgammaCont
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hmajorCont
  refine ⟨max 1 C, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro x y hx
  have hsre :
      (((1 / 2 + x : ℝ) : ℂ) + (y : ℂ) * I).re = 1 / 2 + x := by simp
  have hspos : 0 < (((1 / 2 + x : ℝ) : ℂ) + (y : ℂ) * I).re := by
    rw [hsre]
    have hx0 : 0 < x := hc₀.trans_le hx.1
    positivity
  have hbound := norm_GammaR_le_realGamma_re hspos
  have hmajor : gammaMajor x ≤ C := hC ⟨x, hx, rfl⟩
  calc
    _ ≤ gammaMajor x := by
      simpa [gammaMajor, a, hsre] using hbound
    _ ≤ C := hmajor
    _ ≤ max 1 C := le_max_right _ _

/-- The modulus of one logarithmic Dirichlet power depends only on the real
part of its exponent. -/
theorem norm_hughesYoungLogPower_add_im
    (t x y n : ℝ) :
    ‖hughesYoungLogPower
        (afeCriticalPoint t + (x : ℂ) + (y : ℂ) * I) n‖ =
      ‖hughesYoungLogPower (afeCriticalPoint t + (x : ℂ)) n‖ := by
  unfold hughesYoungLogPower
  rw [Complex.norm_exp, Complex.norm_exp]
  congr 1
  simp [afeCriticalPoint, mul_re]

/-- The arithmetic pair attached to fixed positive indices is uniformly
bounded as the Mellin height varies and the real part stays in a compact
strip. -/
theorem exists_uniform_norm_hughesYoungArithmeticPair
    (t : ℝ) (p : ℕ × ℕ) {c₀ c₁ : ℝ} :
    ∃ L : ℝ, 0 < L ∧ ∀ (x y : ℝ), x ∈ Set.Icc c₀ c₁ →
      ‖divisorWeight p.1 *
          hughesYoungLogPower
            (afeCriticalPoint t + (x : ℂ) + (y : ℂ) * I) p.1 *
          divisorWeight p.2 *
          hughesYoungLogPower
            (afeCriticalPoint (-t) + (x : ℂ) + (y : ℂ) * I) p.2‖ ≤ L := by
  let arithmeticAt : ℝ → ℂ := fun x =>
    divisorWeight p.1 *
      hughesYoungLogPower (afeCriticalPoint t + (x : ℂ)) p.1 *
      divisorWeight p.2 *
      hughesYoungLogPower (afeCriticalPoint (-t) + (x : ℂ)) p.2
  have hcont : Continuous arithmeticAt := by
    dsimp [arithmeticAt, hughesYoungLogPower]
    fun_prop
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont.norm.continuousOn
  refine ⟨max 1 C, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro x y hx
  have hEq :
      ‖divisorWeight p.1 *
          hughesYoungLogPower
            (afeCriticalPoint t + (x : ℂ) + (y : ℂ) * I) p.1 *
          divisorWeight p.2 *
          hughesYoungLogPower
            (afeCriticalPoint (-t) + (x : ℂ) + (y : ℂ) * I) p.2‖ =
        ‖arithmeticAt x‖ := by
    simp only [norm_mul, arithmeticAt]
    rw [norm_hughesYoungLogPower_add_im,
      norm_hughesYoungLogPower_add_im]
  rw [hEq]
  exact (hC ⟨x, hx, rfl⟩).trans (le_max_right _ _)

/-- Exact Gaussian domination on a horizontal segment in the positive
half-plane. -/
theorem norm_hughesYoungGaussian_horizontal_le
    {x c H : ℝ} (hx0 : 0 ≤ x) (hxc : x ≤ c) :
    ‖Complex.exp (100 * (((x : ℂ) + (H : ℂ) * I) ^ 2))‖ ≤
      Real.exp (100 * c ^ 2 - 100 * H ^ 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : ((((x : ℂ) + (H : ℂ) * I) ^ 2).re) = x ^ 2 - H ^ 2 := by
    simp [pow_two, mul_re, mul_im]
  rw [mul_re, hre]
  norm_num
  nlinarith [sq_nonneg (c - x), mul_self_le_mul_self hx0 hxc]

/-- The two pole-cancelling quadratic factors contribute at most eighth
degree polynomial growth along a horizontal segment. -/
theorem norm_hughesYoungPolynomialPair_horizontal_le
    (t : ℝ) {x c H : ℝ} (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hx0 : 0 ≤ x) (hxc : x ≤ c) :
    let w : ℂ := (x : ℂ) + (H : ℂ) * I
    let s₁ : ℂ := afeCriticalPoint t + w
    let s₂ : ℂ := afeCriticalPoint (-t) + w
    ‖(s₁ * (1 - s₁)) ^ 2 * (s₂ * (1 - s₂)) ^ 2‖ ≤
      (2 + |t| + c + H) ^ 8 := by
  dsimp only
  let R : ℝ := 2 + |t| + c + H
  have hxmem : x ∈ Set.uIcc (-c) c := by
    rw [uIcc_of_le (by linarith : -c ≤ c)]
    exact ⟨by linarith, hxc⟩
  have hplus := one_add_norm_afeCriticalPoint_add_horizontal_le
    t c H x hc hH hxmem
  have hminus := one_add_norm_afeCriticalPoint_add_horizontal_le
    (-t) c H x hc hH hxmem
  simp only [abs_neg] at hminus
  have hs₁ :
      ‖afeCriticalPoint t + ((x : ℂ) + (H : ℂ) * I)‖ ≤ R := by
    dsimp [R]
    linarith
  have hs₂ :
      ‖afeCriticalPoint (-t) + ((x : ℂ) + (H : ℂ) * I)‖ ≤ R := by
    dsimp [R]
    linarith
  have h1s₁ :
      ‖1 - (afeCriticalPoint t + ((x : ℂ) + (H : ℂ) * I))‖ ≤ R := by
    calc
      _ ≤ ‖(1 : ℂ)‖ +
          ‖afeCriticalPoint t + ((x : ℂ) + (H : ℂ) * I)‖ := norm_sub_le _ _
      _ ≤ R := by simpa only [norm_one] using hplus
  have h1s₂ :
      ‖1 - (afeCriticalPoint (-t) + ((x : ℂ) + (H : ℂ) * I))‖ ≤ R := by
    calc
      _ ≤ ‖(1 : ℂ)‖ +
          ‖afeCriticalPoint (-t) + ((x : ℂ) + (H : ℂ) * I)‖ := norm_sub_le _ _
      _ ≤ R := by simpa only [norm_one, abs_neg] using hminus
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  rw [norm_mul, norm_pow, norm_pow, norm_mul, norm_mul]
  calc
    _ ≤ (R * R) ^ 2 * (R * R) ^ 2 := by gcongr
    _ = R ^ 8 := by ring

/-- The full non-arithmetic contour coefficient is a Gaussian times an
eighth-degree polynomial, uniformly on every compact positive strip. -/
theorem exists_norm_hughesYoungRightContourWeightComplex_horizontal_le
    (t : ℝ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 1 ≤ H → ∀ x ∈ Set.Icc c₀ c₁,
      ‖hughesYoungRightContourWeightComplex t
          ((x : ℂ) + (H : ℂ) * I)‖ ≤
        K * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16 := by
  obtain ⟨G, hGpos, hG⟩ :=
    exists_uniform_norm_GammaR_vertical_strip (c₀ := c₀) (c₁ := c₁) hc₀
  let K : ℝ := 625 * G ^ 4 * ‖(afePoleNormalization t)⁻¹‖ *
    ‖(afeGammaNormalization t)⁻¹‖
  have hKpos : 0 < K := by
    dsimp [K]
    have hpole : 0 < ‖(afePoleNormalization t)⁻¹‖ :=
      norm_pos_iff.mpr (inv_ne_zero (afePoleNormalization_ne_zero t))
    have hgamma : 0 < ‖(afeGammaNormalization t)⁻¹‖ :=
      norm_pos_iff.mpr (inv_ne_zero (afeGammaNormalization_ne_zero t))
    positivity
  refine ⟨K, hKpos, ?_⟩
  intro H hH x hx
  have hc₁ : 0 ≤ c₁ := le_trans hc₀.le hc
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hx0 : 0 ≤ x := (hc₀.trans_le hx.1).le
  let w : ℂ := (x : ℂ) + (H : ℂ) * I
  let s₁ : ℂ := afeCriticalPoint t + w
  let s₂ : ℂ := afeCriticalPoint (-t) + w
  let poly : ℂ := (s₁ * (1 - s₁)) ^ 2 * (s₂ * (1 - s₂)) ^ 2
  let R : ℝ := 2 + |t| + c₁ + H
  have hgauss : ‖Complex.exp (100 * w ^ 2)‖ ≤
      Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) := by
    exact norm_hughesYoungGaussian_horizontal_le hx0 hx.2
  have hpoly : ‖poly‖ ≤ (2 + |t| + c₁ + H) ^ 8 := by
    exact norm_hughesYoungPolynomialPair_horizontal_le t hc₁ hH0 hx0 hx.2
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg t]
  have hwUpper : ‖w‖ ≤ R := by
    calc
      ‖w‖ ≤ ‖(x : ℂ)‖ + ‖(H : ℂ) * I‖ := by
        dsimp [w]
        exact norm_add_le _ _
      _ = |x| + H := by simp [Real.norm_eq_abs, abs_of_nonneg hH0]
      _ ≤ R := by
        have habs : |x| ≤ c₁ := by simpa [abs_of_nonneg hx0] using hx.2
        calc
          |x| + H ≤ c₁ + H := by linarith
          _ ≤ R := by dsimp [R]; linarith [abs_nonneg t]
  have haux : ‖hughesYoungAuxiliaryZero w‖ ≤ 625 * R ^ 8 :=
    norm_hughesYoungAuxiliaryZero_le_polynomial hR hwUpper
  have hGamma₁ : ‖Complex.Gammaℝ s₁‖ ≤ G := by
    have h := hG x (t + H) hx
    have hs₁eq : s₁ =
        ((1 / 2 + x : ℝ) : ℂ) + ((t + H : ℝ) : ℂ) * I := by
      dsimp [s₁, w, afeCriticalPoint]
      push_cast
      ring
    rw [hs₁eq]
    exact h
  have hGamma₂ : ‖Complex.Gammaℝ s₂‖ ≤ G := by
    have h := hG x (-t + H) hx
    have hs₂eq : s₂ =
        ((1 / 2 + x : ℝ) : ℂ) + ((-t + H : ℝ) : ℂ) * I := by
      dsimp [s₂, w, afeCriticalPoint]
      push_cast
      ring
    rw [hs₂eq]
    exact h
  have hwNorm : 1 ≤ ‖w‖ := by
    have himle := Complex.abs_im_le_norm w
    have him : |w.im| = H := by simp [w, abs_of_nonneg hH0]
    rw [him] at himle
    exact hH.trans himle
  have hwInv : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (zero_lt_one.trans_le hwNorm)).2 hwNorm
  have hfactor :
      hughesYoungRightContourWeightComplex t w =
        Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w * poly *
          (Complex.Gammaℝ s₁ ^ 2 * Complex.Gammaℝ s₂ ^ 2) *
          (afePoleNormalization t)⁻¹ * w⁻¹ *
          (afeGammaNormalization t)⁻¹ := by
    unfold hughesYoungRightContourWeightComplex
    dsimp only [w, s₁, s₂, poly]
    simp only [div_eq_mul_inv]
    ring
  rw [hfactor]
  simp only [norm_mul, norm_pow]
  calc
    _ ≤ Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (625 * R ^ 8) * (2 + |t| + c₁ + H) ^ 8 *
          (G ^ 2 * G ^ 2) * ‖(afePoleNormalization t)⁻¹‖ * 1 *
          ‖(afeGammaNormalization t)⁻¹‖ := by
      gcongr
    _ = K * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16 := by
      dsimp [K, R]
      ring

/-- Uniform Gaussian-polynomial bound for one complete opened divisor
pair on the horizontal sides of a contour-shift rectangle. -/
theorem exists_norm_hughesYoungPairContourTerm_horizontal_le
    (t : ℝ) (p : ℕ × ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∀ x ∈ Set.Icc c₀ c₁,
      ‖hughesYoungPairContourTerm t p
          ((x : ℂ) + (H : ℂ) * I)‖ ≤
        C * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16 := by
  obtain ⟨K, hKpos, hK⟩ :=
    exists_norm_hughesYoungRightContourWeightComplex_horizontal_le t hc₀ hc
  obtain ⟨L, hLpos, hL⟩ :=
    exists_uniform_norm_hughesYoungArithmeticPair t p (c₀ := c₀) (c₁ := c₁)
  refine ⟨K * L, mul_pos hKpos hLpos, ?_⟩
  intro H hH x hx
  have hweight := hK H hH x hx
  have harithmetic := hL x H hx
  have hfactor :
      hughesYoungPairContourTerm t p ((x : ℂ) + (H : ℂ) * I) =
        hughesYoungRightContourWeightComplex t
            ((x : ℂ) + (H : ℂ) * I) *
          (divisorWeight p.1 *
            hughesYoungLogPower
              (afeCriticalPoint t + (x : ℂ) + (H : ℂ) * I) p.1 *
            divisorWeight p.2 *
            hughesYoungLogPower
              (afeCriticalPoint (-t) + (x : ℂ) + (H : ℂ) * I) p.2) := by
    unfold hughesYoungPairContourTerm
    ring
  rw [hfactor, norm_mul]
  calc
    _ ≤ (K * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16) * L := by
      exact mul_le_mul hweight harithmetic (norm_nonneg _) (by positivity)
    _ = (K * L) * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16 := by ac_rfl

/-- A fixed sixteenth-degree polynomial cannot overcome the quadratic
Gaussian decay on the horizontal contour edges. -/
theorem tendsto_const_mul_exp_sub_sq_mul_shift_pow_sixteen
    (C A B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    Tendsto (fun H : ℝ =>
      C * Real.exp (A - 100 * H ^ 2) * (B + H) ^ 16) atTop (nhds 0) := by
  have hExp : Tendsto (fun H : ℝ => Real.exp (-(1 / 2 : ℝ) * H))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg
        (by norm_num : (-(1 / 2 : ℝ)) < 0))
  have hbaseRpow : Tendsto (fun H : ℝ =>
      H ^ (16 : ℝ) * Real.exp (-100 * H ^ 2)) atTop (nhds 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
      (by norm_num : (0 : ℝ) < 100) 16).tendsto_zero_of_tendsto hExp
  have hbase : Tendsto (fun H : ℝ =>
      H ^ 16 * Real.exp (-100 * H ^ 2)) atTop (nhds 0) := by
    simpa only [← Real.rpow_natCast] using hbaseRpow
  let D : ℝ := C * Real.exp A * 65536
  have hmajor : Tendsto (fun H : ℝ =>
      D * (H ^ 16 * Real.exp (-100 * H ^ 2))) atTop (nhds 0) := by
    simpa only [mul_zero] using hbase.const_mul D
  apply squeeze_zero' (Eventually.of_forall fun H => by positivity)
    (show ∀ᶠ H : ℝ in atTop,
      C * Real.exp (A - 100 * H ^ 2) * (B + H) ^ 16 ≤
        D * (H ^ 16 * Real.exp (-100 * H ^ 2)) by
      filter_upwards [eventually_ge_atTop (max 1 B)] with H hH
      have hH1 : 1 ≤ H := (le_max_left 1 B).trans hH
      have hHB : B ≤ H := (le_max_right 1 B).trans hH
      have hH0 : 0 ≤ H := zero_le_one.trans hH1
      have hshift : B + H ≤ 2 * H := by linarith
      have hpow : (B + H) ^ 16 ≤ 65536 * H ^ 16 := by
        calc
          (B + H) ^ 16 ≤ (2 * H) ^ 16 := by gcongr
          _ = 65536 * H ^ 16 := by
            rw [mul_pow]
            norm_num
      have hexp : Real.exp (A - 100 * H ^ 2) =
          Real.exp A * Real.exp (-100 * H ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      dsimp [D]
      calc
        C * (Real.exp A * Real.exp (-100 * H ^ 2)) * (B + H) ^ 16 ≤
            C * (Real.exp A * Real.exp (-100 * H ^ 2)) * (65536 * H ^ 16) := by
          gcongr
        _ = C * Real.exp A * 65536 *
              (H ^ 16 * Real.exp (-100 * H ^ 2)) := by ring)
  exact hmajor

/-- The elementary horizontal-size estimate with no sign restriction on
the height.  This is the form needed for the lower edge of the contour. -/
theorem one_add_norm_afeCriticalPoint_add_horizontal_abs_le
    (t c y x : ℝ) (hc : 0 ≤ c) (hx : x ∈ Set.uIcc (-c) c) :
    1 + ‖afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I)‖ ≤
      2 + |t| + c + |y| := by
  have hxc : |x| ≤ c := by
    rw [uIcc_of_le (by linarith : -c ≤ c)] at hx
    exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hcritical : ‖afeCriticalPoint t‖ ≤ 1 / 2 + |t| := by
    calc
      ‖afeCriticalPoint t‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(t : ℂ) * I‖ := by
        unfold afeCriticalPoint
        exact norm_add_le _ _
      _ = 1 / 2 + |t| := by simp [Real.norm_eq_abs]
  have hhorizontal : ‖(x : ℂ) + (y : ℂ) * I‖ ≤ c + |y| := by
    calc
      ‖(x : ℂ) + (y : ℂ) * I‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * I‖ :=
        norm_add_le _ _
      _ = |x| + |y| := by simp [Real.norm_eq_abs]
      _ ≤ c + |y| := add_le_add hxc le_rfl
  calc
    1 + ‖afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I)‖ ≤
        1 + (‖afeCriticalPoint t‖ + ‖(x : ℂ) + (y : ℂ) * I‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 1 + ((1 / 2 + |t|) + (c + |y|)) := by gcongr
    _ ≤ 2 + |t| + c + |y| := by norm_num; linarith

/-- The pole-cancelling polynomial has the same eighth-degree bound on
either horizontal edge. -/
theorem norm_hughesYoungPolynomialPair_horizontal_abs_le
    (t : ℝ) {x c y : ℝ} (hc : 0 ≤ c)
    (hx0 : 0 ≤ x) (hxc : x ≤ c) :
    let w : ℂ := (x : ℂ) + (y : ℂ) * I
    let s₁ : ℂ := afeCriticalPoint t + w
    let s₂ : ℂ := afeCriticalPoint (-t) + w
    ‖(s₁ * (1 - s₁)) ^ 2 * (s₂ * (1 - s₂)) ^ 2‖ ≤
      (2 + |t| + c + |y|) ^ 8 := by
  dsimp only
  let R : ℝ := 2 + |t| + c + |y|
  have hxmem : x ∈ Set.uIcc (-c) c := by
    rw [uIcc_of_le (by linarith : -c ≤ c)]
    exact ⟨by linarith, hxc⟩
  have hplus := one_add_norm_afeCriticalPoint_add_horizontal_abs_le
    t c y x hc hxmem
  have hminus := one_add_norm_afeCriticalPoint_add_horizontal_abs_le
    (-t) c y x hc hxmem
  simp only [abs_neg] at hminus
  have hs₁ :
      ‖afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I)‖ ≤ R := by
    dsimp [R]
    linarith
  have hs₂ :
      ‖afeCriticalPoint (-t) + ((x : ℂ) + (y : ℂ) * I)‖ ≤ R := by
    dsimp [R]
    linarith
  have h1s₁ :
      ‖1 - (afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I))‖ ≤ R := by
    calc
      _ ≤ ‖(1 : ℂ)‖ +
          ‖afeCriticalPoint t + ((x : ℂ) + (y : ℂ) * I)‖ := norm_sub_le _ _
      _ ≤ R := by simpa only [norm_one] using hplus
  have h1s₂ :
      ‖1 - (afeCriticalPoint (-t) + ((x : ℂ) + (y : ℂ) * I))‖ ≤ R := by
    calc
      _ ≤ ‖(1 : ℂ)‖ +
          ‖afeCriticalPoint (-t) + ((x : ℂ) + (y : ℂ) * I)‖ := norm_sub_le _ _
      _ ≤ R := by simpa only [norm_one, abs_neg] using hminus
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  rw [norm_mul, norm_pow, norm_pow, norm_mul, norm_mul]
  calc
    _ ≤ (R * R) ^ 2 * (R * R) ^ 2 := by gcongr
    _ = R ^ 8 := by ring

/-- Uniform Gaussian-polynomial bound for the non-arithmetic coefficient
on the lower horizontal edge. -/
theorem exists_norm_hughesYoungRightContourWeightComplex_bottom_le
    (t : ℝ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 1 ≤ H → ∀ x ∈ Set.Icc c₀ c₁,
      ‖hughesYoungRightContourWeightComplex t
          ((x : ℂ) + (-H : ℂ) * I)‖ ≤
        K * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16 := by
  obtain ⟨G, hGpos, hG⟩ :=
    exists_uniform_norm_GammaR_vertical_strip (c₀ := c₀) (c₁ := c₁) hc₀
  let K : ℝ := 625 * G ^ 4 * ‖(afePoleNormalization t)⁻¹‖ *
    ‖(afeGammaNormalization t)⁻¹‖
  have hKpos : 0 < K := by
    dsimp [K]
    have hpole : 0 < ‖(afePoleNormalization t)⁻¹‖ :=
      norm_pos_iff.mpr (inv_ne_zero (afePoleNormalization_ne_zero t))
    have hgamma : 0 < ‖(afeGammaNormalization t)⁻¹‖ :=
      norm_pos_iff.mpr (inv_ne_zero (afeGammaNormalization_ne_zero t))
    positivity
  refine ⟨K, hKpos, ?_⟩
  intro H hH x hx
  have hc₁ : 0 ≤ c₁ := le_trans hc₀.le hc
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hx0 : 0 ≤ x := (hc₀.trans_le hx.1).le
  let w : ℂ := (x : ℂ) + (-H : ℂ) * I
  let s₁ : ℂ := afeCriticalPoint t + w
  let s₂ : ℂ := afeCriticalPoint (-t) + w
  let poly : ℂ := (s₁ * (1 - s₁)) ^ 2 * (s₂ * (1 - s₂)) ^ 2
  let R : ℝ := 2 + |t| + c₁ + H
  have hgauss : ‖Complex.exp (100 * w ^ 2)‖ ≤
      Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) := by
    have h := norm_hughesYoungGaussian_horizontal_le
      (x := x) (c := c₁) (H := -H) hx0 hx.2
    push_cast at h
    dsimp [w]
    simpa only [neg_sq] using h
  have hpoly : ‖poly‖ ≤ (2 + |t| + c₁ + H) ^ 8 := by
    have h := norm_hughesYoungPolynomialPair_horizontal_abs_le
      t (x := x) (c := c₁) (y := -H) hc₁ hx0 hx.2
    push_cast at h
    dsimp [poly, s₁, s₂, w]
    simpa only [abs_neg, abs_of_nonneg hH0] using h
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg t]
  have hwUpper : ‖w‖ ≤ R := by
    calc
      ‖w‖ ≤ ‖(x : ℂ)‖ + ‖(-H : ℂ) * I‖ := by
        dsimp [w]
        exact norm_add_le _ _
      _ = |x| + H := by simp [Real.norm_eq_abs, abs_of_nonneg hH0]
      _ ≤ R := by
        have habs : |x| ≤ c₁ := by simpa [abs_of_nonneg hx0] using hx.2
        calc
          |x| + H ≤ c₁ + H := by linarith
          _ ≤ R := by dsimp [R]; linarith [abs_nonneg t]
  have haux : ‖hughesYoungAuxiliaryZero w‖ ≤ 625 * R ^ 8 :=
    norm_hughesYoungAuxiliaryZero_le_polynomial hR hwUpper
  have hGamma₁ : ‖Complex.Gammaℝ s₁‖ ≤ G := by
    have h := hG x (t - H) hx
    have hs₁eq : s₁ =
        ((1 / 2 + x : ℝ) : ℂ) + ((t - H : ℝ) : ℂ) * I := by
      dsimp [s₁, w, afeCriticalPoint]
      push_cast
      ring
    rw [hs₁eq]
    exact h
  have hGamma₂ : ‖Complex.Gammaℝ s₂‖ ≤ G := by
    have h := hG x (-t - H) hx
    have hs₂eq : s₂ =
        ((1 / 2 + x : ℝ) : ℂ) + ((-t - H : ℝ) : ℂ) * I := by
      dsimp [s₂, w, afeCriticalPoint]
      push_cast
      ring
    rw [hs₂eq]
    exact h
  have hwNorm : 1 ≤ ‖w‖ := by
    have himle := Complex.abs_im_le_norm w
    have him : |w.im| = H := by simp [w, abs_of_nonneg hH0]
    rw [him] at himle
    exact hH.trans himle
  have hwInv : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (zero_lt_one.trans_le hwNorm)).2 hwNorm
  have hfactor :
      hughesYoungRightContourWeightComplex t w =
        Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w * poly *
          (Complex.Gammaℝ s₁ ^ 2 * Complex.Gammaℝ s₂ ^ 2) *
          (afePoleNormalization t)⁻¹ * w⁻¹ *
          (afeGammaNormalization t)⁻¹ := by
    unfold hughesYoungRightContourWeightComplex
    dsimp only [w, s₁, s₂, poly]
    simp only [div_eq_mul_inv]
    ring
  rw [hfactor]
  simp only [norm_mul, norm_pow]
  calc
    _ ≤ Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (625 * R ^ 8) * (2 + |t| + c₁ + H) ^ 8 *
          (G ^ 2 * G ^ 2) * ‖(afePoleNormalization t)⁻¹‖ * 1 *
          ‖(afeGammaNormalization t)⁻¹‖ := by
      gcongr
    _ = K * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16 := by
      dsimp [K, R]
      ring

/-- Uniform Gaussian-polynomial bound for a complete opened divisor pair
on the lower horizontal edge. -/
theorem exists_norm_hughesYoungPairContourTerm_bottom_le
    (t : ℝ) (p : ℕ × ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∀ x ∈ Set.Icc c₀ c₁,
      ‖hughesYoungPairContourTerm t p
          ((x : ℂ) + (-H : ℂ) * I)‖ ≤
        C * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16 := by
  obtain ⟨K, hKpos, hK⟩ :=
    exists_norm_hughesYoungRightContourWeightComplex_bottom_le t hc₀ hc
  obtain ⟨L, hLpos, hL⟩ :=
    exists_uniform_norm_hughesYoungArithmeticPair t p (c₀ := c₀) (c₁ := c₁)
  refine ⟨K * L, mul_pos hKpos hLpos, ?_⟩
  intro H hH x hx
  have hweight := hK H hH x hx
  have harithmetic := hL x (-H) hx
  have harithmetic' :
      ‖divisorWeight p.1 *
          hughesYoungLogPower
            (afeCriticalPoint t + (x : ℂ) + (-H : ℂ) * I) p.1 *
          divisorWeight p.2 *
          hughesYoungLogPower
            (afeCriticalPoint (-t) + (x : ℂ) + (-H : ℂ) * I) p.2‖ ≤ L := by
    simpa using harithmetic
  have hfactor :
      hughesYoungPairContourTerm t p ((x : ℂ) + (-H : ℂ) * I) =
        hughesYoungRightContourWeightComplex t
            ((x : ℂ) + (-H : ℂ) * I) *
          (divisorWeight p.1 *
            hughesYoungLogPower
              (afeCriticalPoint t + (x : ℂ) + (-H : ℂ) * I) p.1 *
            divisorWeight p.2 *
            hughesYoungLogPower
              (afeCriticalPoint (-t) + (x : ℂ) + (-H : ℂ) * I) p.2) := by
    unfold hughesYoungPairContourTerm
    ring
  rw [hfactor, norm_mul]
  calc
    _ ≤ (K * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16) * L := by
      exact mul_le_mul hweight harithmetic' (norm_nonneg _) (by positivity)
    _ = (K * L) * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16 := by ac_rfl

set_option maxHeartbeats 1000000 in
/-- The complex contour coefficient has no singularity in `Re w > 0`.
This is the exact analytic domain needed to move from the opening line to
the Hughes--Young `ε` line without crossing the pole at zero. -/
theorem differentiableAt_hughesYoungRightContourWeightComplex
    (t : ℝ) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (hughesYoungRightContourWeightComplex t) w := by
  let s₁ : ℂ → ℂ := fun z => afeCriticalPoint t + z
  let s₂ : ℂ → ℂ := fun z => afeCriticalPoint (-t) + z
  have hs₁ : DifferentiableAt ℂ s₁ w := by
    dsimp [s₁]
    fun_prop
  have hs₂ : DifferentiableAt ℂ s₂ w := by
    dsimp [s₂]
    fun_prop
  have hs₁pos : 0 < (s₁ w).re := by
    simp [s₁, afeCriticalPoint]
    linarith
  have hs₂pos : 0 < (s₂ w).re := by
    simp [s₂, afeCriticalPoint]
    linarith
  have hgamma₁ : DifferentiableAt ℂ (fun z => Complex.Gammaℝ (s₁ z)) w :=
    (differentiableAt_GammaR_of_re_pos hs₁pos).comp w hs₁
  have hgamma₂ : DifferentiableAt ℂ (fun z => Complex.Gammaℝ (s₂ z)) w :=
    (differentiableAt_GammaR_of_re_pos hs₂pos).comp w hs₂
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have haux : DifferentiableAt ℂ hughesYoungAuxiliaryZero w :=
    differentiable_hughesYoungAuxiliaryZero.differentiableAt
  unfold hughesYoungRightContourWeightComplex
  dsimp only [s₁, s₂]
  fun_prop (disch := first | exact haux | assumption)

/-- Every positive-index opened divisor term is holomorphic on the full
open right half-plane. -/
theorem differentiableAt_hughesYoungPairContourTerm
    (t : ℝ) (p : ℕ × ℕ) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (hughesYoungPairContourTerm t p) w := by
  have hweight : DifferentiableAt ℂ
      (hughesYoungRightContourWeightComplex t) w :=
    differentiableAt_hughesYoungRightContourWeightComplex t hw
  have hlog₁ : DifferentiableAt ℂ
      (fun z : ℂ => hughesYoungLogPower (afeCriticalPoint t + z) p.1) w := by
    unfold hughesYoungLogPower
    fun_prop
  have hlog₂ : DifferentiableAt ℂ
      (fun z : ℂ => hughesYoungLogPower (afeCriticalPoint (-t) + z) p.2) w := by
    unfold hughesYoungLogPower
    fun_prop
  unfold hughesYoungPairContourTerm
  exact ((((hweight.mul_const (divisorWeight p.1)).mul hlog₁).mul_const
    (divisorWeight p.2)).mul hlog₂)

/-- Holomorphy on every closed rectangle whose left edge has positive real
part. -/
theorem differentiableOn_hughesYoungPairContourTerm_rectangle
    (t : ℝ) (p : ℕ × ℕ)
    {c₀ c₁ H : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    DifferentiableOn ℂ (hughesYoungPairContourTerm t p)
      ([[c₀, c₁]] ×ℂ [[-H, H]]) := by
  intro w hw
  apply (differentiableAt_hughesYoungPairContourTerm t p ?_).differentiableWithinAt
  rw [mem_reProdIm] at hw
  have hwre : c₀ ≤ w.re := by
    rw [uIcc_of_le hc] at hw
    exact hw.1.1
  exact hc₀.trans_le hwre

/-- Exact finite-height contour shift for one opened divisor pair.  The
right and left vertical integrals differ only by the two horizontal edges
of the rectangle; no residue is crossed because both real parts are
positive. -/
theorem hughesYoungPairContourTerm_boundaryRect_zero
    (t : ℝ) (p : ℕ × ℕ) {c₀ c₁ H : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    (∫ x : ℝ in c₀..c₁,
        hughesYoungPairContourTerm t p ((x : ℂ) + (-H : ℂ) * I)) -
      (∫ x : ℝ in c₀..c₁,
        hughesYoungPairContourTerm t p ((x : ℂ) + (H : ℂ) * I)) +
      I • (∫ y : ℝ in -H..H,
        hughesYoungPairContourTerm t p ((c₁ : ℂ) + (y : ℂ) * I)) -
      I • (∫ y : ℝ in -H..H,
        hughesYoungPairContourTerm t p ((c₀ : ℂ) + (y : ℂ) * I)) = 0 := by
  have hdiff := differentiableOn_hughesYoungPairContourTerm_rectangle
    t p hc₀ hc (H := H)
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (hughesYoungPairContourTerm t p)
    ((c₀ : ℂ) - (H : ℂ) * I) ((c₁ : ℂ) + (H : ℂ) * I) (by
      simpa using hdiff)
  simpa using hrect

/-- The upper horizontal side for one opened divisor pair vanishes as the
rectangle height tends to infinity. -/
theorem tendsto_hIntegral_hughesYoungPair_top_zero
    (t : ℝ) (p : ℕ × ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ =>
      HIntegral (hughesYoungPairContourTerm t p) c₀ c₁ H)
      atTop (nhds 0) := by
  obtain ⟨C, hCpos, hbound⟩ :=
    exists_norm_hughesYoungPairContourTerm_horizontal_le t p hc₀ hc
  let envelope : ℝ → ℝ := fun H =>
    C * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
      (2 + |t| + c₁ + H) ^ 16
  have hc₁ : 0 ≤ c₁ := (hc₀.le.trans hc)
  have henv : Tendsto envelope atTop (nhds 0) := by
    exact tendsto_const_mul_exp_sub_sq_mul_shift_pow_sixteen
      C (100 * c₁ ^ 2) (2 + |t| + c₁) hCpos.le (by positivity)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ H : ℝ in atTop,
      ‖HIntegral (hughesYoungPairContourTerm t p) c₀ c₁ H‖ ≤
        envelope H * |c₁ - c₀| by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      unfold HIntegral
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Set.Icc c₀ c₁ := by
        rw [← uIcc_of_le hc]
        exact Set.uIoc_subset_uIcc hx
      simpa [envelope, add_assoc] using hbound H hH x hx')
  simpa using henv.mul_const |c₁ - c₀|

/-- The lower horizontal side for one opened divisor pair vanishes as the
rectangle height tends to infinity. -/
theorem tendsto_hIntegral_hughesYoungPair_bottom_zero
    (t : ℝ) (p : ℕ × ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ =>
      HIntegral (hughesYoungPairContourTerm t p) c₀ c₁ (-H))
      atTop (nhds 0) := by
  obtain ⟨C, hCpos, hbound⟩ :=
    exists_norm_hughesYoungPairContourTerm_bottom_le t p hc₀ hc
  let envelope : ℝ → ℝ := fun H =>
    C * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
      (2 + |t| + c₁ + H) ^ 16
  have hc₁ : 0 ≤ c₁ := hc₀.le.trans hc
  have henv : Tendsto envelope atTop (nhds 0) := by
    exact tendsto_const_mul_exp_sub_sq_mul_shift_pow_sixteen
      C (100 * c₁ ^ 2) (2 + |t| + c₁) hCpos.le (by positivity)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ H : ℝ in atTop,
      ‖HIntegral (hughesYoungPairContourTerm t p) c₀ c₁ (-H)‖ ≤
        envelope H * |c₁ - c₀| by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      unfold HIntegral
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Set.Icc c₀ c₁ := by
        rw [← uIcc_of_le hc]
        exact Set.uIoc_subset_uIcc hx
      simpa [envelope, add_assoc] using hbound H hH x hx')
  simpa using henv.mul_const |c₁ - c₀|

/-- After the two horizontal edges disappear, the symmetric vertical
integrals of one opened divisor pair agree asymptotically on any two
positive Mellin lines. -/
theorem tendsto_hughesYoungPairContourTerm_vertical_sub_zero
    (t : ℝ) (p : ℕ × ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ =>
      (∫ u in -H..H,
        hughesYoungPairContourTerm t p ((c₁ : ℂ) + (u : ℂ) * I)) -
      (∫ u in -H..H,
        hughesYoungPairContourTerm t p ((c₀ : ℂ) + (u : ℂ) * I)))
      atTop (nhds 0) := by
  have htop := tendsto_hIntegral_hughesYoungPair_top_zero t p hc₀ hc
  have hbottom := tendsto_hIntegral_hughesYoungPair_bottom_zero t p hc₀ hc
  have hhorizontal : Tendsto (fun H : ℝ =>
      (-I) *
        (HIntegral (hughesYoungPairContourTerm t p) c₀ c₁ H -
          HIntegral (hughesYoungPairContourTerm t p) c₀ c₁ (-H)))
      atTop (nhds 0) := by
    simpa only [sub_zero, mul_zero] using (htop.sub hbottom).const_mul (-I)
  apply hhorizontal.congr'
  exact Eventually.of_forall fun H => by
    have hrect := hughesYoungPairContourTerm_boundaryRect_zero
      t p (c₀ := c₀) (c₁ := c₁) (H := H) hc₀ hc
    unfold HIntegral
    rw [smul_eq_mul, smul_eq_mul] at hrect
    have hI :
        I * ((∫ u in -H..H,
            hughesYoungPairContourTerm t p ((c₁ : ℂ) + (u : ℂ) * I)) -
          (∫ u in -H..H,
            hughesYoungPairContourTerm t p ((c₀ : ℂ) + (u : ℂ) * I))) =
          (∫ x in c₀..c₁,
            hughesYoungPairContourTerm t p ((x : ℂ) + (H : ℂ) * I)) -
          (∫ x in c₀..c₁,
            hughesYoungPairContourTerm t p ((x : ℂ) + (-H : ℂ) * I)) := by
      linear_combination hrect
    push_cast
    rw [← hI]
    rw [← mul_assoc]
    have hnegI : (-I : ℂ) * I = 1 := by
      rw [neg_mul, I_mul_I]
      simp
    rw [hnegI, one_mul]

/-- The same line-shift statement in the vertical-line notation of the
opened Hughes--Young AFE. -/
theorem tendsto_hughesYoungRightPairTerm_vertical_sub_zero
    (t : ℝ) {p : ℕ × ℕ} (hp₁ : 0 < p.1) (hp₂ : 0 < p.2)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ =>
      (∫ u in -H..H, hughesYoungRightPairTerm t c₁ u p) -
      (∫ u in -H..H, hughesYoungRightPairTerm t c₀ u p))
      atTop (nhds 0) := by
  have h := tendsto_hughesYoungPairContourTerm_vertical_sub_zero
    t p hc₀ hc
  apply h.congr'
  exact Eventually.of_forall fun H => by
    have h₁ :
        (∫ u in -H..H,
          hughesYoungPairContourTerm t p ((c₁ : ℂ) + (u : ℂ) * I)) =
        ∫ u in -H..H, hughesYoungRightPairTerm t c₁ u p := by
      apply intervalIntegral.integral_congr
      intro u _
      exact hughesYoungPairContourTerm_vertical t c₁ u hp₁ hp₂
    have h₀ :
        (∫ u in -H..H,
          hughesYoungPairContourTerm t p ((c₀ : ℂ) + (u : ℂ) * I)) =
        ∫ u in -H..H, hughesYoungRightPairTerm t c₀ u p := by
      apply intervalIntegral.integral_congr
      intro u _
      exact hughesYoungPairContourTerm_vertical t c₀ u hp₁ hp₂
    exact congrArg₂ (fun a b : ℂ => a - b) h₁ h₀

end RiemannZeta.GuthMaynard
