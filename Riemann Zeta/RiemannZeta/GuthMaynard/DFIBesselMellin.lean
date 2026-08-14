import RiemannZeta.GuthMaynard.DFIBesselKernel
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Mellin transforms of the DFI order-zero Bessel kernels

This file supplies the analytic identification omitted by a merely formal
Mellin--Barnes definition of the two Voronoi transforms.  The normalizations
are those of Duke--Friedlander--Iwaniec Proposition 1.
-/

open Complex Set MeasureTheory
open scoped Topology Interval

namespace RiemannZeta.GuthMaynard

/-- Mellin transform of the order-zero modified Bessel kernel. -/
noncomputable def dfiBesselK0MellinSymbol (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (s - 2) * Gamma (s / 2) ^ 2

/-- Mellin transform of the order-zero Neumann kernel. -/
noncomputable def dfiBesselY0MellinSymbol (s : ℂ) : ℂ :=
  -((2 : ℂ) ^ (s - 1) / Real.pi) *
    Complex.cos (Real.pi * s / 2) * Gamma (s / 2) ^ 2

theorem dfiBesselK0MellinSymbol_two_mul (w : ℂ) :
    dfiBesselK0MellinSymbol (2 * w) =
      (2 : ℂ) ^ (2 * w - 2) * Gamma w ^ 2 := by
  unfold dfiBesselK0MellinSymbol
  congr 2
  ring_nf

theorem dfiBesselY0MellinSymbol_two_mul (w : ℂ) :
    dfiBesselY0MellinSymbol (2 * w) =
      -((2 : ℂ) ^ (2 * w - 1) / Real.pi) *
        Complex.cos (Real.pi * w) * Gamma w ^ 2 := by
  unfold dfiBesselY0MellinSymbol
  congr 2
  · ring_nf
  · congr 1
    ring_nf

/-- The elementary Gamma integral after a positive real dilation. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_eq
    {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Complex.exp (-(a * x))) =
      (1 / a : ℂ) ^ s * Gamma s := by
  simpa only [Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_exp] using
    Complex.integral_cpow_mul_exp_neg_mul_Ioi hs ha

/-- Squaring is a bijection from the positive unit interval to itself. -/
theorem image_sq_Ioo_zero_one :
    (fun x : ℝ => x ^ 2) '' Set.Ioo 0 1 = Set.Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · change 0 < x ^ 2
      exact sq_pos_of_pos hx.1
    · change x ^ 2 < 1
      nlinarith [hx.1, hx.2, sq_nonneg (x - 1)]
  · intro hy
    have hs := Real.sq_sqrt hy.1.le
    refine ⟨Real.sqrt y, ⟨Real.sqrt_pos.2 hy.1, ?_⟩, hs⟩
    nlinarith [hy.2, Real.sqrt_nonneg y]

/-- Set-integral presentation of the Euler beta integral. -/
theorem betaIntegral_eq_integral_Ioo (u v : ℂ) :
    Complex.betaIntegral u v =
      ∫ x : ℝ in Set.Ioo 0 1,
        (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1) := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

/-- The exact square-substitution identity behind the hyperbolic beta
integral. -/
theorem betaIntegral_square_substitution (u v : ℂ) :
    Complex.betaIntegral u v =
      ∫ x : ℝ in Set.Ioo 0 1,
        |2 * x| •
          (((x ^ 2 : ℝ) : ℂ) ^ (u - 1) *
            (1 - ((x ^ 2 : ℝ) : ℂ)) ^ (v - 1)) := by
  rw [betaIntegral_eq_integral_Ioo]
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioo (0 : ℝ) 1) (f := fun x : ℝ => x ^ 2)
    (f' := fun x : ℝ => 2 * x) measurableSet_Ioo
    (fun x _ => by
      convert (hasDerivAt_pow 2 x).hasDerivWithinAt using 1
      ring_nf)
    (fun x hx y hy hxy => by
      have hxp : 0 < x := hx.1
      have hyp : 0 < y := hy.1
      nlinarith)
    (fun x : ℝ =>
      (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1))
  rwa [image_sq_Ioo_zero_one] at h

/-- The Jacobian cancels the square-root singularity in the beta
substitution. -/
theorem abs_two_mul_smul_sq_cpow_neg_half
    {x : ℝ} (hx : 0 < x) :
    |2 * x| • (((x ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1)) = 2 := by
  rw [abs_of_pos (mul_pos (by norm_num) hx), Complex.real_smul]
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by ring]
  rw [Complex.cpow_neg]
  have hsqrt : (((x ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = x := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (sq_nonneg x)]
    norm_cast
    rw [show (x ^ 2) ^ (1 / 2 : ℝ) = Real.sqrt (x ^ 2) by
      rw [Real.sqrt_eq_rpow], Real.sqrt_sq_eq_abs, abs_of_pos hx]
  rw [hsqrt]
  norm_num
  field_simp [hx.ne']

/-- Euler's beta integral after `u = tanh t` and then `v = u²`. -/
theorem integral_one_sub_sq_cpow_Ioo_eq_half_beta
    {w : ℂ} :
    (∫ x : ℝ in Set.Ioo 0 1,
        ((1 - x ^ 2 : ℝ) : ℂ) ^ (w - 1)) =
      (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) w := by
  have h := betaIntegral_square_substitution (1 / 2 : ℂ) w
  have h' : Complex.betaIntegral (1 / 2) w =
      ∫ x : ℝ in Set.Ioo 0 1,
        2 * (((1 - x ^ 2 : ℝ) : ℂ) ^ (w - 1)) := by
    rw [h]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    change |2 * x| •
        ((((x ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1)) *
          (1 - ((x ^ 2 : ℝ) : ℂ)) ^ (w - 1)) = _
    rw [← smul_mul_assoc, abs_two_mul_smul_sq_cpow_neg_half hx.1]
    push_cast
    norm_num
  rw [h', ← MeasureTheory.integral_const_mul]
  ring_nf

/-- Hyperbolic tangent maps the positive half-line bijectively to the
positive unit interval. -/
theorem image_tanh_Ioi_zero :
    Real.tanh '' Set.Ioi (0 : ℝ) = Set.Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.2 hx) (Real.cosh_pos x)
    · exact Real.tanh_lt_one x
  · intro hy
    refine ⟨Real.artanh y, Real.artanh_pos hy, Real.tanh_artanh ?_⟩
    exact ⟨by linarith [hy.1], hy.2⟩

/-- The derivative of `tanh`, in the reciprocal-cosh-square form needed by
the Mellin calculation. -/
theorem hasDerivAt_tanh_recip_cosh_sq (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (Real.cosh_pos x).ne'
  have hfun : Real.sinh / Real.cosh = Real.tanh := by
    funext y
    exact (Real.tanh_eq_sinh_div_cosh (x := y)).symm
  rw [hfun] at h
  convert h using 1
  field_simp [(Real.cosh_pos x).ne']
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- The elementary hyperbolic identity used by the `tanh` substitution. -/
theorem one_sub_tanh_sq_eq_inv_cosh_sq (x : ℝ) :
    1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos x).ne']
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- Complex-power bookkeeping for the hyperbolic Jacobian. -/
theorem inv_sq_mul_inv_sq_cpow_sub_one
    {c : ℝ} (hc : 0 < c) (w : ℂ) :
    ((1 / c ^ 2 : ℝ) : ℂ) *
        (((1 / c ^ 2 : ℝ) : ℂ) ^ (w - 1)) =
      (c : ℂ) ^ (-2 * w) := by
  let C : ℂ := (c : ℂ)
  have hC : C ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hCarg : C.arg = 0 := Complex.arg_ofReal_of_nonneg hc.le
  have hbase : (((1 / c ^ 2 : ℝ) : ℂ)) = (C ^ (2 : ℕ))⁻¹ := by
    dsimp [C]
    push_cast
    field_simp
  rw [hbase]
  have hB : (C ^ (2 : ℕ))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hC)
  calc
    (C ^ (2 : ℕ))⁻¹ * ((C ^ (2 : ℕ))⁻¹ ^ (w - 1)) =
        ((C ^ (2 : ℕ))⁻¹ ^ (w - 1)) *
          ((C ^ (2 : ℕ))⁻¹ ^ (1 : ℂ)) := by
            rw [Complex.cpow_one]
            ring
    _ = (C ^ (2 : ℕ))⁻¹ ^ ((w - 1) + 1) :=
      (Complex.cpow_add (w - 1) 1 hB).symm
    _ = (C ^ (2 : ℕ))⁻¹ ^ w := by
      congr 1
      ring
    _ = ((C ^ (2 : ℕ)) ^ w)⁻¹ := by
      have hpow : C ^ (2 : ℕ) = ((c ^ 2 : ℝ) : ℂ) := by
        simp [C]
      rw [Complex.inv_cpow]
      rw [hpow]
      rw [Complex.arg_ofReal_of_nonneg (sq_nonneg c)]
      exact Real.pi_ne_zero.symm
    _ = (C ^ (2 * w))⁻¹ := by
      congr 1
      exact (Complex.cpow_nat_mul' (n := 2) (x := C) (by
          rw [hCarg]
          norm_num
          exact Real.pi_pos) (by
          rw [hCarg]
          norm_num
          exact Real.pi_pos.le) w).symm
    _ = C ^ (-2 * w) := by
      rw [show -2 * w = -(2 * w) by ring, Complex.cpow_neg]
    _ = (c : ℂ) ^ (-2 * w) := by rfl

/-- Pointwise Jacobian identity for the hyperbolic substitution. -/
theorem tanh_jacobian_smul_one_sub_sq_cpow
    (x : ℝ) (w : ℂ) :
    (1 / Real.cosh x ^ 2) •
        (((1 - Real.tanh x ^ 2 : ℝ) : ℂ) ^ (w - 1)) =
      (Real.cosh x : ℂ) ^ (-2 * w) := by
  rw [one_sub_tanh_sq_eq_inv_cosh_sq]
  rw [Complex.real_smul]
  exact inv_sq_mul_inv_sq_cpow_sub_one (Real.cosh_pos x) w

/-- Exact beta evaluation of the hyperbolic power integral. -/
theorem integral_cosh_cpow_neg_two_mul_Ioi_eq
    (w : ℂ) :
    (∫ x : ℝ in Set.Ioi 0,
        (Real.cosh x : ℂ) ^ (-2 * w)) =
      (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) w := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) (f := Real.tanh)
    (f' := fun x : ℝ => 1 / Real.cosh x ^ 2) measurableSet_Ioi
    (fun x _ => (hasDerivAt_tanh_recip_cosh_sq x).hasDerivWithinAt)
    Real.tanh_injective.injOn
    (fun u : ℝ => ((1 - u ^ 2 : ℝ) : ℂ) ^ (w - 1))
  rw [image_tanh_Ioi_zero] at h
  calc
    (∫ x : ℝ in Set.Ioi 0,
        (Real.cosh x : ℂ) ^ (-2 * w)) =
        ∫ x : ℝ in Set.Ioi 0,
          |1 / Real.cosh x ^ 2| •
            (((1 - Real.tanh x ^ 2 : ℝ) : ℂ) ^ (w - 1)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x _
              change (Real.cosh x : ℂ) ^ (-2 * w) =
                |1 / Real.cosh x ^ 2| •
                  (((1 - Real.tanh x ^ 2 : ℝ) : ℂ) ^ (w - 1))
              rw [abs_of_pos (by positivity : 0 < 1 / Real.cosh x ^ 2)]
              exact (tanh_jacobian_smul_one_sub_sq_cpow x w).symm
    _ = ∫ u : ℝ in Set.Ioo 0 1,
          ((1 - u ^ 2 : ℝ) : ℂ) ^ (w - 1) := h.symm
    _ = (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) w :=
      integral_one_sub_sq_cpow_Ioo_eq_half_beta

/-- Absolute integrability of the beta kernel obtained after the square
substitution. -/
theorem integrableOn_one_sub_sq_cpow_Ioo
    {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn
      (fun x : ℝ => ((1 - x ^ 2 : ℝ) : ℂ) ^ (w - 1))
      (Set.Ioo 0 1) := by
  let g : ℝ → ℂ := fun y =>
    (y : ℂ) ^ ((1 / 2 : ℂ) - 1) *
      (1 - (y : ℂ)) ^ (w - 1)
  have hgIoc : IntegrableOn g (Set.Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact Complex.betaIntegral_convergent (by norm_num) hw
  have hg : IntegrableOn g (Set.Ioo 0 1) :=
    hgIoc.mono_set Set.Ioo_subset_Ioc_self
  have htrans : IntegrableOn
      (fun x : ℝ => |2 * x| • g (x ^ 2)) (Set.Ioo 0 1) := by
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Set.Ioo (0 : ℝ) 1) (f := fun x : ℝ => x ^ 2)
      (f' := fun x : ℝ => 2 * x) measurableSet_Ioo
      (fun x _ => by
        convert (hasDerivAt_pow 2 x).hasDerivWithinAt using 1
        ring_nf)
      (fun x hx y hy hxy => by
        have hxp : 0 < x := hx.1
        have hyp : 0 < y := hy.1
        nlinarith) g
    rw [image_sq_Ioo_zero_one] at hiff
    exact hiff.mp hg
  have htwo : IntegrableOn
      (fun x : ℝ => 2 * (((1 - x ^ 2 : ℝ) : ℂ) ^ (w - 1)))
      (Set.Ioo 0 1) := by
    refine htrans.congr_fun ?_ measurableSet_Ioo
    intro x hx
    dsimp [g]
    change |2 * x| •
        ((((x ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1)) *
          (1 - ((x ^ 2 : ℝ) : ℂ)) ^ (w - 1)) = _
    rw [← smul_mul_assoc, abs_two_mul_smul_sq_cpow_neg_half hx.1]
    push_cast
    norm_num
  have hhalf : IntegrableOn
      (fun x : ℝ => (1 / 2 : ℂ) *
        (2 * (((1 - x ^ 2 : ℝ) : ℂ) ^ (w - 1))))
      (Set.Ioo 0 1) := htwo.const_mul (1 / 2 : ℂ)
  refine hhalf.congr_fun ?_ measurableSet_Ioo
  intro x _
  ring

/-- Absolute integrability of the hyperbolic Mellin kernel. -/
theorem integrableOn_cosh_cpow_neg_two_mul_Ioi
    {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn
      (fun x : ℝ => (Real.cosh x : ℂ) ^ (-2 * w))
      (Set.Ioi 0) := by
  let g : ℝ → ℂ := fun u =>
    ((1 - u ^ 2 : ℝ) : ℂ) ^ (w - 1)
  have hg : IntegrableOn g (Set.Ioo 0 1) :=
    integrableOn_one_sub_sq_cpow_Ioo hw
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) (f := Real.tanh)
    (f' := fun x : ℝ => 1 / Real.cosh x ^ 2) measurableSet_Ioi
    (fun x _ => (hasDerivAt_tanh_recip_cosh_sq x).hasDerivWithinAt)
    Real.tanh_injective.injOn g
  rw [image_tanh_Ioi_zero] at hiff
  have htrans := hiff.mp hg
  refine htrans.congr_fun ?_ measurableSet_Ioi
  intro x _
  dsimp [g]
  rw [abs_of_pos (by positivity : 0 < 1 / Real.cosh x ^ 2)]
  exact tanh_jacobian_smul_one_sub_sq_cpow x w

/-- The dilated complex Gamma integrand is integrable on the positive
half-line. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi
    {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s - 1) * Complex.exp (-(a * x)))
      (Set.Ioi 0) := by
  let f : ℝ → ℂ := fun u => Complex.exp (-(u : ℂ))
  have hbase : MellinConvergent f s := by
    unfold MellinConvergent f
    refine (Complex.GammaIntegral_convergent hs).congr_fun ?_ measurableSet_Ioi
    intro x hx
    change ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
      (x : ℂ) ^ (s - 1) * Complex.exp (-(x : ℂ))
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  have hscaled : MellinConvergent (fun x => f (a * x)) s :=
    (MellinConvergent.comp_mul_left (f := f) (s := s) ha).2 hbase
  unfold MellinConvergent at hscaled
  refine hscaled.congr_fun ?_ measurableSet_Ioi
  intro x _
  simp only [f, smul_eq_mul, Complex.ofReal_mul]

/-- Norm of the two-variable Gamma kernel on the positive quadrant. -/
theorem norm_cpow_mul_exp_neg_cosh
    {s : ℂ} {x t : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (s - 1) * Complex.exp (-(x * Real.cosh t))‖ =
      x ^ (s.re - 1) * Real.exp (-(Real.cosh t * x)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
  simp only [sub_re, one_re, neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring_nf

/-- Exact integral of the norm in the radial variable. -/
theorem integral_norm_cpow_mul_exp_neg_cosh_Ioi
    {s : ℂ} (hs : 0 < s.re) (t : ℝ) :
    (∫ x : ℝ in Set.Ioi 0,
        ‖(x : ℂ) ^ (s - 1) * Complex.exp (-(x * Real.cosh t))‖) =
      (1 / Real.cosh t) ^ s.re * Real.Gamma s.re := by
  calc
    (∫ x : ℝ in Set.Ioi 0,
        ‖(x : ℂ) ^ (s - 1) * Complex.exp (-(x * Real.cosh t))‖) =
        ∫ x : ℝ in Set.Ioi 0,
          x ^ (s.re - 1) * Real.exp (-(Real.cosh t * x)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            exact norm_cpow_mul_exp_neg_cosh hx
    _ = (1 / Real.cosh t) ^ s.re * Real.Gamma s.re :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs (Real.cosh_pos t)

/-- The real reciprocal-cosh power inherited from the beta integral is
integrable. -/
theorem integrableOn_inv_cosh_rpow_Ioi
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (1 / Real.cosh t) ^ r) (Set.Ioi 0) := by
  have hcomplex := integrableOn_cosh_cpow_neg_two_mul_Ioi
    (w := ((r / 2 : ℝ) : ℂ)) (by simp [hr])
  have hnorm : IntegrableOn
      (fun t : ℝ => ‖(Real.cosh t : ℂ) ^ (-2 * ((r / 2 : ℝ) : ℂ))‖)
      (Set.Ioi 0) := hcomplex.norm
  refine hnorm.congr_fun ?_ measurableSet_Ioi
  intro t _
  change ‖(Real.cosh t : ℂ) ^ (-2 * ((r / 2 : ℝ) : ℂ))‖ =
    (1 / Real.cosh t) ^ r
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.cosh_pos t)]
  have hre : (-2 * ((r / 2 : ℝ) : ℂ)).re = -r := by
    norm_num
    ring
  rw [hre]
  rw [Real.rpow_neg (Real.cosh_pos t).le, one_div]
  exact (Real.inv_rpow (x := Real.cosh t) (Real.cosh_pos t).le r).symm

/-- Joint absolute integrability needed to exchange the two integrals in
the Mellin transform of `K₀`. -/
theorem integrableOn_dfiBesselK0_mellin_joint
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        (p.1 : ℂ) ^ (s - 1) *
          Complex.exp (-(p.1 * Real.cosh p.2)))
      (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.1 : ℂ) ^ (s - 1) * Complex.exp (-(p.1 * Real.cosh p.2))
  have hcont : ContinuousOn F (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · have hreal : ContinuousAt
          (fun x : ℝ => (x : ℂ) ^ (s - 1)) p.1 :=
        (continuousAt_cpow_const
          (Complex.ofReal_mem_slitPlane.2 hp.1)).comp
            Complex.continuous_ofReal.continuousAt
      exact hreal.comp continuousAt_fst
    · fun_prop
  have hmeas : AEStronglyMeasurable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
    rw [Measure.prod_restrict]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  have hprod : Integrable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
    refine (integrable_prod_iff' hmeas).2 ⟨?_, ?_⟩
    · filter_upwards with t
      change IntegrableOn (fun x : ℝ => F (x, t)) (Set.Ioi 0)
      refine (integrableOn_cpow_mul_exp_neg_mul_Ioi hs
        (Real.cosh_pos t)).congr_fun ?_ measurableSet_Ioi
      intro x _
      dsimp [F]
      congr 2
      push_cast
      ring
    · have hout : IntegrableOn
          (fun t : ℝ =>
            (1 / Real.cosh t) ^ s.re * Real.Gamma s.re) (Set.Ioi 0) :=
        (integrableOn_inv_cosh_rpow_Ioi hs).mul_const _
      refine hout.congr_fun ?_ measurableSet_Ioi
      intro t _
      exact (integral_norm_cpow_mul_exp_neg_cosh_Ioi hs t).symm
  simpa only [F, Measure.prod_restrict] using hprod

/-- Reciprocal-cosh version of the hyperbolic beta evaluation. -/
theorem integral_inv_cosh_cpow_Ioi_eq
    {s : ℂ} :
    (∫ t : ℝ in Set.Ioi 0,
        ((1 / Real.cosh t : ℝ) : ℂ) ^ s) =
      (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) (s / 2) := by
  calc
    (∫ t : ℝ in Set.Ioi 0,
        ((1 / Real.cosh t : ℝ) : ℂ) ^ s) =
        ∫ t : ℝ in Set.Ioi 0,
          (Real.cosh t : ℂ) ^ (-2 * (s / 2)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t _
            change ((1 / Real.cosh t : ℝ) : ℂ) ^ s =
              (Real.cosh t : ℂ) ^ (-2 * (s / 2))
            rw [show -2 * (s / 2) = -s by ring, Complex.cpow_neg]
            rw [Complex.ofReal_div, Complex.ofReal_one, one_div,
              Complex.inv_cpow]
            rw [Complex.arg_ofReal_of_nonneg (Real.cosh_pos t).le]
            exact Real.pi_ne_zero.symm
    _ = (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) (s / 2) :=
      integral_cosh_cpow_neg_two_mul_Ioi_eq (s / 2)

/-- Complex realization of the defining integral for `K₀`. -/
theorem dfiBesselK0_ofReal_eq_integral {x : ℝ} :
    (dfiBesselK0 x : ℂ) =
      ∫ t : ℝ in Set.Ioi 0,
        Complex.exp (-(x * Real.cosh t)) := by
  unfold dfiBesselK0
  refine integral_ofReal.symm.trans ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  change (Real.exp (-x * Real.cosh t) : ℂ) =
    Complex.exp (-(x * Real.cosh t))
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Fubini evaluation of the Mellin transform of the positive DFI kernel,
before simplifying the beta factor. -/
theorem integral_cpow_mul_dfiBesselK0_Ioi_eq_beta
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * (dfiBesselK0 x : ℂ)) =
      ((1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) (s / 2)) *
        Gamma s := by
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.1 : ℂ) ^ (s - 1) * Complex.exp (-(p.1 * Real.cosh p.2))
  have hjointOn : IntegrableOn F (Set.Ioi 0 ×ˢ Set.Ioi 0) :=
    integrableOn_dfiBesselK0_mellin_joint hs
  have hjoint : Integrable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
    simpa only [F, Measure.prod_restrict] using hjointOn
  have hswap :
      (∫ x : ℝ in Set.Ioi 0, ∫ t : ℝ in Set.Ioi 0, F (x, t)) =
        ∫ t : ℝ in Set.Ioi 0, ∫ x : ℝ in Set.Ioi 0, F (x, t) :=
    integral_integral_swap hjoint
  calc
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * (dfiBesselK0 x : ℂ)) =
        ∫ x : ℝ in Set.Ioi 0, ∫ t : ℝ in Set.Ioi 0, F (x, t) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          change (x : ℂ) ^ (s - 1) * (dfiBesselK0 x : ℂ) =
            ∫ t : ℝ in Set.Ioi 0, F (x, t)
          rw [dfiBesselK0_ofReal_eq_integral,
            ← MeasureTheory.integral_const_mul]
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ x : ℝ in Set.Ioi 0, F (x, t) := hswap
    _ = ∫ t : ℝ in Set.Ioi 0,
          ((1 / Real.cosh t : ℝ) : ℂ) ^ s * Gamma s := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t _
          dsimp [F]
          convert integral_cpow_mul_exp_neg_mul_Ioi_eq hs (Real.cosh_pos t) using 1
          · apply setIntegral_congr_fun measurableSet_Ioi
            intro x _
            push_cast
            ring_nf
          · rw [Complex.ofReal_div, Complex.ofReal_one]
    _ = (∫ t : ℝ in Set.Ioi 0,
          ((1 / Real.cosh t : ℝ) : ℂ) ^ s) * Gamma s := by
          rw [MeasureTheory.integral_mul_const]
    _ = ((1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) (s / 2)) *
          Gamma s := by rw [integral_inv_cosh_cpow_Ioi_eq]

/-- The duplication formula simplifies the beta factor to the standard
Mellin symbol of `K₀`. -/
theorem half_beta_mul_Gamma_eq_besselK0MellinSymbol
    {s : ℂ} (hs : 0 < s.re) :
    ((1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) (s / 2)) * Gamma s =
      dfiBesselK0MellinSymbol s := by
  have hsHalf : 0 < (s / 2).re := by
    have hre : (s / 2).re = s.re / 2 := by
      norm_num [div_re, normSq]
    rw [hre]
    linarith
  have hdenRe : 0 < (s / 2 + (1 / 2 : ℂ)).re := by
    have hre : (s / 2 + (1 / 2 : ℂ)).re = s.re / 2 + 1 / 2 := by
      norm_num [div_re, normSq]
    rw [hre]
    linarith
  have hden : Gamma (s / 2 + (1 / 2 : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hdenRe
  have hden' : Gamma ((s + 1) / 2) ≠ 0 := by
    rw [show (s + 1) / 2 = s / 2 + (1 / 2 : ℂ) by ring]
    exact hden
  have hdup :
      Gamma (s / 2) * Gamma (s / 2 + (1 / 2 : ℂ)) =
        Gamma s * (2 : ℂ) ^ (1 - s) * (Real.sqrt Real.pi : ℂ) := by
    have h := Complex.Gamma_mul_Gamma_add_half (s / 2)
    convert h using 1
    all_goals ring_nf
  have hp : (2 : ℂ) ^ (s - 2) * (2 : ℂ) ^ (1 - s) = 1 / 2 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    rw [show s - 2 + (1 - s) = (-1 : ℂ) by ring,
      Complex.cpow_neg_one]
    norm_num
  have hhalf : Gamma (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [Complex.Gamma_one_half_eq]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow Real.pi_pos.le]
    norm_cast
    rw [Real.sqrt_eq_rpow]
  have hcore :
      (Real.sqrt Real.pi : ℂ) * Gamma (s / 2) * Gamma s =
        2 * ((2 : ℂ) ^ (s - 2) * Gamma (s / 2) ^ 2 *
          Gamma (s / 2 + (1 / 2 : ℂ))) := by
    symm
    calc
      2 * ((2 : ℂ) ^ (s - 2) * Gamma (s / 2) ^ 2 *
          Gamma (s / 2 + (1 / 2 : ℂ))) =
          2 * (2 : ℂ) ^ (s - 2) * Gamma (s / 2) *
            (Gamma (s / 2) * Gamma (s / 2 + (1 / 2 : ℂ))) := by ring
      _ = 2 * (2 : ℂ) ^ (s - 2) * Gamma (s / 2) *
            (Gamma s * (2 : ℂ) ^ (1 - s) *
              (Real.sqrt Real.pi : ℂ)) := by rw [hdup]
      _ = (Real.sqrt Real.pi : ℂ) * Gamma (s / 2) * Gamma s := by
        rw [show 2 * (2 : ℂ) ^ (s - 2) * Gamma (s / 2) *
              (Gamma s * (2 : ℂ) ^ (1 - s) *
                (Real.sqrt Real.pi : ℂ)) =
            2 * ((2 : ℂ) ^ (s - 2) * (2 : ℂ) ^ (1 - s)) *
              Gamma (s / 2) * Gamma s * (Real.sqrt Real.pi : ℂ) by ring,
          hp]
        ring
  rw [Complex.betaIntegral_eq_Gamma_mul_div (1 / 2) (s / 2)
    (by norm_num) hsHalf, show (1 / 2 : ℂ) + s / 2 =
      s / 2 + (1 / 2 : ℂ) by ring, hhalf]
  unfold dfiBesselK0MellinSymbol
  field_simp [hden, hden']
  rw [show (s + 1) / 2 = s / 2 + (1 / 2 : ℂ) by ring]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hcore

/-- The classical Mellin transform of the Macdonald kernel on its absolute
convergence half-plane. This is the analytic identity used in the positive
Voronoi transform. -/
theorem integral_cpow_mul_dfiBesselK0_Ioi_eq
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * (dfiBesselK0 x : ℂ)) =
      dfiBesselK0MellinSymbol s := by
  rw [integral_cpow_mul_dfiBesselK0_Ioi_eq_beta hs,
    half_beta_mul_Gamma_eq_besselK0MellinSymbol hs]

end RiemannZeta.GuthMaynard
