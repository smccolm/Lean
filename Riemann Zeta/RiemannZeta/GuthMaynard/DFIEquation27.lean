import RiemannZeta.GuthMaynard.DFIEquation28
import RiemannZeta.GuthMaynard.DFIEquation26
import Mathlib.Analysis.PSeries

/-!
# DFI equation (27): complex delta approximation for the main branch

The source main kernel is complex-valued, whereas equation (18) was first
proved for real test functions.  This file supplies the exact real/imaginary
projection bridge and then recombines the two estimates.  It is the analytic
input for evaluating the double-main term in equation (27).
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff Topology

namespace RiemannZeta.GuthMaynard

/-- Iterated real derivatives commute with real projection from `ℂ`. -/
theorem iteratedDeriv_complex_re
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    iteratedDeriv k (fun x => (g x).re) =
      fun x => (iteratedDeriv k g x).re := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      funext x
      have hkTop : (k : WithTop ℕ∞) < ∞ :=
        WithTop.coe_lt_coe.mpr (ENat.coe_lt_top k)
      have hd : HasDerivAt (iteratedDeriv k g)
          (deriv (iteratedDeriv k g) x) x :=
        (hg.differentiable_iteratedDeriv k hkTop).differentiableAt.hasDerivAt
      simpa [Function.comp_def] using
        (Complex.reCLM.hasFDerivAt.comp x hd.hasFDerivAt).hasDerivAt.deriv

/-- Iterated real derivatives commute with imaginary projection from `ℂ`. -/
theorem iteratedDeriv_complex_im
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    iteratedDeriv k (fun x => (g x).im) =
      fun x => (iteratedDeriv k g x).im := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      funext x
      have hkTop : (k : WithTop ℕ∞) < ∞ :=
        WithTop.coe_lt_coe.mpr (ENat.coe_lt_top k)
      have hd : HasDerivAt (iteratedDeriv k g)
          (deriv (iteratedDeriv k g) x) x :=
        (hg.differentiable_iteratedDeriv k hkTop).differentiableAt.hasDerivAt
      simpa [Function.comp_def] using
        (Complex.imCLM.hasFDerivAt.comp x hd.hasFDerivAt).hasDerivAt.deriv

theorem contDiff_complex_re
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => (g x).re) :=
  Complex.reCLM.contDiff.comp hg

theorem contDiff_complex_im
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => (g x).im) :=
  Complex.imCLM.contDiff.comp hg

theorem hasCompactSupport_complex_re
    {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => (g x).re) :=
  hg.comp_left rfl

theorem hasCompactSupport_complex_im
    {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => (g x).im) :=
  hg.comp_left rfl

/-- Complex-valued form of the left side of DFI equation (12). -/
noncomputable def dfiEquation12LeftComplex {Q : ℝ} (w : DFIDeltaWeight Q)
    (q : ℕ) (g : ℝ → ℂ) : ℂ :=
  ∫ u : ℝ, g u * dfiDeltaKernel w q u

/-- Real projection of the complex equation-(12) integral. -/
theorem dfiEquation12LeftComplex_re
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (dfiEquation12LeftComplex w q g).re =
      dfiEquation12Left w q (fun u => (g u).re) := by
  have hδ : Continuous (fun u : ℝ => (dfiDeltaKernel w q u : ℂ)) :=
    (Complex.ofRealCLM.continuous.comp (contDiff_dfiDeltaKernel w q hq).continuous)
  have hint : Integrable (fun u : ℝ => g u * (dfiDeltaKernel w q u : ℂ)) :=
    (hg.continuous.mul hδ).integrable_of_hasCompactSupport hgc.mul_right
  unfold dfiEquation12LeftComplex dfiEquation12Left
  calc
    (∫ u : ℝ, g u * (dfiDeltaKernel w q u : ℂ)).re =
        ∫ u : ℝ, (g u * (dfiDeltaKernel w q u : ℂ)).re :=
      (integral_re hint).symm
    _ = ∫ u : ℝ, (g u).re * dfiDeltaKernel w q u := by
      congr 1
      funext u
      simp

/-- Imaginary projection of the complex equation-(12) integral. -/
theorem dfiEquation12LeftComplex_im
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (dfiEquation12LeftComplex w q g).im =
      dfiEquation12Left w q (fun u => (g u).im) := by
  have hδ : Continuous (fun u : ℝ => (dfiDeltaKernel w q u : ℂ)) :=
    (Complex.ofRealCLM.continuous.comp (contDiff_dfiDeltaKernel w q hq).continuous)
  have hint : Integrable (fun u : ℝ => g u * (dfiDeltaKernel w q u : ℂ)) :=
    (hg.continuous.mul hδ).integrable_of_hasCompactSupport hgc.mul_right
  unfold dfiEquation12LeftComplex dfiEquation12Left
  calc
    (∫ u : ℝ, g u * (dfiDeltaKernel w q u : ℂ)).im =
        ∫ u : ℝ, (g u * (dfiDeltaKernel w q u : ℂ)).im :=
      (integral_im hint).symm
    _ = ∫ u : ℝ, (g u).im * dfiDeltaKernel w q u := by
      congr 1
      funext u
      simp

theorem integral_abs_re_le_integral_norm
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ u : ℝ, |(g u).re|) ≤ ∫ u : ℝ, ‖g u‖ := by
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  exact integral_mono hgint.re.abs hgint.norm
    (fun u => Complex.abs_re_le_norm (g u))

theorem integral_abs_im_le_integral_norm
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ u : ℝ, |(g u).im|) ≤ ∫ u : ℝ, ‖g u‖ := by
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  exact integral_mono hgint.im.abs hgint.norm
    (fun u => Complex.abs_im_le_norm (g u))

/-- Complex form of DFI equation (18), with the same source scales and one
explicit constant obtained by combining the real and imaginary estimates. -/
theorem dfiEquation18_complex
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (U j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ g : ℝ → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
        tsupport g ⊆ Set.Icc (-(U : ℝ)) (U : ℝ) →
      ‖dfiEquation12LeftComplex w q g - g 0‖ ≤
        C * ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, ‖g u‖) +
          (q : ℝ) ^ j * Q ^ (j - 1) *
            ∫ u : ℝ, ‖iteratedDeriv j g u‖) := by
  obtain ⟨C₀, hC₀, hreal⟩ := dfiEquation18 w q hq U j hj
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro g hg hgc hsupp
  let gr : ℝ → ℝ := fun u => (g u).re
  let gi : ℝ → ℝ := fun u => (g u).im
  have hgr : ContDiff ℝ ∞ gr := contDiff_complex_re hg
  have hgi : ContDiff ℝ ∞ gi := contDiff_complex_im hg
  have hgrc : HasCompactSupport gr := hasCompactSupport_complex_re hgc
  have hgic : HasCompactSupport gi := hasCompactSupport_complex_im hgc
  have hgrsupp : tsupport gr ⊆ Set.Icc (-(U : ℝ)) (U : ℝ) := by
    apply (closure_mono ?_).trans hsupp
    intro u hu hzero
    exact hu (by simp [gr, hzero])
  have hgisupp : tsupport gi ⊆ Set.Icc (-(U : ℝ)) (U : ℝ) := by
    apply (closure_mono ?_).trans hsupp
    intro u hu hzero
    exact hu (by simp [gi, hzero])
  have hr := hreal gr hgr hgrc hgrsupp
  have hi := hreal gi hgi hgic hgisupp
  let E : ℝ :=
    (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, ‖g u‖) +
      (q : ℝ) ^ j * Q ^ (j - 1) *
        ∫ u : ℝ, ‖iteratedDeriv j g u‖
  have hderivSmooth : ContDiff ℝ ∞ (iteratedDeriv j g) :=
    ContDiff.contDiff_iteratedDeriv_top hg j
  have hderivCompact : HasCompactSupport (iteratedDeriv j g) := by
    have haux : ∀ k : ℕ, HasCompactSupport (iteratedDeriv k g) := by
      intro k
      induction k with
      | zero => simpa using hgc
      | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
    exact haux j
  have hmassRe : (∫ u : ℝ, |gr u|) ≤ ∫ u : ℝ, ‖g u‖ :=
    integral_abs_re_le_integral_norm g hg hgc
  have hmassIm : (∫ u : ℝ, |gi u|) ≤ ∫ u : ℝ, ‖g u‖ :=
    integral_abs_im_le_integral_norm g hg hgc
  have hderivRe : (∫ u : ℝ, |iteratedDeriv j gr u|) ≤
      ∫ u : ℝ, ‖iteratedDeriv j g u‖ := by
    rw [iteratedDeriv_complex_re g hg j]
    exact integral_abs_re_le_integral_norm
      (iteratedDeriv j g) hderivSmooth hderivCompact
  have hderivIm : (∫ u : ℝ, |iteratedDeriv j gi u|) ≤
      ∫ u : ℝ, ‖iteratedDeriv j g u‖ := by
    rw [iteratedDeriv_complex_im g hg j]
    exact integral_abs_im_le_integral_norm
      (iteratedDeriv j g) hderivSmooth hderivCompact
  have hqpow : 0 ≤ (q : ℝ) ^ j := by positivity
  have hQinv : 0 ≤ (Q ^ (j + 1))⁻¹ :=
    inv_nonneg.mpr (pow_nonneg w.Q_pos.le _)
  have hQpow : 0 ≤ Q ^ (j - 1) := pow_nonneg w.Q_pos.le _
  have hEr :
      (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, |gr u|) +
        (q : ℝ) ^ j * Q ^ (j - 1) *
          (∫ u : ℝ, |iteratedDeriv j gr u|) ≤ E := by
    dsimp [E]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hmassRe (mul_nonneg hqpow hQinv))
      (mul_le_mul_of_nonneg_left hderivRe (mul_nonneg hqpow hQpow))
  have hEi :
      (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, |gi u|) +
        (q : ℝ) ^ j * Q ^ (j - 1) *
          (∫ u : ℝ, |iteratedDeriv j gi u|) ≤ E := by
    dsimp [E]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hmassIm (mul_nonneg hqpow hQinv))
      (mul_le_mul_of_nonneg_left hderivIm (mul_nonneg hqpow hQpow))
  let z := dfiEquation12LeftComplex w q g - g 0
  have hzre : z.re = dfiEquation12Left w q gr - gr 0 := by
    dsimp [z, gr]
    rw [dfiEquation12LeftComplex_re w q hq g hg hgc]
  have hzim : z.im = dfiEquation12Left w q gi - gi 0 := by
    dsimp [z, gi]
    rw [dfiEquation12LeftComplex_im w q hq g hg hgc]
  have hre : |z.re| ≤ C₀ * E := by
    rw [hzre]
    exact hr.trans (mul_le_mul_of_nonneg_left hEr hC₀.le)
  have him : |z.im| ≤ C₀ * E := by
    rw [hzim]
    exact hi.trans (mul_le_mul_of_nonneg_left hEi hC₀.le)
  change ‖z‖ ≤ (2 * C₀) * E
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ C₀ * E + C₀ * E := add_le_add hre him
    _ = (2 * C₀) * E := by ring

/-- The scale expression on the right of complex DFI equation (18). -/
noncomputable def dfiEquation18ComplexMajorant
    {Q : ℝ} (q j : ℕ) (g : ℝ → ℂ) : ℝ :=
  (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, ‖g u‖) +
    (q : ℝ) ^ j * Q ^ (j - 1) *
      ∫ u : ℝ, ‖iteratedDeriv j g u‖

/-- Uniform equation-(18) estimates may be integrated over a family of test
functions.  This is the analytic quantifier bridge used in DFI equation
(27); the three integrability premises are later discharged from the source
dyadic support and equation-(21) derivative bounds. -/
theorem dfiEquation18_complex_family_integral
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (U j : ℕ) (hj : 2 ≤ j) (g : ℝ → ℝ → ℂ)
    (hsmooth : ∀ x, ContDiff ℝ ∞ (g x))
    (hcompact : ∀ x, HasCompactSupport (g x))
    (hsupp : ∀ x, tsupport (g x) ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (hleft : Integrable (fun x => dfiEquation12LeftComplex w q (g x)))
    (hcenter : Integrable (fun x => g x 0))
    (hmajor : Integrable (fun x => dfiEquation18ComplexMajorant
      (Q := Q) q j (g x))) :
    ∃ C : ℝ, 0 < C ∧
      ‖(∫ x : ℝ, dfiEquation12LeftComplex w q (g x)) -
          ∫ x : ℝ, g x 0‖ ≤
        C * ∫ x : ℝ,
          dfiEquation18ComplexMajorant (Q := Q) q j (g x) := by
  obtain ⟨C, hC, hbound⟩ := dfiEquation18_complex w q hq U j hj
  refine ⟨C, hC, ?_⟩
  have hdiff : Integrable (fun x =>
      dfiEquation12LeftComplex w q (g x) - g x 0) := hleft.sub hcenter
  have hpoint : ∀ x : ℝ,
      ‖dfiEquation12LeftComplex w q (g x) - g x 0‖ ≤
        C * dfiEquation18ComplexMajorant (Q := Q) q j (g x) := by
    intro x
    simpa [dfiEquation18ComplexMajorant] using
      hbound (g x) (hsmooth x) (hcompact x) (hsupp x)
  rw [← MeasureTheory.integral_sub hleft hcenter]
  calc
    ‖∫ x : ℝ, dfiEquation12LeftComplex w q (g x) - g x 0‖ ≤
        ∫ x : ℝ, ‖dfiEquation12LeftComplex w q (g x) - g x 0‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ,
        C * dfiEquation18ComplexMajorant (Q := Q) q j (g x) := by
      exact MeasureTheory.integral_mono hdiff.norm (hmajor.const_mul C) hpoint
    _ = C * ∫ x : ℝ,
        dfiEquation18ComplexMajorant (Q := Q) q j (g x) := by
      rw [MeasureTheory.integral_const_mul]

/-- The DFI delta kernel is even in its displacement variable.  This is the
sign correction needed when the change of variables in source equation (27)
is written as `y = x - h + u`. -/
theorem dfiDeltaKernel_neg
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (u : ℝ) :
    dfiDeltaKernel w q (-u) = dfiDeltaKernel w q u := by
  unfold dfiDeltaKernel dfiDeltaRadius
  rw [abs_neg]
  apply Finset.sum_congr rfl
  intro r hr
  rw [show (-u) / (q * r : ℕ) = -(u / (q * r : ℕ)) by ring]
  rw [w.even]

/-- The one-dimensional test function occurring after the exact affine
change of variables in DFI equation (27). -/
noncomputable def dfiEquation27Slice
    (C : ℝ → ℝ → ℂ) (h x u : ℝ) : ℂ :=
  C x (x - h + u)

/-- Exact inner-integral change of variables in DFI equation (27). -/
theorem dfiEquation27_inner_change_variables
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    (C : ℝ → ℝ → ℂ) (h x : ℝ) :
    (∫ y : ℝ, C x y *
        (dfiDeltaKernel w q (x - y - h) : ℂ)) =
      dfiEquation12LeftComplex w q (dfiEquation27Slice C h x) := by
  let G : ℝ → ℂ := fun y =>
    C x y * (dfiDeltaKernel w q (x - y - h) : ℂ)
  have hshift : (∫ u : ℝ, G (u + (x - h))) = ∫ y : ℝ, G y :=
    integral_add_right_eq_self G (x - h)
  rw [← hshift]
  unfold dfiEquation12LeftComplex dfiEquation27Slice G
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  rw [show x - (u + (x - h)) - h = -u by ring, dfiDeltaKernel_neg]
  congr 2
  ring

/-- Exact two-dimensional version of the change of variables displayed at
the start of DFI equation (27). -/
theorem dfiEquation27_double_change_variables
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    (C : ℝ → ℝ → ℂ) (h : ℝ) :
    (∫ x : ℝ, ∫ y : ℝ, C x y *
        (dfiDeltaKernel w q (x - y - h) : ℂ)) =
      ∫ x : ℝ,
        dfiEquation12LeftComplex w q (dfiEquation27Slice C h x) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  exact dfiEquation27_inner_change_variables w q C h x

/-- DFI equation (18), applied to the literal equation-(27) affine slice.
This theorem is the quantitative pointwise input to the subsequent
integration in `x`. -/
theorem dfiEquation27_slice_approximation
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (C : ℝ → ℝ → ℂ) (h x : ℝ)
    (U j : ℕ)
    (hsmooth : ContDiff ℝ ∞ (dfiEquation27Slice C h x))
    (hcompact : HasCompactSupport (dfiEquation27Slice C h x))
    (hsupp : tsupport (dfiEquation27Slice C h x) ⊆
      Set.Icc (-(U : ℝ)) (U : ℝ))
    (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧
      ‖dfiEquation12LeftComplex w q (dfiEquation27Slice C h x) -
          C x (x - h)‖ ≤
        K * ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ *
            (∫ u : ℝ, ‖dfiEquation27Slice C h x u‖) +
          (q : ℝ) ^ j * Q ^ (j - 1) *
            ∫ u : ℝ,
              ‖iteratedDeriv j (dfiEquation27Slice C h x) u‖) := by
  obtain ⟨K, hK, hbound⟩ := dfiEquation18_complex w q hq U j hj
  refine ⟨K, hK, ?_⟩
  simpa [dfiEquation27Slice] using
    hbound (dfiEquation27Slice C h x) hsmooth hcompact hsupp

/-- The physical-variable logarithmic factor produced by a Voronoi main
term after the substitution `x = a m`.  Here `qred` is the reduced
denominator `q / gcd(a,q)`. -/
noncomputable def dfiEquation27LogFactor
    (a qred : ℕ) (x : ℝ) : ℂ :=
  (Real.log x : ℂ) - Complex.log (a : ℂ) +
    2 * Real.eulerMascheroniConstant - 2 * Complex.log (qred : ℂ)

/-- Exact cancellation of the physical scaling logarithm against the
`-log a` term. -/
theorem dfiEquation27LogFactor_nat_mul
    (a qred : ℕ) (ha : 0 < a) (x : ℝ) (hx : 0 < x) :
    dfiEquation27LogFactor a qred ((a : ℝ) * x) =
      (Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant -
        2 * Complex.log (qred : ℂ) := by
  unfold dfiEquation27LogFactor
  rw [Real.log_mul (by exact_mod_cast ha.ne') hx.ne']
  rw [Complex.ofReal_add, Complex.natCast_log]
  ring

/-- The literal `C(x,y)` used in section 6 of DFI, with both changes of
scale from the divisor variables exposed. -/
noncomputable def dfiEquation27C
    (a b qx qy : ℕ) (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  dfiEquation27LogFactor a qx x *
    dfiEquation27LogFactor b qy y * F x y

/-- The affine family of one-variable slices occurring when equation (27)
is integrated first in the displacement variable. -/
noncomputable def dfiEquation27SourceSliceFamily
    (a b qx qy : ℕ) (F : ℝ → ℝ → ℂ) (h x u : ℝ) : ℂ :=
  dfiEquation27Slice (dfiEquation27C a b qx qy F) h x u

/-- A Voronoi logarithmic main term after the exact positive scaling
`X = a x`.  This is one of the two Jacobian identities used in equation
(27). -/
theorem dfiVoronoiMainTerm_scale_nat
    (a q : ℕ) (ha : 0 < a) (G : ℝ → ℂ) :
    dfiVoronoiMainTerm q (fun x => G ((a : ℝ) * x)) =
      (q : ℂ)⁻¹ * (a : ℂ)⁻¹ *
        ∫ X in Set.Ioi (0 : ℝ),
          dfiEquation27LogFactor a q X * G X := by
  let H : ℝ → ℂ := fun X => dfiEquation27LogFactor a q X * G X
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hinter :
      (∫ x in Set.Ioi (0 : ℝ),
        ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant -
          2 * Complex.log (q : ℂ)) * G ((a : ℝ) * x)) =
        ∫ x in Set.Ioi (0 : ℝ), H (x * (a : ℝ)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp [H]
    rw [show x * (a : ℝ) = (a : ℝ) * x by ring]
    rw [dfiEquation27LogFactor_nat_mul a q ha x hx]
  unfold dfiVoronoiMainTerm
  rw [hinter, integral_comp_mul_right_Ioi H 0 haR]
  simp only [zero_mul, Complex.real_smul]
  rw [ofReal_inv, Complex.ofReal_natCast]
  simp only [H]
  ring

/-- The physical double integral denoted `I` in DFI section 6, after both
divisor-variable scalings have been made explicit. -/
noncomputable def dfiEquation27PhysicalMainIntegral
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    (a b qx qy : ℕ) (F : ℝ → ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ X in Set.Ioi (0 : ℝ), ∫ Y in Set.Ioi (0 : ℝ),
    dfiEquation27C a b qx qy F X Y *
      (dfiDeltaKernel w q (X - Y - h) : ℂ)

/-- Applying the two Voronoi main branches and then returning to physical
variables gives exactly the DFI section-6 integral, including both
Jacobians and both reduced-modulus logarithms. -/
theorem dfiEquation27_doubleVoronoiMain_eq_physical
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    (a b qx qy : ℕ) (ha : 0 < a) (hb : 0 < b)
    (F : ℝ → ℝ → ℂ) (h : ℤ) :
    dfiVoronoiMainTerm qx (fun x =>
      dfiVoronoiMainTerm qy
        (dfiEquation23Weight w F a b h q x)) =
      (qx : ℂ)⁻¹ * (qy : ℂ)⁻¹ *
        (a : ℂ)⁻¹ * (b : ℂ)⁻¹ *
          dfiEquation27PhysicalMainIntegral w q a b qx qy F h := by
  let K : ℝ → ℂ := fun X =>
    ∫ Y in Set.Ioi (0 : ℝ),
      dfiEquation27LogFactor b qy Y * F X Y *
        (dfiDeltaKernel w q (X - Y - h) : ℂ)
  have hinner (x : ℝ) :
      dfiVoronoiMainTerm qy
          (dfiEquation23Weight w F a b h q x) =
        (qy : ℂ)⁻¹ * (b : ℂ)⁻¹ * K ((a : ℝ) * x) := by
    let G : ℝ → ℂ := fun Y =>
      F ((a : ℝ) * x) Y *
        (dfiDeltaKernel w q ((a : ℝ) * x - Y - h) : ℂ)
    have hfun :
        dfiEquation23Weight w F a b h q x =
          fun y => G ((b : ℝ) * y) := by
      funext y
      simp only [dfiEquation23Weight, G]
    rw [hfun, dfiVoronoiMainTerm_scale_nat b qy hb G]
    simp only [K, G]
    congr 1
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro Y hY
    ring
  rw [show (fun x => dfiVoronoiMainTerm qy
      (dfiEquation23Weight w F a b h q x)) =
      fun x => ((qy : ℂ)⁻¹ * (b : ℂ)⁻¹) *
        K ((a : ℝ) * x) by
      funext x
      exact hinner x]
  rw [dfiVoronoiMainTerm_const_mul,
    dfiVoronoiMainTerm_scale_nat a qx ha K]
  have hphys :
      (∫ X in Set.Ioi (0 : ℝ), dfiEquation27LogFactor a qx X * K X) =
        dfiEquation27PhysicalMainIntegral w q a b qx qy F h := by
    unfold dfiEquation27PhysicalMainIntegral
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro X hX
    dsimp only [K, dfiEquation27C]
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro Y hY
    ring
  rw [hphys]
  ring

/-- Under the source coprimality condition `(a,b)=1`, the two reduced
Voronoi denominators produce exactly the arithmetic prefactor
`gcd(ab,q)/(ab q^2)` in DFI equations (24) and (27). -/
theorem dfiEquation27_reduced_main_prefactor
    (a b q : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) :
    (((dfiReducedModulus a q).denominator : ℂ)⁻¹ *
          ((dfiReducedModulus b q).denominator : ℂ)⁻¹) *
        (a : ℂ)⁻¹ * (b : ℂ)⁻¹ =
      (Nat.gcd (a * b) q : ℂ) / ((q : ℂ) ^ 2 * (a : ℂ) * (b : ℂ)) := by
  let Ra := dfiReducedModulus a q
  let Rb := dfiReducedModulus b q
  have hga : Ra.gcd * Ra.denominator = q := Ra.denominator_reconstruct
  have hgb : Rb.gcd * Rb.denominator = q := Rb.denominator_reconstruct
  have hgprod : Nat.gcd (a * b) q = Ra.gcd * Rb.gcd := by
    change Nat.gcd (a * b) q = Nat.gcd a q * Nat.gcd b q
    rw [Nat.gcd_comm (a * b) q, hab.gcd_mul q,
      Nat.gcd_comm q a, Nat.gcd_comm q b]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hRa : (Ra.denominator : ℂ) ≠ 0 := by
    exact_mod_cast Ra.denominator_pos.ne'
  have hRb : (Rb.denominator : ℂ) ≠ 0 := by
    exact_mod_cast Rb.denominator_pos.ne'
  have hnat : q ^ 2 =
      Ra.denominator * Rb.denominator * Nat.gcd (a * b) q := by
    calc
      q ^ 2 = q * q := pow_two q
      _ = (Ra.gcd * Ra.denominator) *
          (Rb.gcd * Rb.denominator) :=
        congrArg₂ (· * ·) hga.symm hgb.symm
      _ = Ra.denominator * Rb.denominator * Nat.gcd (a * b) q := by
        rw [hgprod]
        ring
  dsimp only [Ra, Rb] at hga hgb hgprod hRa hRb ⊢
  field_simp
  exact_mod_cast hnat

/-- The complete primitive-residue main branch of equation (24), after both
Voronoi main terms are evaluated, is exactly the per-modulus summand used in
DFI equation (27). -/
theorem dfiEquation27_main_summand_exact
    {Q : ℝ} (w : DFIDeltaWeight Q) (a b q : ℕ) [NeZero q]
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (F : ℝ → ℝ → ℂ) (h : ℤ) :
    dfiEquation24MainCoefficient q h
        (dfiVoronoiMainTerm (dfiReducedModulus a q).denominator (fun x =>
          dfiVoronoiMainTerm (dfiReducedModulus b q).denominator
            (dfiEquation23Weight w F a b h q x))) =
      ((Nat.gcd (a * b) q : ℂ) /
          ((q : ℂ) ^ 2 * (a : ℂ) * (b : ℂ))) *
        ramanujanSumInt q (-h) *
          dfiEquation27PhysicalMainIntegral w q a b
            (dfiReducedModulus a q).denominator
            (dfiReducedModulus b q).denominator F h := by
  rw [dfiEquation24MainCoefficient_eq_ramanujan q (NeZero.pos q) h]
  rw [dfiEquation27_doubleVoronoiMain_eq_physical w q a b
    (dfiReducedModulus a q).denominator
    (dfiReducedModulus b q).denominator ha hb F h]
  rw [dfiEquation27_reduced_main_prefactor a b q ha hb hab]
  ring

/-- Multiplication by a logarithm preserves global smoothness when the
other factor is smooth and supported a positive distance from zero. -/
theorem contDiff_log_add_const_mul_of_support_pos
    {A : ℝ} (hA : 0 < A) (c : ℂ) {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g)
    (hsupp : Function.support g ⊆ Set.Ici A) :
    ContDiff ℝ ∞ (fun y => ((Real.log y : ℂ) + c) * g y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst y
    have hEventually :
        (fun y : ℝ => ((Real.log y : ℂ) + c) * g y) =ᶠ[nhds 0] 0 := by
      filter_upwards [Iio_mem_nhds hA] with z hz
      have hgz : g z = 0 := by
        by_contra hne
        exact (not_le_of_gt (show z < A from hz)) (hsupp hne)
      simp [hgz]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hlog : ContDiffAt ℝ ∞ Real.log y := Real.contDiffAt_log.2 hy
    have hlogC : ContDiffAt ℝ ∞ (fun z : ℝ => (Real.log z : ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y hlog
    exact (hlogC.add contDiffAt_const).mul hg.contDiffAt

/-- Product-space version of logarithmic multiplication in the first
coordinate.  The apparent singularity at zero is removable because the
second factor is supported a positive distance from that axis. -/
theorem contDiff_log_fst_add_const_mul_of_support_pos
    {A : ℝ} (hA : 0 < A) (c : ℂ) {g : ℝ × ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g)
    (hsupp : Function.support g ⊆ Set.Ici A ×ˢ Set.univ) :
    ContDiff ℝ ∞ (fun p => ((Real.log p.1 : ℂ) + c) * g p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 = 0
  · have hEventually :
        (fun z : ℝ × ℝ => ((Real.log z.1 : ℂ) + c) * g z) =ᶠ[nhds p] 0 := by
      have hmem : Set.Iio A ∈ nhds p.1 := by
        rw [hp]
        exact Iio_mem_nhds hA
      have hev : (Prod.fst ⁻¹' Set.Iio A) ∈ nhds p :=
        continuous_fst.continuousAt hmem
      filter_upwards [hev] with z hz
      change z.1 < A at hz
      have hgz : g z = 0 := by
        by_contra hne
        exact (not_lt_of_ge (hsupp hne).1) hz
      simp [hgz]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hlog : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => Real.log z.1) p :=
      (Real.contDiffAt_log.2 hp).comp p contDiff_fst.contDiffAt
    have hlogC : ContDiffAt ℝ ∞
        (fun z : ℝ × ℝ => (Real.log z.1 : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p hlog
    exact (hlogC.add contDiffAt_const).mul hg.contDiffAt

/-- Product-space version of logarithmic multiplication in the second
coordinate. -/
theorem contDiff_log_snd_add_const_mul_of_support_pos
    {A : ℝ} (hA : 0 < A) (c : ℂ) {g : ℝ × ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g)
    (hsupp : Function.support g ⊆ Set.univ ×ˢ Set.Ici A) :
    ContDiff ℝ ∞ (fun p => ((Real.log p.2 : ℂ) + c) * g p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 = 0
  · have hEventually :
        (fun z : ℝ × ℝ => ((Real.log z.2 : ℂ) + c) * g z) =ᶠ[nhds p] 0 := by
      have hmem : Set.Iio A ∈ nhds p.2 := by
        rw [hp]
        exact Iio_mem_nhds hA
      have hev : (Prod.snd ⁻¹' Set.Iio A) ∈ nhds p :=
        continuous_snd.continuousAt hmem
      filter_upwards [hev] with z hz
      change z.2 < A at hz
      have hgz : g z = 0 := by
        by_contra hne
        exact (not_lt_of_ge (hsupp hne).2) hz
      simp [hgz]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hlog : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => Real.log z.2) p :=
      (Real.contDiffAt_log.2 hp).comp p contDiff_snd.contDiffAt
    have hlogC : ContDiffAt ℝ ∞
        (fun z : ℝ × ℝ => (Real.log z.2 : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p hlog
    exact (hlogC.add contDiffAt_const).mul hg.contDiffAt

/-- The literal two-variable coefficient `C(x,y)` in DFI equation (27) is
smooth for the source-localized weight.  The apparent singularities of the
two logarithms at zero are removable because equation (2) places the support
inside the positive dyadic box. -/
theorem contDiff_uncurry_dfiEquation27C_source
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U h : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (a b qx qy : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h))) := by
  let F : ℝ × ℝ → ℂ :=
    Function.uncurry (dfiLocalizedWeight f φ h)
  let cx : ℂ := -Complex.log (a : ℂ) +
    2 * Real.eulerMascheroniConstant - 2 * Complex.log (qx : ℂ)
  let cy : ℂ := -Complex.log (b : ℂ) +
    2 * Real.eulerMascheroniConstant - 2 * Complex.log (qy : ℂ)
  have hFsmooth : ContDiff ℝ ∞ F := by
    exact contDiff_uncurry_dfiLocalizedWeight hf hφ
  have hFsupp : Function.support F ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    exact support_uncurry_dfiLocalizedWeight_subset hbox
  have hFfst : Function.support F ⊆ Set.Ici X ×ˢ Set.univ := by
    intro p hp
    exact ⟨(hFsupp hp).1.1, Set.mem_univ _⟩
  let G : ℝ × ℝ → ℂ := fun p => ((Real.log p.1 : ℂ) + cx) * F p
  have hGsmooth : ContDiff ℝ ∞ G := by
    exact contDiff_log_fst_add_const_mul_of_support_pos
      (zero_lt_one.trans_le hf.one_le_X) cx hFsmooth hFfst
  have hGsupp : Function.support G ⊆ Set.univ ×ˢ Set.Ici Y := by
    intro p hp
    have hpF : F p ≠ 0 := by
      intro hzero
      exact hp (by simp [G, hzero])
    exact ⟨Set.mem_univ _, (hFsupp hpF).2.1⟩
  have hfinal := contDiff_log_snd_add_const_mul_of_support_pos
    (zero_lt_one.trans_le hf.one_le_Y) cy hGsmooth hGsupp
  convert hfinal using 1
  funext p
  simp only [Function.uncurry, dfiEquation27C, dfiEquation27LogFactor,
    F, G, cx, cy]
  ring

/-- Joint smoothness of the affine slices used to turn the physical
two-variable integral in equation (27) into an outer integral of equation
(18). -/
theorem contDiff_uncurry_dfiEquation27_sourceSliceFamily
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U h : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (a b qx qy : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h)) := by
  have hC := contDiff_uncurry_dfiEquation27C_source
    (h := h) hf hbox hφ a b qx qy
  exact hC.comp (by
    fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1, p.1 - h + p.2)))

/-- The full affine slice family has compact support in the explicit
rectangle forced by the two dyadic source intervals. -/
theorem support_uncurry_dfiEquation27_sourceSliceFamily_subset
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {X Y h : ℝ}
    (hbox : DFILocalizedBox f X Y) (a b qx qy : ℕ) :
    Function.support (Function.uncurry
      (dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h)) ⊆
      Set.Icc X (2 * X) ×ˢ
        Set.Icc (Y - 2 * X + h) (2 * Y - X + h) := by
  intro p hp
  have hlocal : dfiLocalizedWeight f φ h p.1 (p.1 - h + p.2) ≠ 0 := by
    intro hz
    exact hp (by simp [Function.uncurry, dfiEquation27SourceSliceFamily,
      dfiEquation27Slice, dfiEquation27C, hz])
  have hlocal' : (p.1, p.1 - h + p.2) ∈ Function.support
      (Function.uncurry (dfiLocalizedWeight f φ h)) := hlocal
  have hmem := support_uncurry_dfiLocalizedWeight_subset hbox hlocal'
  constructor
  · exact hmem.1
  · constructor <;> linarith [hmem.1.1, hmem.1.2, hmem.2.1, hmem.2.2]

theorem hasCompactSupport_uncurry_dfiEquation27_sourceSliceFamily
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {X Y h : ℝ}
    (hbox : DFILocalizedBox f X Y) (a b qx qy : ℕ) :
    HasCompactSupport (Function.uncurry
      (dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc.prod isCompact_Icc)
  exact support_uncurry_dfiEquation27_sourceSliceFamily_subset
    hbox a b qx qy

theorem hasCompactSupport_dfiPartialY
    (j : ℕ) {g : ℝ × ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (dfiPartialY j g) := by
  induction j with
  | zero => simpa [dfiPartialY] using hg
  | succ j ih =>
      rw [dfiPartialY]
      exact ih.fderiv_apply (𝕜 := ℝ) (0, 1)

/-- The equation-(18) left side is integrable in the outer variable for the
literal source slice family. -/
theorem integrable_dfiEquation27_source_left
    {Q P X Y U h : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy q : ℕ) (hq : 0 < q) :
    Integrable (fun x => dfiEquation12LeftComplex w q
      (dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h x)) := by
  let g : ℝ → ℝ → ℂ := dfiEquation27SourceSliceFamily a b qx qy
    (dfiLocalizedWeight f φ h) h
  have hgSmooth : ContDiff ℝ ∞ (Function.uncurry g) := by
    exact contDiff_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hf hbox hφ a b qx qy
  have hgCompact : HasCompactSupport (Function.uncurry g) := by
    exact hasCompactSupport_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hbox a b qx qy
  have hδSmooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      (dfiDeltaKernel w q p.2 : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      ((contDiff_dfiDeltaKernel w q hq).comp contDiff_snd)
  have hleftJoint : Integrable (fun p : ℝ × ℝ =>
      g p.1 p.2 * (dfiDeltaKernel w q p.2 : ℂ)) :=
    (hgSmooth.mul hδSmooth).continuous.integrable_of_hasCompactSupport
      hgCompact.mul_right
  change Integrable (fun x => dfiEquation12LeftComplex w q (g x))
  simpa only [dfiEquation12LeftComplex] using hleftJoint.integral_prod_left

/-- The central source slice is supported in the first dyadic interval. -/
theorem support_dfiEquation27_source_center_subset
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {X Y h : ℝ}
    (hbox : DFILocalizedBox f X Y) (a b qx qy : ℕ) :
    Function.support (fun x => dfiEquation27SourceSliceFamily a b qx qy
      (dfiLocalizedWeight f φ h) h x 0) ⊆ Set.Icc X (2 * X) := by
  intro x hx
  have hlocal : dfiLocalizedWeight f φ h x (x - h) ≠ 0 := by
    intro hz
    exact hx (by simp [dfiEquation27SourceSliceFamily, dfiEquation27Slice,
      dfiEquation27C, hz])
  have hp : (x, x - h) ∈ Function.support
      (Function.uncurry (dfiLocalizedWeight f φ h)) := hlocal
  exact (support_uncurry_dfiLocalizedWeight_subset hbox hp).1

/-- The central value in equation (18) is integrable in the outer variable
for the source family. -/
theorem integrable_dfiEquation27_source_center
    {P X Y U h : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (a b qx qy : ℕ) :
    Integrable (fun x => dfiEquation27SourceSliceFamily a b qx qy
      (dfiLocalizedWeight f φ h) h x 0) := by
  have hjoint := contDiff_uncurry_dfiEquation27_sourceSliceFamily
    (h := h) hf hbox hφ a b qx qy
  have hcenterCD := hjoint.comp (contDiff_prodMk_left (0 : ℝ))
  have hcenterSmooth : Continuous (fun x : ℝ =>
      dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h x 0) := by
    simpa only [Function.comp_apply, Function.uncurry_apply_pair] using
      hcenterCD.continuous
  have hcenterCompact : HasCompactSupport (fun x : ℝ =>
      dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h x 0) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    exact support_dfiEquation27_source_center_subset
      (h := h) hbox a b qx qy
  exact hcenterSmooth.integrable_of_hasCompactSupport hcenterCompact

/-- The complete equation-(18) derivative majorant is integrable in the
outer variable for the source family. -/
theorem integrable_dfiEquation27_source_majorant
    {Q P X Y U h : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy q j : ℕ) :
    Integrable (fun x => dfiEquation18ComplexMajorant
      (Q := Q) q j (dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h x)) := by
  let g : ℝ → ℝ → ℂ := dfiEquation27SourceSliceFamily a b qx qy
    (dfiLocalizedWeight f φ h) h
  have hgSmooth : ContDiff ℝ ∞ (Function.uncurry g) := by
    exact contDiff_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hf hbox hφ a b qx qy
  have hgCompact : HasCompactSupport (Function.uncurry g) := by
    exact hasCompactSupport_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hbox a b qx qy
  have hgIntegrable : Integrable (Function.uncurry g) :=
    hgSmooth.continuous.integrable_of_hasCompactSupport hgCompact
  have hzeroMajor : Integrable (fun x => ∫ u : ℝ, ‖g x u‖) :=
    hgIntegrable.integral_norm_prod_left
  have hderivSmooth : ContDiff ℝ ∞
      (dfiPartialY j (Function.uncurry g)) :=
    contDiff_dfiPartialY j hgSmooth
  have hderivCompact : HasCompactSupport
      (dfiPartialY j (Function.uncurry g)) :=
    hasCompactSupport_dfiPartialY j hgCompact
  have hderivIntegrable : Integrable
      (dfiPartialY j (Function.uncurry g)) :=
    hderivSmooth.continuous.integrable_of_hasCompactSupport hderivCompact
  have hjMajor : Integrable (fun x =>
      ∫ u : ℝ, ‖iteratedDeriv j (g x) u‖) := by
    convert hderivIntegrable.integral_norm_prod_left using 1
    funext x
    apply integral_congr_ae
    filter_upwards [] with u
    rw [dfiPartialY_apply j hgSmooth x u]
    simp only [Function.uncurry_apply_pair]
  change Integrable (fun x => dfiEquation18ComplexMajorant
    (Q := Q) q j (g x))
  unfold dfiEquation18ComplexMajorant
  exact (hzeroMajor.const_mul
      ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹)).add
    (hjMajor.const_mul ((q : ℝ) ^ j * Q ^ (j - 1)))

/-- For fixed `x`, the source-localized weight is smooth in `y` and is
supported in the positive dyadic interval `[Y,2Y]`. -/
theorem dfiLocalizedWeight_fixed_left_smooth_support
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U h : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (x : ℝ) :
    ContDiff ℝ ∞ (fun y => dfiLocalizedWeight f φ h x y) ∧
      Function.support (fun y => dfiLocalizedWeight f φ h x y) ⊆
        Set.Icc Y (2 * Y) := by
  constructor
  · exact (contDiff_uncurry_dfiLocalizedWeight hf hφ).comp
      (by fun_prop : ContDiff ℝ ∞ (fun y : ℝ => (x, y)))
  · intro y hy
    have hp : (x, y) ∈ Function.support
        (Function.uncurry (dfiLocalizedWeight f φ h)) := hy
    exact (support_uncurry_dfiLocalizedWeight_subset hbox hp).2

/-- The actual equation-(27) slice has the smoothness required by the
complex delta approximation. -/
theorem contDiff_dfiEquation27_sourceSlice
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy : ℕ) (h x : ℝ) :
    ContDiff ℝ ∞ (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) := by
  obtain ⟨hgy, hgysupp⟩ :=
    dfiLocalizedWeight_fixed_left_smooth_support (h := h) hf hbox hφ x
  let cx : ℂ := dfiEquation27LogFactor a qx x
  let cy : ℂ := -Complex.log (b : ℂ) +
    2 * Real.eulerMascheroniConstant - 2 * Complex.log (qy : ℂ)
  have hweighted : ContDiff ℝ ∞ (fun y =>
      cx * ((Real.log y : ℂ) + cy) * dfiLocalizedWeight f φ h x y) := by
    simpa only [mul_assoc] using contDiff_const.mul
      (contDiff_log_add_const_mul_of_support_pos
        (lt_of_lt_of_le zero_lt_one hf.one_le_Y) cy hgy
        (hgysupp.trans Set.Icc_subset_Ici_self))
  have hcomp := hweighted.comp
    (by fun_prop : ContDiff ℝ ∞ (fun u : ℝ => x - h + u))
  convert hcomp using 1
  funext u
  simp only [Function.comp_def, dfiEquation27Slice, dfiEquation27C,
    dfiEquation27LogFactor, cx, cy]
  ring

/-- The redundant cutoff confines the actual equation-(27) slice to the
source interval `[-U,U]`. -/
theorem support_dfiEquation27_sourceSlice_subset
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {U : ℝ}
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy : ℕ) (h x : ℝ) :
    Function.support (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) ⊆
        Set.Icc (-U) U := by
  intro u hu
  have hlocal : dfiLocalizedWeight f φ h x (x - h + u) ≠ 0 := by
    intro hz
    exact hu (by simp [dfiEquation27Slice, dfiEquation27C, hz])
  have hcut : φ (x - (x - h + u) - h) ≠ 0 := by
    intro hz
    exact hlocal (by simp [dfiLocalizedWeight, hz])
  have hmem := hφ.support_subset hcut
  rw [show x - (x - h + u) - h = -u by ring] at hmem
  constructor <;> linarith [hmem.1, hmem.2]

/-- Compact support of the source equation-(27) slice, derived rather than
left as a theorem parameter. -/
theorem hasCompactSupport_dfiEquation27_sourceSlice
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {U : ℝ}
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy : ℕ) (h x : ℝ) :
    HasCompactSupport (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact support_dfiEquation27_sourceSlice_subset hφ a b qx qy h x

/-- The topological support of the source slice lies in the integer interval
required by equation (18). -/
theorem tsupport_dfiEquation27_sourceSlice_subset_natCeil
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {U : ℝ}
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy : ℕ) (h x : ℝ) :
    tsupport (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) ⊆
        Set.Icc (-((⌈U⌉₊ : ℕ) : ℝ)) (((⌈U⌉₊ : ℕ) : ℝ)) := by
  have hsupp : tsupport (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) ⊆
      Set.Icc (-U) U := by
    change closure (Function.support (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x)) ⊆
        Set.Icc (-U) U
    exact (closure_minimal
      (support_dfiEquation27_sourceSlice_subset hφ a b qx qy h x)
      isClosed_Icc)
  intro u hu
  have hUceil : U ≤ ((⌈U⌉₊ : ℕ) : ℝ) := Nat.le_ceil U
  have hu' : u ∈ Set.Icc (-U) U := hsupp hu
  constructor <;> linarith [hu'.1, hu'.2]

/-- Source-facing pointwise form of the approximation used in DFI equation
(27).  Smoothness, compact support, and the support radius are all derived
from equations (2) and (21); none remains as an external premise. -/
theorem dfiEquation27_source_slice_approximation
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy : ℕ) (h x : ℝ) (q j : ℕ)
    (hq : 0 < q) (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧
      ‖dfiEquation12LeftComplex w q
          (dfiEquation27Slice
            (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) -
        dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)
          x (x - h)‖ ≤
        K * ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ *
            (∫ u : ℝ,
              ‖dfiEquation27Slice
                (dfiEquation27C a b qx qy
                  (dfiLocalizedWeight f φ h)) h x u‖) +
          (q : ℝ) ^ j * Q ^ (j - 1) *
            ∫ u : ℝ,
              ‖iteratedDeriv j
                (dfiEquation27Slice
                  (dfiEquation27C a b qx qy
                    (dfiLocalizedWeight f φ h)) h x) u‖) := by
  exact dfiEquation27_slice_approximation w q hq
    (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x
    ⌈U⌉₊ j
    (contDiff_dfiEquation27_sourceSlice hf hbox hφ a b qx qy h x)
    (hasCompactSupport_dfiEquation27_sourceSlice hφ a b qx qy h x)
    (tsupport_dfiEquation27_sourceSlice_subset_natCeil
      hφ a b qx qy h x) hj

/-- Uniform source-facing form of the equation-(27) slice estimate.  The
constant is chosen before the outer variable `x`, which is essential for the
subsequent integration in DFI section 6. -/
theorem dfiEquation27_source_slice_approximation_uniform
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy : ℕ) (h : ℝ) (q j : ℕ)
    (hq : 0 < q) (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ,
      ‖dfiEquation12LeftComplex w q
          (dfiEquation27Slice
            (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) -
        dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)
          x (x - h)‖ ≤
        K * ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ *
            (∫ u : ℝ,
              ‖dfiEquation27Slice
                (dfiEquation27C a b qx qy
                  (dfiLocalizedWeight f φ h)) h x u‖) +
          (q : ℝ) ^ j * Q ^ (j - 1) *
            ∫ u : ℝ,
              ‖iteratedDeriv j
                (dfiEquation27Slice
                  (dfiEquation27C a b qx qy
                    (dfiLocalizedWeight f φ h)) h x) u‖) := by
  obtain ⟨K, hK, hbound⟩ :=
    dfiEquation18_complex w q hq ⌈U⌉₊ j hj
  refine ⟨K, hK, ?_⟩
  intro x
  simpa [dfiEquation27Slice] using hbound _
      (contDiff_dfiEquation27_sourceSlice hf hbox hφ a b qx qy h x)
      (hasCompactSupport_dfiEquation27_sourceSlice hφ a b qx qy h x)
      (tsupport_dfiEquation27_sourceSlice_subset_natCeil
        hφ a b qx qy h x)

/-- For the source-localized weight, the positive-quadrant physical main
integral is exactly the whole-line affine-slice integral to which equation
(18) applies.  Positivity is derived from the dyadic support, not assumed as
an integration convention. -/
theorem dfiEquation27_physicalMainIntegral_eq_sliceIntegral
    {Q P X Y : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (a b qx qy q : ℕ) (h : ℝ) :
    dfiEquation27PhysicalMainIntegral w q a b qx qy
        (dfiLocalizedWeight f φ h) h =
      ∫ x : ℝ, dfiEquation12LeftComplex w q
        (dfiEquation27Slice
          (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) := by
  let C : ℝ → ℝ → ℂ :=
    dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)
  have hinner (x : ℝ) :
      (∫ y in Set.Ioi (0 : ℝ),
          C x y * (dfiDeltaKernel w q (x - y - h) : ℂ)) =
        ∫ y : ℝ, C x y *
          (dfiDeltaKernel w q (x - y - h) : ℂ) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hyNonpos : y ≤ 0 := not_lt.mp hy
    have hlocal : dfiLocalizedWeight f φ h x y = 0 := by
      by_contra hne
      have hp : (x, y) ∈ Function.support
          (Function.uncurry (dfiLocalizedWeight f φ h)) := by
        exact hne
      have hymem := (support_uncurry_dfiLocalizedWeight_subset hbox hp).2
      linarith [hf.one_le_Y, hymem.1]
    simp [C, dfiEquation27C, hlocal]
  have houterZero : ∀ x ∉ Set.Ioi (0 : ℝ),
      (∫ y : ℝ, C x y *
        (dfiDeltaKernel w q (x - y - h) : ℂ)) = 0 := by
    intro x hx
    have hxNonpos : x ≤ 0 := not_lt.mp hx
    have hpoint : ∀ y : ℝ, C x y *
        (dfiDeltaKernel w q (x - y - h) : ℂ) = 0 := by
      intro y
      have hlocal : dfiLocalizedWeight f φ h x y = 0 := by
        by_contra hne
        have hp : (x, y) ∈ Function.support
            (Function.uncurry (dfiLocalizedWeight f φ h)) := by
          exact hne
        have hxmem := (support_uncurry_dfiLocalizedWeight_subset hbox hp).1
        linarith [hf.one_le_X, hxmem.1]
      simp [C, dfiEquation27C, hlocal]
    simp_rw [hpoint]
    simp
  unfold dfiEquation27PhysicalMainIntegral
  change (∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
      C x y * (dfiDeltaKernel w q (x - y - h) : ℂ)) = _
  simp_rw [hinner]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero houterZero]
  exact dfiEquation27_double_change_variables w q C h

/-- Source-facing integrated equation (27).  All smoothness, compact-support,
support-radius, Fubini, and majorant-integrability hypotheses of equation
(18) are discharged from equations (2) and (21). -/
theorem dfiEquation27_source_integrated_approximation
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy q j : ℕ) (h : ℝ) (hq : 0 < q) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧
      ‖dfiEquation27PhysicalMainIntegral w q a b qx qy
          (dfiLocalizedWeight f φ h) h -
        ∫ x : ℝ, dfiEquation27C a b qx qy
          (dfiLocalizedWeight f φ h) x (x - h)‖ ≤
        C * ∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) := by
  let g : ℝ → ℝ → ℂ := dfiEquation27SourceSliceFamily a b qx qy
    (dfiLocalizedWeight f φ h) h
  have hsmooth : ∀ x, ContDiff ℝ ∞ (g x) := by
    intro x
    simpa [g, dfiEquation27SourceSliceFamily] using
      contDiff_dfiEquation27_sourceSlice hf hbox hφ a b qx qy h x
  have hcompact : ∀ x, HasCompactSupport (g x) := by
    intro x
    simpa [g, dfiEquation27SourceSliceFamily] using
      hasCompactSupport_dfiEquation27_sourceSlice hφ a b qx qy h x
  have hsupp : ∀ x, tsupport (g x) ⊆
      Set.Icc (-((⌈U⌉₊ : ℕ) : ℝ)) (((⌈U⌉₊ : ℕ) : ℝ)) := by
    intro x
    simpa [g, dfiEquation27SourceSliceFamily] using
      tsupport_dfiEquation27_sourceSlice_subset_natCeil
        hφ a b qx qy h x
  have hleft : Integrable (fun x => dfiEquation12LeftComplex w q (g x)) := by
    simpa only [g] using integrable_dfiEquation27_source_left
      w hf hbox hφ a b qx qy q hq
  have hcenter : Integrable (fun x => g x 0) := by
    simpa only [g] using integrable_dfiEquation27_source_center
      hf hbox hφ a b qx qy
  have hmajor : Integrable (fun x =>
      dfiEquation18ComplexMajorant (Q := Q) q j (g x)) := by
    simpa only [g] using integrable_dfiEquation27_source_majorant
      hf hbox hφ a b qx qy q j
  obtain ⟨C, hC, hbound⟩ := dfiEquation18_complex_family_integral
    w q hq ⌈U⌉₊ j hj g hsmooth hcompact hsupp hleft hcenter hmajor
  refine ⟨C, hC, ?_⟩
  rw [dfiEquation27_physicalMainIntegral_eq_sliceIntegral
    w hf hbox a b qx qy q h]
  simpa [g, dfiEquation27SourceSliceFamily, dfiEquation27Slice] using hbound

/-- Compatibility between the integer-frequency Ramanujan sum used by the
delta symbol and the natural-frequency Kloosterman specialization used in
DFI equations (24)--(27). -/
theorem ramanujanSumInt_ofNat_eq_ramanujanSum
    (q h : ℕ) [NeZero q] :
    ramanujanSumInt q h = ramanujanSum q h := by
  have hq : 0 < q := NeZero.pos q
  unfold ramanujanSumInt ramanujanSum kloostermanSum
  simp only [hq.ne', dite_false]
  simpa using sum_range_coprime_eq_sum_zmod_units q
    (fun z => ZMod.stdAddChar ((h : ZMod q) * z))

/-- The arithmetic coefficient of the main integral in DFI equation (27).
The zero modulus is defined to contribute zero, so the complete series can
be indexed by all natural numbers. -/
noncomputable def dfiEquation27ArithmeticCoefficient
    (a b h q : ℕ) : ℂ :=
  if q = 0 then 0 else
    ((Nat.gcd (a * b) q : ℂ) / (q : ℂ) ^ 2) * ramanujanSumInt q h

theorem dfiEquation27ArithmeticCoefficient_zero
    (a b h : ℕ) :
    dfiEquation27ArithmeticCoefficient a b h 0 = 0 := by
  simp [dfiEquation27ArithmeticCoefficient]

theorem dfiEquation27ArithmeticCoefficient_eq
    (a b h q : ℕ) [NeZero q] :
    dfiEquation27ArithmeticCoefficient a b h q =
      ((Nat.gcd (a * b) q : ℂ) / (q : ℂ) ^ 2) * ramanujanSum q h := by
  have hq : 0 < q := NeZero.pos q
  simp only [dfiEquation27ArithmeticCoefficient, hq.ne', if_false]
  rw [ramanujanSumInt_ofNat_eq_ramanujanSum q h]

/-- Equation (26) gives the exact arithmetic majorant needed for the tail
of the main series in equation (27). -/
theorem norm_dfiEquation27ArithmeticCoefficient_le
    (a b h q : ℕ) [NeZero q] :
    ‖dfiEquation27ArithmeticCoefficient a b h q‖ ≤
      (Nat.gcd (a * b) q : ℝ) * (Nat.gcd h q : ℝ) *
        ((Nat.gcd h q).divisors.card : ℝ) / (q : ℝ) ^ 2 := by
  rw [dfiEquation27ArithmeticCoefficient_eq]
  rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow,
    Complex.norm_natCast]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hram := norm_ramanujanSum_le_gcd_mul_divisors q h
  calc
    ((Nat.gcd (a * b) q : ℝ) / (q : ℝ) ^ 2) *
        ‖ramanujanSum q h‖ ≤
      ((Nat.gcd (a * b) q : ℝ) / (q : ℝ) ^ 2) *
        ((Nat.gcd h q : ℝ) *
          ((Nat.gcd h q).divisors.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hram (by positivity)
    _ = (Nat.gcd (a * b) q : ℝ) * (Nat.gcd h q : ℝ) *
        ((Nat.gcd h q).divisors.card : ℝ) / (q : ℝ) ^ 2 := by
      field_simp

/-- For a nonzero shift, the equation-(26) arithmetic coefficient has the
uniform inverse-square majorant used to sum the large-modulus part of DFI
equation (27).  The constant is deliberately elementary: both gcd factors
and the divisor count are bounded by their fixed source arguments. -/
theorem norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
    (a b h q : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) [NeZero q] :
    ‖dfiEquation27ArithmeticCoefficient a b h q‖ ≤
      ((a * b * h ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹ := by
  have hbase := norm_dfiEquation27ArithmeticCoefficient_le a b h q
  have hab : Nat.gcd (a * b) q ≤ a * b :=
    Nat.gcd_le_left _ (Nat.mul_pos ha hb)
  have hhgcd : Nat.gcd h q ≤ h := Nat.gcd_le_left _ hh
  have hcard : (Nat.gcd h q).divisors.card ≤ Nat.gcd h q :=
    Nat.card_divisors_le_self _
  have hqnonneg : 0 ≤ ((q : ℝ) ^ 2)⁻¹ := by positivity
  calc
    ‖dfiEquation27ArithmeticCoefficient a b h q‖ ≤
        (Nat.gcd (a * b) q : ℝ) * (Nat.gcd h q : ℝ) *
          ((Nat.gcd h q).divisors.card : ℝ) / (q : ℝ) ^ 2 := hbase
    _ ≤ ((a * b : ℕ) : ℝ) * (h : ℝ) * (h : ℝ) / (q : ℝ) ^ 2 := by
      have habR : (Nat.gcd (a * b) q : ℝ) ≤ (a * b : ℕ) := by exact_mod_cast hab
      have hhR : (Nat.gcd h q : ℝ) ≤ h := by exact_mod_cast hhgcd
      have hcR : ((Nat.gcd h q).divisors.card : ℝ) ≤ Nat.gcd h q := by
        exact_mod_cast hcard
      have hch : ((Nat.gcd h q).divisors.card : ℝ) ≤ h := hcR.trans hhR
      gcongr
    _ = ((a * b * h ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹ := by
      push_cast
      rw [div_eq_mul_inv]
      ring

/-- The full equation-(27) arithmetic coefficient series is absolutely
summable for every nonzero shift. -/
theorem summable_norm_dfiEquation27ArithmeticCoefficient
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    Summable (fun q : ℕ => ‖dfiEquation27ArithmeticCoefficient a b h q‖) := by
  have hsquare : Summable (fun q : ℕ => ((q : ℝ) ^ 2)⁻¹) := by
    exact (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
  have hmajor := hsquare.mul_left (((a * b * h ^ 2 : ℕ) : ℝ))
  apply Summable.of_norm_bounded hmajor
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  by_cases hq : q = 0
  · subst q
    simp [dfiEquation27ArithmeticCoefficient]
  · letI : NeZero q := ⟨hq⟩
    exact norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b h q ha hb hh

/-- Quantitative finite-tail form of the preceding summability theorem.
This is the exact estimate used when equation (30) supplies a uniform bound
for the modulus-dependent main integral in the range discarded from (27). -/
theorem norm_sum_Ioo_dfiEquation27ArithmeticCoefficient_mul_le
    (a b h K L : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (I : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hI : ∀ q ∈ Finset.Ioo K L, ‖I q‖ ≤ B) :
    ‖∑ q ∈ Finset.Ioo K L,
        dfiEquation27ArithmeticCoefficient a b h q * I q‖ ≤
      ((a * b * h ^ 2 : ℕ) : ℝ) * B * (2 / (K + 1 : ℝ)) := by
  let C : ℝ := ((a * b * h ^ 2 : ℕ) : ℝ)
  have hC : 0 ≤ C := by positivity
  calc
    ‖∑ q ∈ Finset.Ioo K L,
        dfiEquation27ArithmeticCoefficient a b h q * I q‖ ≤
        ∑ q ∈ Finset.Ioo K L,
          ‖dfiEquation27ArithmeticCoefficient a b h q * I q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Ioo K L, (C * ((q : ℝ) ^ 2)⁻¹) * B := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      have hq0 : q ≠ 0 := by
        intro hzero
        subst q
        simp at hq
      letI : NeZero q := ⟨hq0⟩
      exact mul_le_mul
        (norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b h q ha hb hh)
        (hI q hq) (norm_nonneg _) (mul_nonneg hC (by positivity))
    _ = C * B * (∑ q ∈ Finset.Ioo K L, ((q : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ C * B * (2 / (K + 1 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioo_inv_sq_le K L) (mul_nonneg hC hB)
    _ = ((a * b * h ^ 2 : ℕ) : ℝ) * B * (2 / (K + 1 : ℝ)) := rfl

end RiemannZeta.GuthMaynard
