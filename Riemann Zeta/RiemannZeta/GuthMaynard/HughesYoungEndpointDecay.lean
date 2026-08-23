import RiemannZeta.GuthMaynard.HughesYoungComplementContourTransfer

open Asymptotics Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

set_option maxHeartbeats 800000

namespace RiemannZeta.GuthMaynard

/-!
# The lower endpoint in the Hughes--Young dyadic reassembly

The nonnegative dyadic partition used for the DFI boxes is a partition of
unity on the arithmetic source coordinates, which are positive integers.
On the continuous DFI central line it leaves the genuine lower multiplier
`hughesYoungDyadicStep (x * hughesYoungDyadicRatio)`.  This file keeps that
multiplier explicit and estimates it by the physical-height Fourier decay
in Hughes--Young equation (65).
-/

/-! ## Absolute-convergence infrastructure -/

/-- A Bochner series whose terms are integrable and whose `L¹` masses are
summable is itself integrable.  Mathlib's corresponding interchange theorem
identifies the integral, but the explicit integrability conclusion is also
needed below to move the finite Hughes--Young shift family through the
physical-height integral. -/
theorem integrable_tsum_of_summable_integral_norm
    {α E ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Countable ι]
    {F : ι → α → E}
    (hF_int : ∀ i : ι, Integrable (F i) μ)
    (hF_sum : Summable fun i => ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a => ∑' i, F i a) μ := by
  have hmeas : AEStronglyMeasurable (fun a => ∑' i, F i a) μ :=
    AEStronglyMeasurable.tsum fun i => (hF_int i).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hterm (i : ι) :
      ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [MeasureTheory.lintegral_coe_eq_integral _ (hF_int i).norm,
      ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun a => norm_nonneg (F i a)))]
    simp only [coe_nnnorm]
  have hseries : (∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ) ≠ ⊤ := by
    rw [funext hterm]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hF_sum.abs
  have hmeasNorm (i : ι) : AEMeasurable (fun a => ‖F i a‖ₑ) μ :=
    (hF_int i).aestronglyMeasurable.enorm
  calc
    ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤
        ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ :=
      lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ :=
      MeasureTheory.lintegral_tsum hmeasNorm
    _ < ⊤ := lt_top_iff_ne_top.2 hseries

/-- The height-independent reduced Mellin monomial before either physical
coordinate has been localized to a DFI box. -/
noncomputable def hughesYoungPureReducedStaticWeight
    (T c u : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  if 0 < x ∧ 0 < y then
    hughesYoungLocalizedStaticScalar T h k *
      hughesYoungLogPower
        ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))
        (x / hughesYoungReducedLeft h k) *
      hughesYoungLogPower
        ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))
        (y / hughesYoungReducedRight h k)
  else 0

/-- Height-independent counterpart of the equation-(83) reduced Mellin
scale constant. -/
noncomputable def hughesYoungPureReducedStaticScaleConstant
    (T c u : ℝ) (h k : ℕ) : ℂ :=
  let s : ℂ := (1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)
  hughesYoungLocalizedStaticScalar T h k *
    Complex.exp
      (s * (Real.log (hughesYoungReducedLeft h k : ℝ) : ℂ)) *
    Complex.exp
      (s * (Real.log (hughesYoungReducedRight h k : ℝ) : ℂ))

/-- Exact coordinate symmetry of the height-independent endpoint source.
The reduced moduli and mollifier indices are swapped together. -/
theorem dfiSwapWeight_hughesYoungPureReducedStaticWeight
    (T c u : ℝ) (h k : ℕ) :
    dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k) =
      hughesYoungPureReducedStaticWeight T c u k h := by
  funext x y
  unfold dfiSwapWeight hughesYoungPureReducedStaticWeight
  rw [hughesYoungLocalizedStaticScalar_swap T h k,
    hughesYoungReducedLeft_swap h k, hughesYoungReducedRight_swap h k]
  by_cases hx : 0 < x <;> by_cases hy : 0 < y <;> simp [hx, hy]
  ring

/-- The static Mellin scale has the same exact coordinate symmetry. -/
theorem hughesYoungPureReducedStaticScaleConstant_swap
    (T c u : ℝ) (h k : ℕ) :
    hughesYoungPureReducedStaticScaleConstant T c u k h =
      hughesYoungPureReducedStaticScaleConstant T c u h k := by
  unfold hughesYoungPureReducedStaticScaleConstant
  rw [hughesYoungLocalizedStaticScalar_swap T h k,
    hughesYoungReducedLeft_swap h k, hughesYoungReducedRight_swap h k]
  ring

/-- Exact norm of the height-independent reduced Mellin scale.  The
Mellin ordinate is purely imaginary, so it disappears from the norm; the
two reduced arithmetic scales retain precisely the real exponent
`1 / 2 + c`. -/
theorem norm_hughesYoungPureReducedStaticScaleConstant_eq
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ =
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 + c) *
        (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 + c) := by
  have ha : 0 < (hughesYoungReducedLeft h k : ℝ) := by
    exact_mod_cast hughesYoungReducedLeft_pos hh
  have hb : 0 < (hughesYoungReducedRight h k : ℝ) := by
    exact_mod_cast hughesYoungReducedRight_pos hh hk
  unfold hughesYoungPureReducedStaticScaleConstant
  simp only [norm_mul, Complex.norm_exp, mul_re, add_re, ofReal_re,
    ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_self, add_zero]
  norm_num [Complex.div_re, Complex.normSq]
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb]
  ring_nf

/-- After the normalizing `1/(ab)` in DFI equation (27), the static
Hughes--Young scale is exactly the coefficient scale used by the native
small-contour signed-shift bound. -/
theorem norm_inverse_reducedProduct_mul_pureStaticScale_eq
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ‖(((hughesYoungReducedLeft h k : ℂ) *
        (hughesYoungReducedRight h k : ℂ))⁻¹)‖ *
        ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ =
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) *
        (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2) := by
  let a : ℝ := hughesYoungReducedLeft h k
  let b : ℝ := hughesYoungReducedRight h k
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast hughesYoungReducedLeft_pos hh
  have hb : 0 < b := by
    dsimp only [b]
    exact_mod_cast hughesYoungReducedRight_pos hh hk
  rw [norm_hughesYoungPureReducedStaticScaleConstant_eq T c u hh hk]
  change ‖(((a : ℂ) * (b : ℂ))⁻¹)‖ *
      (‖hughesYoungLocalizedStaticScalar T h k‖ *
        a ^ (1 / 2 + c) * b ^ (1 / 2 + c)) = _
  simp only [norm_inv, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos ha, abs_of_pos hb]
  rw [show 1 / 2 + c = (c - 1 / 2) + 1 by ring,
    Real.rpow_add ha, Real.rpow_add hb, Real.rpow_one, Real.rpow_one]
  field_simp [ha.ne', hb.ne']; ring

/-- Swapping the DFI test weight and both logarithmic coordinates commutes
exactly with the equation-(27) central kernel. -/
theorem dfiEquation27C_swap
    (a b qx qy : ℕ) (F : ℝ → ℝ → ℂ) (x y : ℝ) :
    dfiEquation27C b a qy qx (dfiSwapWeight F) x y =
      dfiEquation27C a b qx qy F y x := by
  unfold dfiEquation27C dfiSwapWeight
  ring

theorem hughesYoungPureReducedStaticWeight_of_pos
    (T c u : ℝ) (h k : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hughesYoungPureReducedStaticWeight T c u h k x y =
      hughesYoungLocalizedStaticScalar T h k *
        hughesYoungLogPower
          ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))
          (x / hughesYoungReducedLeft h k) *
        hughesYoungLogPower
          ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))
          (y / hughesYoungReducedRight h k) := by
  simp [hughesYoungPureReducedStaticWeight, hx, hy]

/-- Exact physical-power factorization of the height-independent source. -/
theorem hughesYoungPureReducedStaticWeight_eq_scaled_powers
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hughesYoungPureReducedStaticWeight T c u h k x y =
      hughesYoungPureReducedStaticScaleConstant T c u h k *
        (x : ℂ) ^ (-((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) *
        (y : ℂ) ^ (-((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) := by
  have ha : 0 < hughesYoungReducedLeft h k :=
    hughesYoungReducedLeft_pos hh
  have hb : 0 < hughesYoungReducedRight h k :=
    hughesYoungReducedRight_pos hh hk
  rw [hughesYoungPureReducedStaticWeight_of_pos T c u h k hx hy]
  unfold hughesYoungPureReducedStaticScaleConstant
  rw [hughesYoungLogPower_div_nat hx ha,
    hughesYoungLogPower_div_nat hy hb]
  ring

/-- Centering a reduced dyadic box at an arbitrary positive point recovers
the unlocalized Mellin monomial exactly. -/
theorem hughesYoungReducedLocalizedMellinWeight_centered_eq_pure
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hughesYoungReducedLocalizedMellinWeight T t c u
        (x / hughesYoungDyadicRatio) (y / hughesYoungDyadicRatio)
        h k x y =
      hughesYoungPureReducedMellinWeight T t c u h k x y := by
  rw [hughesYoungReducedLocalizedMellinWeight_eq_scaled_powers
    T t c u _ _ hh hk hx hy]
  rw [hughesYoungPureReducedMellinWeight_of_pos T t c u h k hx hy]
  rw [hughesYoungDyadicCutoffAt_eq_one_centered hx,
    hughesYoungDyadicCutoffAt_eq_one_centered hy]
  norm_num

/-- The same centered box recovers the height-independent unlocalized
amplitude exactly. -/
theorem hughesYoungReducedLocalizedStaticWeight_centered_eq_pure
    (T c u : ℝ) (h k : ℕ)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hughesYoungReducedLocalizedStaticWeight T c u
        (x / hughesYoungDyadicRatio) (y / hughesYoungDyadicRatio)
        h k x y =
      hughesYoungPureReducedStaticWeight T c u h k x y := by
  rw [hughesYoungPureReducedStaticWeight_of_pos T c u h k hx hy]
  unfold hughesYoungReducedLocalizedStaticWeight
    hughesYoungLocalizedLogKernel
  rw [hughesYoungDyadicCutoffAt_eq_one_centered hx,
    hughesYoungDyadicCutoffAt_eq_one_centered hy]
  norm_num
  ring

/-- The exact height phase of the unlocalized equation-(83) source. -/
theorem heightWeight_mul_hughesYoungPureReducedMellinWeight_eq_static_mul_phase
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungPureReducedMellinWeight T t c u h k x y =
      hughesYoungPureReducedStaticWeight T c u h k x y *
        Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) *
        hughesYoungHeightFourierInput T c u t := by
  rw [← hughesYoungReducedLocalizedMellinWeight_centered_eq_pure
    T t c u hh hk hx hy]
  rw [heightWeight_mul_hughesYoungReducedLocalizedMellinWeight_eq_static_mul_phase
    T t c u _ _ hh hk hx hy]
  rw [hughesYoungReducedLocalizedStaticWeight_centered_eq_pure
    T c u h k hx hy]

/-- Height integration of the pure equation-(83) monomial is exactly the
same Fourier transform that occurs in the localized DFI weights. -/
theorem integral_heightWeight_mul_hughesYoungPureReducedMellinWeight_eq_transform
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungPureReducedMellinWeight T t c u h k x y) =
      hughesYoungPureReducedStaticWeight T c u h k x y *
        hughesYoungHeightTransform T c u (Real.log (y / x)) := by
  simp_rw [heightWeight_mul_hughesYoungPureReducedMellinWeight_eq_static_mul_phase
    T _ c u hh hk hx hy]
  rw [show (fun t : ℝ =>
      hughesYoungPureReducedStaticWeight T c u h k x y *
        Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) *
          hughesYoungHeightFourierInput T c u t) =
      fun t : ℝ => hughesYoungPureReducedStaticWeight T c u h k x y *
        (Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) *
          hughesYoungHeightFourierInput T c u t) by
    funext t
    ring]
  rw [integral_const_mul, ← hughesYoungHeightTransform_eq_integral]

/-! ## Uniform Fourier separation on the lower endpoint -/

/-- Absolute integrability of the literal affine two-logarithm beta
kernel on the source convergence strip.  This is the domination theorem
needed below after the positive central slice is rescaled by its signed
shift. -/
theorem integrableOn_hughesYoungAffineLogBeta
    {A B CX COne : ℂ}
    (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    IntegrableOn
      (fun x : ℝ =>
        ((Real.log x : ℂ) + CX) *
          ((Real.log (1 + x) : ℂ) + COne) *
          ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B))
      (Set.Ioi 0) := by
  let f₀ : ℝ → ℂ := fun x =>
    (x : ℂ) ^ A * (1 + (x : ℂ)) ^ B
  let fX : ℝ → ℂ := fun x => (Real.log x : ℂ) * f₀ x
  let fOne : ℝ → ℂ := fun x => (Real.log (1 + x) : ℂ) * f₀ x
  let fMix : ℝ → ℂ := fun x =>
    (Real.log x : ℂ) * (Real.log (1 + x) : ℂ) * f₀ x
  have h₀ : IntegrableOn f₀ (Set.Ioi 0) := by
    simpa only [f₀] using integrableOn_hughesYoungBeta hA hAB
  have hX : IntegrableOn fX (Set.Ioi 0) := by
    simpa only [fX, f₀] using integrableOn_hughesYoungLogXBeta hA hAB
  have hOne : IntegrableOn fOne (Set.Ioi 0) := by
    simpa only [fOne, f₀] using
      integrableOn_hughesYoungLogOneAddBeta hA hAB
  have hMix : IntegrableOn fMix (Set.Ioi 0) := by
    simpa only [fMix, f₀] using
      integrableOn_hughesYoungMixedLogBeta hA hAB
  have hLeft : IntegrableOn
      (fun x => fMix x + COne * fX x) (Set.Ioi 0) := by
    simpa only [Pi.add_apply] using hMix.add (hX.const_mul COne)
  have hRight : IntegrableOn
      (fun x => CX * fOne x + CX * COne * f₀ x) (Set.Ioi 0) := by
    simpa only [Pi.add_apply] using
      (hOne.const_mul CX).add (h₀.const_mul (CX * COne))
  have hsum := hLeft.add hRight
  convert hsum using 1
  ext x
  simp only [Pi.add_apply]
  dsimp only [fMix, fX, fOne, f₀]
  ring

/-- The same affine beta majorant remains integrable after restricting to
the lower endpoint `0 < x < 1`. -/
theorem integrableOn_hughesYoungAffineLogBeta_lowerEndpoint
    {A B CX COne : ℂ}
    (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    IntegrableOn
      (fun x : ℝ =>
        ((Real.log x : ℂ) + CX) *
          ((Real.log (1 + x) : ℂ) + COne) *
          ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B))
      (Set.Ioo 0 1) :=
  (integrableOn_hughesYoungAffineLogBeta hA hAB).mono_set
    Set.Ioo_subset_Ioi_self

/-- The symmetric exponent in the endpoint source lies in the beta
convergence strip exactly when `0 < c < 1/2`. -/
theorem integrableOn_hughesYoungEndpointAffineBeta
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (u : ℝ) (CX COne : ℂ) :
    IntegrableOn
      (fun x : ℝ =>
        ((Real.log x : ℂ) + CX) *
          ((Real.log (1 + x) : ℂ) + COne) *
          ((x : ℂ) ^
              (-((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) *
            (1 + (x : ℂ)) ^
              (-((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)))))
      (Set.Ioi 0) := by
  apply integrableOn_hughesYoungAffineLogBeta
  · norm_num [Complex.div_re, Complex.normSq]
    linarith
  · norm_num [Complex.div_re, Complex.normSq]
    linarith

/-- The height-independent DFI central kernel on a positive signed-shift
line is absolutely integrable.  This is the integrability half of the
literal substitution `y = r x` in Hughes--Young equation (83); unlike the
bare integral identity, it is strong enough to justify later domination
and finite additivity arguments. -/
theorem integrableOn_dfiEquation27C_pureReducedStaticWeight_posShift
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (T u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b qx qy : ℕ)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn
      (fun y : ℝ => dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y)
      (Set.Ioi 0) := by
  let s : ℂ := (1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)
  let β : ℝ → ℂ := fun x =>
    ((Real.log x : ℂ) +
        ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)) *
      ((Real.log (1 + x) : ℂ) +
        ((Real.log r : ℂ) + dfiEquation27LogConstant a qx)) *
      ((x : ℂ) ^ (-s) * (1 + (x : ℂ)) ^ (-s))
  have hβ : IntegrableOn β (Set.Ioi 0) := by
    simpa only [β, s] using
      integrableOn_hughesYoungEndpointAffineBeta hc hcHalf u
        ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
        ((Real.log r : ℂ) + dfiEquation27LogConstant a qx)
  let C : ℂ :=
    hughesYoungPureReducedStaticScaleConstant T c u h k *
      (r : ℂ) ^ (-s) * (r : ℂ) ^ (-s)
  have hscaled : IntegrableOn (fun x => C * β x) (Set.Ioi 0) :=
    hβ.const_mul C
  let f : ℝ → ℂ := fun y =>
    dfiEquation27C a b qx qy
      (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y
  have hcomp : IntegrableOn (fun x => f (r * x)) (Set.Ioi 0) := by
    refine hscaled.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hx
    have hOne : 0 < 1 + x := add_pos_of_nonneg_of_pos zero_le_one hx0
    have hrx : 0 < r * x := mul_pos hr hx0
    have hrOne : 0 < r * (1 + x) := mul_pos hr hOne
    have hsum : r * x + r = r * (1 + x) := by ring
    dsimp only [f]
    rw [hsum]
    unfold dfiEquation27C
    rw [dfiEquation27LogFactor_eq_log_add_constant,
      dfiEquation27LogFactor_eq_log_add_constant,
      hughesYoungPureReducedStaticWeight_eq_scaled_powers
        T c u hh hk hrOne hrx]
    rw [Real.log_mul hr.ne' hOne.ne', Real.log_mul hr.ne' hx0.ne']
    rw [show ((r * (1 + x) : ℝ) : ℂ) =
        (r : ℂ) * (1 + (x : ℂ)) by push_cast; rfl,
      show ((r * x : ℝ) : ℂ) = (r : ℂ) * (x : ℂ) by
        push_cast; rfl]
    have hone : (1 + (x : ℂ)) = (((1 + x : ℝ) : ℂ)) := by
      push_cast
      rfl
    rw [hone]
    rw [Complex.mul_cpow_ofReal_nonneg hr.le hOne.le,
      Complex.mul_cpow_ofReal_nonneg hr.le hx0.le]
    dsimp only [C, β, s]
    push_cast
    ring
  simpa only [mul_zero, f] using
    (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff f 0 hr).mp hcomp

/-- Exact pointwise form of the physical dilation behind equation (83),
now expressed in the quantitative critical-beta notation used by the
Hughes--Young source estimates. -/
theorem dfiEquation27C_pureReducedStaticWeight_dilate_eq_criticalBeta
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy : ℕ) {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k)
        (r * x + r) (r * x) =
      (hughesYoungPureReducedStaticScaleConstant T c u h k *
        (r : ℂ) ^
          (-((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) *
        (r : ℂ) ^
          (-((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)))) *
      hughesYoungCriticalAffineBetaIntegrand 0 u c x
        ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
        ((Real.log r : ℂ) + dfiEquation27LogConstant a qx) := by
  have hOne : 0 < 1 + x := add_pos_of_nonneg_of_pos zero_le_one hx
  have hrx : 0 < r * x := mul_pos hr hx
  have hrOne : 0 < r * (1 + x) := mul_pos hr hOne
  have hsum : r * x + r = r * (1 + x) := by ring
  rw [hsum]
  unfold dfiEquation27C
  rw [dfiEquation27LogFactor_eq_log_add_constant,
    dfiEquation27LogFactor_eq_log_add_constant,
    hughesYoungPureReducedStaticWeight_eq_scaled_powers
      T c u hh hk hrOne hrx]
  rw [Real.log_mul hr.ne' hOne.ne', Real.log_mul hr.ne' hx.ne']
  rw [show ((r * (1 + x) : ℝ) : ℂ) =
      (r : ℂ) * (1 + (x : ℂ)) by push_cast; rfl,
    show ((r * x : ℝ) : ℂ) = (r : ℂ) * (x : ℂ) by
      push_cast; rfl]
  have hone : (1 + (x : ℂ)) = (((1 + x : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [hone]
  rw [Complex.mul_cpow_ofReal_nonneg hr.le hOne.le,
    Complex.mul_cpow_ofReal_nonneg hr.le hx.le]
  unfold hughesYoungCriticalAffineBetaIntegrand afeCriticalPoint
  dsimp only
  push_cast
  ring_nf

theorem norm_hughesYoungPureReducedStaticScale_shiftFactor_eq
    (T c u : ℝ) (h k : ℕ) {r : ℝ} (hr : 0 < r) :
    ‖hughesYoungPureReducedStaticScaleConstant T c u h k *
        (r : ℂ) ^
          (-((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) *
        (r : ℂ) ^
          (-((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)))‖ =
      ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
        r ^ (-1 - 2 * c) := by
  rw [norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp only [neg_re, add_re, ofReal_re, mul_re, I_re, I_im,
    ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
  norm_num [Complex.div_re, Complex.normSq]
  calc
    ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          r ^ (-c + -(1 / 2)) * r ^ (-c + -(1 / 2)) =
        ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          (r ^ (-c + -(1 / 2)) * r ^ (-c + -(1 / 2))) := by ring
    _ = ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          r ^ ((-c + -(1 / 2)) + (-c + -(1 / 2))) := by
      congr 1
      exact (Real.rpow_add hr (-c + -(1 / 2)) (-c + -(1 / 2))).symm
    _ = _ := by
      congr 2
      ring

/-- Real-valued dilation of an `Ioi 0` integral. -/
theorem integral_Ioi_eq_mul_integral_dilate_real
    (g : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ y in Set.Ioi (0 : ℝ), g y) =
      r * ∫ x in Set.Ioi (0 : ℝ), g (r * x) := by
  have hs := MeasureTheory.integral_comp_mul_left_Ioi g 0 hr
  rw [mul_zero, smul_eq_mul] at hs
  calc
    (∫ y in Set.Ioi (0 : ℝ), g y) =
        r * (r⁻¹ * ∫ y in Set.Ioi (0 : ℝ), g y) := by
          field_simp [hr.ne']
    _ = r * ∫ x in Set.Ioi (0 : ℝ), g (r * x) := by rw [hs]

/-- Quantitative absolute-mass bound for the pure physical DFI central
slice.  This is stronger than a bound on the norm of its integral and is
therefore the correct majorant for the lower-endpoint correction. -/
theorem integral_norm_dfiEquation27C_pureReducedStaticWeight_posShift_le
    {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4) (T u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b qx qy : ℕ)
    {r : ℝ} (hr : 1 ≤ r) :
    (∫ y in Set.Ioi (0 : ℝ),
      ‖dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖) ≤
      ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
        r ^ (-2 * c) *
        (2312 *
            (1 +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) ^ 2 +
          9 *
            (1 +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) ^ 2 *
            c⁻¹ ^ 3) := by
  let S : ℝ := 1 +
    ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
    ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖
  let G : ℝ → ℝ := fun y =>
    ‖dfiEquation27C a b qx qy
      (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [show (∫ y in Set.Ioi (0 : ℝ),
      ‖dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖) =
      ∫ y in Set.Ioi (0 : ℝ), G y by rfl]
  rw [integral_Ioi_eq_mul_integral_dilate_real G hr0]
  have hpoint : ∀ x ∈ Set.Ioi (0 : ℝ),
      G (r * x) ≤
        (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          r ^ (-1 - 2 * c)) *
        hughesYoungCriticalAffineBetaMajorant c S x := by
    intro x hx
    have hx0 : 0 < x := hx
    have heq := dfiEquation27C_pureReducedStaticWeight_dilate_eq_criticalBeta
      T c u hh hk a b qx qy hr0 hx0
    have hbeta := norm_hughesYoungCriticalAffineBetaIntegrand_le_majorant
      hc hc4 hx0
      (t := 0) (u := u)
      (CX := (Real.log r : ℂ) + dfiEquation27LogConstant b qy)
      (COne := (Real.log r : ℂ) + dfiEquation27LogConstant a qx)
    dsimp only [G]
    rw [heq, norm_mul,
      norm_hughesYoungPureReducedStaticScale_shiftFactor_eq T c u h k hr0]
    simpa only [S] using
      mul_le_mul_of_nonneg_left hbeta
        (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hr0.le _))
  have hmajorInt := integrable_hughesYoungCriticalAffineBetaMajorant
    (S := S) hc
  have hmajorOn : IntegrableOn (fun x : ℝ =>
      (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
        r ^ (-1 - 2 * c)) *
        hughesYoungCriticalAffineBetaMajorant c S x) (Set.Ioi 0) :=
    hmajorInt.integrableOn.const_mul _
  have hmono : (∫ x in Set.Ioi (0 : ℝ), G (r * x)) ≤
      ∫ x in Set.Ioi (0 : ℝ),
        (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          r ^ (-1 - 2 * c)) *
          hughesYoungCriticalAffineBetaMajorant c S x := by
    apply MeasureTheory.integral_mono_ae
    · have hpureNorm :=
        (integrableOn_dfiEquation27C_pureReducedStaticWeight_posShift
          hc (hc4.trans_lt (by norm_num)) T u hh hk a b qx qy hr0).norm
      have hcomp := (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
          (fun y : ℝ =>
            ‖dfiEquation27C a b qx qy
              (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖)
          0 hr0).mpr (by simpa only [mul_zero] using hpureNorm)
      simpa only [G, mul_zero] using hcomp
    · exact hmajorOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hpoint x hx
  calc
    r * (∫ x in Set.Ioi (0 : ℝ), G (r * x)) ≤
        r * (∫ x in Set.Ioi (0 : ℝ),
          (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
            r ^ (-1 - 2 * c)) *
            hughesYoungCriticalAffineBetaMajorant c S x) :=
      mul_le_mul_of_nonneg_left hmono hr0.le
    _ = r * (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          r ^ (-1 - 2 * c)) *
        (∫ x in Set.Ioi (0 : ℝ),
          hughesYoungCriticalAffineBetaMajorant c S x) := by
      rw [MeasureTheory.integral_const_mul]
      ring
    _ ≤ r * (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          r ^ (-1 - 2 * c)) *
        (∫ x : ℝ, hughesYoungCriticalAffineBetaMajorant c S x) := by
      have hrestrict := MeasureTheory.setIntegral_le_integral
        (s := Set.Ioi (0 : ℝ)) hmajorInt
        (Filter.Eventually.of_forall fun x =>
          hughesYoungCriticalAffineBetaMajorant_nonneg)
      exact mul_le_mul_of_nonneg_left hrestrict
        (mul_nonneg hr0.le (mul_nonneg (norm_nonneg _)
          (Real.rpow_nonneg hr0.le _)))
    _ = ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
        r ^ (-2 * c) *
        (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3) := by
      rw [integral_hughesYoungCriticalAffineBetaMajorant_eq hc]
      have hrpow : r ^ (-2 * c) = r * r ^ (-1 - 2 * c) := by
        calc
          r ^ (-2 * c) = r ^ ((1 : ℝ) + (-1 - 2 * c)) := by ring_nf
          _ = r ^ (1 : ℝ) * r ^ (-1 - 2 * c) :=
            Real.rpow_add hr0 1 (-1 - 2 * c)
          _ = r * r ^ (-1 - 2 * c) := by rw [Real.rpow_one]
      rw [hrpow]
      ring
    _ = _ := by rfl

/-- Absolute integrability of the pure negative signed-shift kernel in the
coordinate convention used by `dfiSignedCentralSeries`. -/
theorem integrableOn_dfiEquation27C_swappedPureReducedStaticWeight_posShift
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (T u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b qx qy : ℕ)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn
      (fun y : ℝ => dfiEquation27C b a qy qx
        (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
        (y + r) y)
      (Set.Ioi 0) := by
  rw [dfiSwapWeight_hughesYoungPureReducedStaticWeight T c u h k]
  exact integrableOn_dfiEquation27C_pureReducedStaticWeight_posShift
    hc hcHalf T u hk hh b a qy qx hr

/-- The pure negative signed-shift slice has the same critical-beta mass
as the positive slice, with the two DFI logarithmic coordinates swapped. -/
theorem integral_norm_dfiEquation27C_swappedPureReducedStaticWeight_posShift_le
    {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4) (T u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b qx qy : ℕ)
    {r : ℝ} (hr : 1 ≤ r) :
    (∫ y in Set.Ioi (0 : ℝ),
      ‖dfiEquation27C b a qy qx
        (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
        (y + r) y‖) ≤
      ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
        r ^ (-2 * c) *
        (2312 *
            (1 +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖ +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖) ^ 2 +
          9 *
            (1 +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖ +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖) ^ 2 *
            c⁻¹ ^ 3) := by
  rw [dfiSwapWeight_hughesYoungPureReducedStaticWeight T c u h k]
  have hbound :=
    integral_norm_dfiEquation27C_pureReducedStaticWeight_posShift_le
      hc hc4 T u hk hh b a qy qx hr
  rw [hughesYoungPureReducedStaticScaleConstant_swap T c u h k] at hbound
  exact hbound

theorem hughesYoungDyadicStep_nonneg (x : ℝ) :
    0 ≤ hughesYoungDyadicStep x := by
  unfold hughesYoungDyadicStep
  exact Real.smoothTransition.nonneg _

theorem hughesYoungDyadicStep_le_one (x : ℝ) :
    hughesYoungDyadicStep x ≤ 1 := by
  unfold hughesYoungDyadicStep
  exact Real.smoothTransition.le_one _

/-- The Hughes--Young smooth step is decreasing.  Keeping this elementary
order fact explicit is useful at the upper dyadic endpoint, where the
finite partial partition is compared with the locally finite infinite
partition before any central-series norm is taken. -/
theorem antitone_hughesYoungDyadicStep :
    Antitone hughesYoungDyadicStep := by
  intro x y hxy
  unfold hughesYoungDyadicStep
  apply Real.smoothTransition.monotone
  apply (div_le_div_iff_of_pos_right
    (sub_pos.mpr one_lt_hughesYoungDyadicRatio)).2
  linarith

/-- The scalar multiplier carried by the upper endpoint of the finite
two-dimensional dyadic partition.  The first summand is the tail in the
left coordinate while the right coordinate remains in the complete
nonnegative-index partition; the second is the remaining finite left
factor times the right-coordinate tail.  This disjoint algebraic split is
the form needed for the cancellation-preserving terminal contour move. -/
noncomputable def hughesYoungTerminalDyadicMultiplier
    (K : ℕ) (x y : ℝ) : ℝ :=
  (1 - hughesYoungDyadicStep
      (x / hughesYoungDyadicRatio ^ (K + 1))) *
    (1 - hughesYoungDyadicStep (y * hughesYoungDyadicRatio)) +
  (hughesYoungDyadicStep
      (x / hughesYoungDyadicRatio ^ (K + 1)) -
      hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) *
    (1 - hughesYoungDyadicStep
      (y / hughesYoungDyadicRatio ^ (K + 1)))

/-- Exact scalar endpoint algebra: the infinite lower-complete multiplier
minus its depth-`K` rectangle is the two-piece terminal multiplier above.
No estimate or limiting assertion is used here. -/
theorem hughesYoung_lowerComplete_sub_finite_multiplier_eq_terminal
    (K : ℕ) (x y : ℝ) :
    (1 - hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) *
        (1 - hughesYoungDyadicStep (y * hughesYoungDyadicRatio)) -
      (hughesYoungDyadicStep
          (x / hughesYoungDyadicRatio ^ (K + 1)) -
        hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) *
      (hughesYoungDyadicStep
          (y / hughesYoungDyadicRatio ^ (K + 1)) -
        hughesYoungDyadicStep (y * hughesYoungDyadicRatio)) =
      hughesYoungTerminalDyadicMultiplier K x y := by
  unfold hughesYoungTerminalDyadicMultiplier
  ring

/-- Exact positive-quadrant formula for the terminal Mellin correction.
This identifies the missing source with the common Hughes--Young Mellin
monomial times the genuine two-piece terminal cutoff. -/
theorem hughesYoungTerminalReducedMellinCorrection_eq_scaled_multiplier
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (K : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hughesYoungTerminalReducedMellinCorrection
        T t c u h k K x y =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        (hughesYoungTerminalDyadicMultiplier K x y : ℂ) *
        (x : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (y : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) := by
  unfold hughesYoungTerminalReducedMellinCorrection
    hughesYoungLowerCompleteReducedMellinWeight
  rw [if_pos ⟨hx, hy⟩,
    hughesYoungFiniteReassembledReducedMellinWeight_eq_endpoint
      T t c u hh hk K hx hy]
  rw [← hughesYoung_lowerComplete_sub_finite_multiplier_eq_terminal K x y]
  push_cast
  ring

/-- On the positive quadrant the terminal multiplier is nonnegative.  This
is the order-theoretic input needed for monotone/Tonelli treatment of the
beyond-depth family. -/
theorem hughesYoungTerminalDyadicMultiplier_nonneg
    (K : ℕ) {x y : ℝ} (hx : 0 ≤ x) :
    0 ≤ hughesYoungTerminalDyadicMultiplier K x y := by
  have hpow : 1 ≤ hughesYoungDyadicRatio ^ (K + 1) :=
    one_le_pow₀ one_lt_hughesYoungDyadicRatio.le
  have hxOrder :
      x / hughesYoungDyadicRatio ^ (K + 1) ≤
        x * hughesYoungDyadicRatio := by
    calc
      x / hughesYoungDyadicRatio ^ (K + 1) ≤ x :=
        div_le_self hx hpow
      _ ≤ x * hughesYoungDyadicRatio := by
        nlinarith [one_lt_hughesYoungDyadicRatio]
  have hstepX :
      hughesYoungDyadicStep (x * hughesYoungDyadicRatio) ≤
        hughesYoungDyadicStep
          (x / hughesYoungDyadicRatio ^ (K + 1)) :=
    antitone_hughesYoungDyadicStep hxOrder
  unfold hughesYoungTerminalDyadicMultiplier
  exact add_nonneg
    (mul_nonneg
      (sub_nonneg.mpr (hughesYoungDyadicStep_le_one _))
      (sub_nonneg.mpr (hughesYoungDyadicStep_le_one _)))
    (mul_nonneg (sub_nonneg.mpr hstepX)
      (sub_nonneg.mpr (hughesYoungDyadicStep_le_one _)))

/-- The two terminal pieces form a subpartition: their total multiplier is
at most one.  This sharper estimate avoids the artificial factor two that
would result from bounding the two coordinate tails independently. -/
theorem hughesYoungTerminalDyadicMultiplier_le_one
    (K : ℕ) {x y : ℝ} (hx : 0 ≤ x) :
    hughesYoungTerminalDyadicMultiplier K x y ≤ 1 := by
  have hpow : 1 ≤ hughesYoungDyadicRatio ^ (K + 1) :=
    one_le_pow₀ one_lt_hughesYoungDyadicRatio.le
  have hxOrder :
      x / hughesYoungDyadicRatio ^ (K + 1) ≤
        x * hughesYoungDyadicRatio := by
    calc
      x / hughesYoungDyadicRatio ^ (K + 1) ≤ x :=
        div_le_self hx hpow
      _ ≤ x * hughesYoungDyadicRatio := by
        nlinarith [one_lt_hughesYoungDyadicRatio]
  let Ax := hughesYoungDyadicStep
    (x / hughesYoungDyadicRatio ^ (K + 1))
  let ax := hughesYoungDyadicStep (x * hughesYoungDyadicRatio)
  let Ay := hughesYoungDyadicStep
    (y / hughesYoungDyadicRatio ^ (K + 1))
  let ay := hughesYoungDyadicStep (y * hughesYoungDyadicRatio)
  have hAx1 : Ax ≤ 1 := hughesYoungDyadicStep_le_one _
  have hAy0 : 0 ≤ Ay := hughesYoungDyadicStep_nonneg _
  have hax0 : 0 ≤ ax := hughesYoungDyadicStep_nonneg _
  have hay0 : 0 ≤ ay := hughesYoungDyadicStep_nonneg _
  have haxAx : ax ≤ Ax := antitone_hughesYoungDyadicStep hxOrder
  have hfirst : (1 - Ax) * (1 - ay) ≤ 1 - Ax := by
    have hfactor : 1 - ay ≤ 1 := by linarith
    calc
      (1 - Ax) * (1 - ay) ≤ (1 - Ax) * 1 :=
        mul_le_mul_of_nonneg_left hfactor (sub_nonneg.mpr hAx1)
      _ = 1 - Ax := mul_one _
  have hsecond : (Ax - ax) * (1 - Ay) ≤ Ax - ax := by
    have hfactor : 1 - Ay ≤ 1 := by linarith
    calc
      (Ax - ax) * (1 - Ay) ≤ (Ax - ax) * 1 :=
        mul_le_mul_of_nonneg_left hfactor (sub_nonneg.mpr haxAx)
      _ = Ax - ax := mul_one _
  change (1 - Ax) * (1 - ay) + (Ax - ax) * (1 - Ay) ≤ 1
  linarith

/-- The upper-end correction vanishes throughout the finite square covered
by the terminal dyadic scale.  Consequently a nonzero terminal term really
does come from at least one coordinate beyond that scale. -/
theorem hughesYoungTerminalDyadicMultiplier_eq_zero_of_le_scale
    (K : ℕ) {x y : ℝ}
    (hx : x ≤ hughesYoungDyadicRatio ^ (K + 1))
    (hy : y ≤ hughesYoungDyadicRatio ^ (K + 1)) :
    hughesYoungTerminalDyadicMultiplier K x y = 0 := by
  have hpow : 0 < hughesYoungDyadicRatio ^ (K + 1) :=
    pow_pos hughesYoungDyadicRatio_pos _
  have hxDiv : x / hughesYoungDyadicRatio ^ (K + 1) ≤ 1 :=
    (div_le_one hpow).2 hx
  have hyDiv : y / hughesYoungDyadicRatio ^ (K + 1) ≤ 1 :=
    (div_le_one hpow).2 hy
  unfold hughesYoungTerminalDyadicMultiplier
  rw [hughesYoungDyadicStep_eq_one hxDiv,
    hughesYoungDyadicStep_eq_one hyDiv]
  ring

theorem terminal_scale_lt_left_or_right_of_multiplier_ne_zero
    (K : ℕ) {x y : ℝ}
    (hterm : hughesYoungTerminalDyadicMultiplier K x y ≠ 0) :
    hughesYoungDyadicRatio ^ (K + 1) < x ∨
      hughesYoungDyadicRatio ^ (K + 1) < y := by
  by_contra hxy
  push Not at hxy
  exact hterm
    (hughesYoungTerminalDyadicMultiplier_eq_zero_of_le_scale K hxy.1 hxy.2)

/-- A nonzero lower-end step forces its physical coordinate below one. -/
theorem lt_one_of_hughesYoungDyadicStep_mul_ratio_ne_zero
    {x : ℝ} (hstep :
      hughesYoungDyadicStep (x * hughesYoungDyadicRatio) ≠ 0) :
    x < 1 := by
  by_contra hx
  have hx1 : 1 ≤ x := le_of_not_gt hx
  apply hstep
  apply hughesYoungDyadicStep_eq_zero
  calc
    hughesYoungDyadicRatio = 1 * hughesYoungDyadicRatio := by ring
    _ ≤ x * hughesYoungDyadicRatio := by
      exact mul_le_mul_of_nonneg_right hx1 hughesYoungDyadicRatio_pos.le

/-- On a positive central shift, the lower endpoint can occur only on the
right coordinate, and then its physical-height Fourier frequency is at
least `1/2`. -/
theorem one_half_le_abs_log_div_of_pos_shift_right_lt_one
    {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) (hr : 1 ≤ r)
    (hshift : x - y = r) (hy1 : y < 1) :
    (1 / 2 : ℝ) ≤ |Real.log (y / x)| := by
  have hyx : y ≤ x := by linarith
  have hyr : y ≤ r := hy1.le.trans hr
  have hxle : x ≤ 2 * r := by linarith
  have hratio : (1 / 2 : ℝ) ≤ |x - y| / max x y := by
    rw [max_eq_left hyx, abs_of_nonneg (sub_nonneg.mpr hyx), hshift]
    rw [le_div_iff₀ hx]
    linarith
  exact hratio.trans (abs_sub_div_max_le_abs_log_div hx hy)

/-- The symmetric negative-shift lower endpoint has the same uniform
Fourier separation. -/
theorem one_half_le_abs_log_div_of_neg_shift_left_lt_one
    {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) (hr : r ≤ -1)
    (hshift : x - y = r) (hx1 : x < 1) :
    (1 / 2 : ℝ) ≤ |Real.log (y / x)| := by
  have hxy : x ≤ y := by linarith
  have hxneg : x ≤ -r := hx1.le.trans (by linarith)
  have hyle : y ≤ 2 * (-r) := by linarith
  have hratio : (1 / 2 : ℝ) ≤ |x - y| / max x y := by
    rw [max_eq_right hxy, abs_of_nonpos (sub_nonpos.mpr hxy), hshift]
    rw [le_div_iff₀ hy]
    linarith
  exact hratio.trans (abs_sub_div_max_le_abs_log_div hx hy)

/-- Equation (65) with the fixed lower-endpoint frequency gap solved for
the Fourier transform itself. -/
theorem norm_hughesYoungHeightTransform_le_of_one_half_le_frequency
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u ξ : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hu : |u| ≤ T / 8) (hξ : (1 / 2 : ℝ) ≤ |ξ|) :
    ‖hughesYoungHeightTransform T c u ξ‖ ≤
      (2 : ℝ) ^ j *
        ((15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j))) := by
  let E : ℝ := (15 * T / 4) *
    (c⁻¹ * Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 +
        4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
      (25 + 8 * u ^ 2) ^ 4 *
      hughesYoungHeightInputDerivativeConstant Cw j *
      (((T / 16)⁻¹ * (1 + |u|)) ^ j))
  have hraw : |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤ E :=
    h65 j T c u ξ hT hc hc1 hu
  have hhalf : (1 / 2 : ℝ) ^ j *
      ‖hughesYoungHeightTransform T c u ξ‖ ≤ E := by
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num) hξ j) (norm_nonneg _)).trans hraw
  calc
    ‖hughesYoungHeightTransform T c u ξ‖ =
        (2 : ℝ) ^ j * ((1 / 2 : ℝ) ^ j *
          ‖hughesYoungHeightTransform T c u ξ‖) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (2 : ℝ) ^ j * E := by gcongr
    _ = _ := by rfl

/-- Quantitative endpoint decay for a positive signed central shift. -/
theorem norm_hughesYoungHeightTransform_lowerEndpoint_posShift_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u x y r : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hu : |u| ≤ T / 8) (hx : 0 < x) (hy : 0 < y)
    (hr : 1 ≤ r) (hshift : x - y = r)
    (hstep : hughesYoungDyadicStep
      (y * hughesYoungDyadicRatio) ≠ 0) :
    ‖hughesYoungHeightTransform T c u (Real.log (y / x))‖ ≤
      (2 : ℝ) ^ j *
        ((15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j))) := by
  apply norm_hughesYoungHeightTransform_le_of_one_half_le_frequency
    h65 j hT hc hc1 hu
  exact one_half_le_abs_log_div_of_pos_shift_right_lt_one
    hx hy hr hshift
      (lt_one_of_hughesYoungDyadicStep_mul_ratio_ne_zero hstep)

/-- Quantitative endpoint decay for a negative signed central shift. -/
theorem norm_hughesYoungHeightTransform_lowerEndpoint_negShift_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u x y r : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hu : |u| ≤ T / 8) (hx : 0 < x) (hy : 0 < y)
    (hr : r ≤ -1) (hshift : x - y = r)
    (hstep : hughesYoungDyadicStep
      (x * hughesYoungDyadicRatio) ≠ 0) :
    ‖hughesYoungHeightTransform T c u (Real.log (y / x))‖ ≤
      (2 : ℝ) ^ j *
        ((15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j))) := by
  apply norm_hughesYoungHeightTransform_le_of_one_half_le_frequency
    h65 j hT hc hc1 hu
  exact one_half_le_abs_log_div_of_neg_shift_left_lt_one
    hx hy hr hshift
      (lt_one_of_hughesYoungDyadicStep_mul_ratio_ne_zero hstep)

/-! ## Exact lower-endpoint source -/

/-- Inclusion-exclusion multiplier left by the missing negative-index
dyadic boxes. -/
noncomputable def hughesYoungLowerBoundaryMultiplier (x y : ℝ) : ℝ :=
  hughesYoungDyadicStep (x * hughesYoungDyadicRatio) +
    hughesYoungDyadicStep (y * hughesYoungDyadicRatio) -
    hughesYoungDyadicStep (x * hughesYoungDyadicRatio) *
      hughesYoungDyadicStep (y * hughesYoungDyadicRatio)

theorem hughesYoungLowerBoundaryMultiplier_posShift
    {x y r : ℝ} (hy : 0 < y) (hr : 1 ≤ r)
    (hshift : x - y = r) :
    hughesYoungLowerBoundaryMultiplier x y =
      hughesYoungDyadicStep (y * hughesYoungDyadicRatio) := by
  have hx1 : 1 ≤ x := by linarith
  have hstepX : hughesYoungDyadicStep
      (x * hughesYoungDyadicRatio) = 0 := by
    apply hughesYoungDyadicStep_eq_zero
    calc
      hughesYoungDyadicRatio = 1 * hughesYoungDyadicRatio := by ring
      _ ≤ x * hughesYoungDyadicRatio :=
        mul_le_mul_of_nonneg_right hx1 hughesYoungDyadicRatio_pos.le
  unfold hughesYoungLowerBoundaryMultiplier
  rw [hstepX]
  ring

theorem hughesYoungLowerBoundaryMultiplier_negShift
    {x y r : ℝ} (hx : 0 < x) (hr : r ≤ -1)
    (hshift : x - y = r) :
    hughesYoungLowerBoundaryMultiplier x y =
      hughesYoungDyadicStep (x * hughesYoungDyadicRatio) := by
  have hy1 : 1 ≤ y := by linarith
  have hstepY : hughesYoungDyadicStep
      (y * hughesYoungDyadicRatio) = 0 := by
    apply hughesYoungDyadicStep_eq_zero
    calc
      hughesYoungDyadicRatio = 1 * hughesYoungDyadicRatio := by ring
      _ ≤ y * hughesYoungDyadicRatio :=
        mul_le_mul_of_nonneg_right hy1 hughesYoungDyadicRatio_pos.le
  unfold hughesYoungLowerBoundaryMultiplier
  rw [hstepY]
  ring

theorem hughesYoungLowerBoundaryMultiplier_nonneg
    (x y : ℝ) : 0 ≤ hughesYoungLowerBoundaryMultiplier x y := by
  let sx := hughesYoungDyadicStep (x * hughesYoungDyadicRatio)
  let sy := hughesYoungDyadicStep (y * hughesYoungDyadicRatio)
  have hsx0 : 0 ≤ sx := hughesYoungDyadicStep_nonneg _
  have hsx1 : sx ≤ 1 := hughesYoungDyadicStep_le_one _
  have hsy0 : 0 ≤ sy := hughesYoungDyadicStep_nonneg _
  change 0 ≤ sx + sy - sx * sy
  nlinarith

theorem hughesYoungLowerBoundaryMultiplier_le_one
    (x y : ℝ) : hughesYoungLowerBoundaryMultiplier x y ≤ 1 := by
  let sx := hughesYoungDyadicStep (x * hughesYoungDyadicRatio)
  let sy := hughesYoungDyadicStep (y * hughesYoungDyadicRatio)
  have hsx0 : 0 ≤ sx := hughesYoungDyadicStep_nonneg _
  have hsx1 : sx ≤ 1 := hughesYoungDyadicStep_le_one _
  have hsy0 : 0 ≤ sy := hughesYoungDyadicStep_nonneg _
  have hsy1 : sy ≤ 1 := hughesYoungDyadicStep_le_one _
  change sx + sy - sx * sy ≤ 1
  nlinarith [mul_nonneg (sub_nonneg.mpr hsx1) (sub_nonneg.mpr hsy1)]

theorem hughesYoungLowerBoundaryReducedMellinCorrection_eq_multiplier_mul
    (T t c u : ℝ) (h k : ℕ) (x y : ℝ) :
    hughesYoungLowerBoundaryReducedMellinCorrection
        T t c u h k x y =
      (hughesYoungLowerBoundaryMultiplier x y : ℂ) *
        hughesYoungPureReducedMellinWeight T t c u h k x y := by
  by_cases hx : 0 < x
  · by_cases hy : 0 < y
    · unfold hughesYoungLowerBoundaryReducedMellinCorrection
        hughesYoungLowerCompleteReducedMellinWeight
        hughesYoungLowerBoundaryMultiplier
      rw [hughesYoungPureReducedMellinWeight_of_pos
        T t c u h k hx hy]
      simp only [hx, hy, and_self, if_true]
      push_cast
      ring
    · have hy' : y ≤ 0 := le_of_not_gt hy
      unfold hughesYoungLowerBoundaryReducedMellinCorrection
        hughesYoungLowerCompleteReducedMellinWeight
      rw [hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_right
        T t c u h k hy']
      simp only [hy, and_false, if_false, sub_zero, mul_zero]
  · have hx' : x ≤ 0 := le_of_not_gt hx
    unfold hughesYoungLowerBoundaryReducedMellinCorrection
      hughesYoungLowerCompleteReducedMellinWeight
    rw [hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_left
      T t c u h k hx']
    simp only [hx, false_and, if_false, sub_zero, mul_zero]

/-- The lower endpoint keeps the same Fourier character as the pure source;
only its height-independent inclusion-exclusion multiplier changes. -/
theorem heightWeight_mul_hughesYoungLowerBoundaryReducedMellinCorrection_eq
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k x y =
      ((hughesYoungLowerBoundaryMultiplier x y : ℝ) : ℂ) *
        hughesYoungPureReducedStaticWeight T c u h k x y *
        Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) *
        hughesYoungHeightFourierInput T c u t := by
  rw [hughesYoungLowerBoundaryReducedMellinCorrection_eq_multiplier_mul]
  calc
    (hughesYoungHeightWeight T t : ℂ) *
        ((hughesYoungLowerBoundaryMultiplier x y : ℂ) *
          hughesYoungPureReducedMellinWeight T t c u h k x y) =
      (hughesYoungLowerBoundaryMultiplier x y : ℂ) *
        ((hughesYoungHeightWeight T t : ℂ) *
          hughesYoungPureReducedMellinWeight T t c u h k x y) := by ring
    _ = _ := by
      rw [heightWeight_mul_hughesYoungPureReducedMellinWeight_eq_static_mul_phase
        T t c u hh hk hx hy]
      ring

/-- Exact height integration of the lower endpoint. -/
theorem integral_heightWeight_mul_hughesYoungLowerBoundaryReducedMellinCorrection_eq
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k x y) =
      ((hughesYoungLowerBoundaryMultiplier x y : ℝ) : ℂ) *
        hughesYoungPureReducedStaticWeight T c u h k x y *
        hughesYoungHeightTransform T c u (Real.log (y / x)) := by
  simp_rw [heightWeight_mul_hughesYoungLowerBoundaryReducedMellinCorrection_eq
    T _ c u hh hk hx hy]
  rw [show (fun t : ℝ =>
      ((hughesYoungLowerBoundaryMultiplier x y : ℝ) : ℂ) *
        hughesYoungPureReducedStaticWeight T c u h k x y *
        Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) *
        hughesYoungHeightFourierInput T c u t) =
      fun t : ℝ =>
        (((hughesYoungLowerBoundaryMultiplier x y : ℝ) : ℂ) *
          hughesYoungPureReducedStaticWeight T c u h k x y) *
          (Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) *
            hughesYoungHeightFourierInput T c u t) by
      funext t
      ring]
  rw [integral_const_mul, ← hughesYoungHeightTransform_eq_integral]

/-! ## Height-integrated endpoint weight inside DFI equation (27) -/

/-- The literal lower-endpoint weight after the physical-height integral
has been evaluated.  It retains the DFI variables and is therefore the
object to which the equation-(27) central integral is applied. -/
noncomputable def hughesYoungLowerBoundaryHeightIntegratedWeight
    (T c u : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  ((hughesYoungLowerBoundaryMultiplier x y : ℝ) : ℂ) *
    hughesYoungPureReducedStaticWeight T c u h k x y *
    hughesYoungHeightTransform T c u (Real.log (y / x))

/-- Pointwise evaluation of the height integral in the exact notation used
by the DFI central integral. -/
theorem integral_heightWeight_mul_hughesYoungLowerBoundaryReducedMellinCorrection_eq_weight
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k x y) =
      hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k x y := by
  rw [integral_heightWeight_mul_hughesYoungLowerBoundaryReducedMellinCorrection_eq
    T c u hh hk hx hy]
  rfl

/-- At fixed positive physical coordinates the physical-height integral
commutes exactly with the two equation-(27) logarithmic factors. -/
theorem integral_heightWeight_mul_dfiEquation27C_lowerBoundaryCorrection_eq
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
      dfiEquation27C a b qx qy
        (hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k) x y) =
      dfiEquation27C a b qx qy
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) x y := by
  rw [show (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      dfiEquation27C a b qx qy
        (hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k) x y) =
      fun t =>
        (dfiEquation27LogFactor a qx x *
          dfiEquation27LogFactor b qy y) *
        ((hughesYoungHeightWeight T t : ℂ) *
          hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k x y) by
    funext t
    unfold dfiEquation27C
    ring]
  rw [integral_const_mul,
    integral_heightWeight_mul_hughesYoungLowerBoundaryReducedMellinCorrection_eq_weight
      T c u hh hk hx hy]
  unfold dfiEquation27C
  ring

theorem hughesYoungLowerBoundaryReducedMellinCorrection_eq_zero_of_nonpos_right
    (T t c u : ℝ) (h k : ℕ) {x y : ℝ} (hy : y ≤ 0) :
    hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k x y = 0 := by
  rw [hughesYoungLowerBoundaryReducedMellinCorrection_eq_multiplier_mul]
  rw [hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_right
    T t c u h k hy]
  simp

/-- The joint physical/height kernel for the lower endpoint on the
positive shifted line.  Unlike the cleaned finite-box kernel, its physical
support is not compact, so its Fubini theorem below uses the critical-beta
absolute majorant. -/
noncomputable def hughesYoungLowerBoundaryCentralHeightIntegrand
    (T c u : ℝ) (h k : ℕ) (r : ℝ) (a b qx qy : ℕ)
    (y t : ℝ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    dfiEquation27C a b qx qy
      (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k)
      (y + r) y

/-- Exact separation of the lower-endpoint joint kernel into its physical
critical-beta kernel, inclusion-exclusion multiplier, Fourier character,
and compactly supported height input. -/
theorem hughesYoungLowerBoundaryCentralHeightIntegrand_eq
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (a b qx qy : ℕ) (y t : ℝ) :
    hughesYoungLowerBoundaryCentralHeightIntegrand
        T c u h k r a b qx qy y t =
      ((hughesYoungLowerBoundaryMultiplier (y + r) y : ℝ) : ℂ) *
        dfiEquation27C a b qx qy
          (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y *
        Complex.exp ((((t * Real.log (y / (y + r)) : ℝ) : ℂ)) * I) *
        hughesYoungHeightFourierInput T c u t := by
  by_cases hy : 0 < y
  · have hyr : 0 < y + r := add_pos hy hr
    unfold hughesYoungLowerBoundaryCentralHeightIntegrand dfiEquation27C
    calc
      (hughesYoungHeightWeight T t : ℂ) *
          (dfiEquation27LogFactor a qx (y + r) *
            dfiEquation27LogFactor b qy y *
            hughesYoungLowerBoundaryReducedMellinCorrection
              T t c u h k (y + r) y) =
        (dfiEquation27LogFactor a qx (y + r) *
          dfiEquation27LogFactor b qy y) *
          ((hughesYoungHeightWeight T t : ℂ) *
            hughesYoungLowerBoundaryReducedMellinCorrection
              T t c u h k (y + r) y) := by ring
      _ = _ := by
        rw [heightWeight_mul_hughesYoungLowerBoundaryReducedMellinCorrection_eq
          T t c u hh hk hyr hy]
        ring
  · have hy' : y ≤ 0 := le_of_not_gt hy
    unfold hughesYoungLowerBoundaryCentralHeightIntegrand dfiEquation27C
    rw [hughesYoungLowerBoundaryReducedMellinCorrection_eq_zero_of_nonpos_right
      T t c u h k hy']
    unfold hughesYoungPureReducedStaticWeight
    simp [hy]

/-- The height-independent equation-(27) critical-beta kernel, extended by
zero off the positive translated half-line, is integrable on the whole
physical line. -/
theorem integrable_dfiEquation27C_pureReducedStaticWeight_posShift
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (T u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b qx qy : ℕ)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : ℝ => dfiEquation27C a b qx qy
      (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y) := by
  apply (integrableOn_dfiEquation27C_pureReducedStaticWeight_posShift
    hc hcHalf T u hh hk a b qx qy hr).integrable_of_forall_notMem_eq_zero
  intro y hy
  have hy' : y ≤ 0 := le_of_not_gt hy
  unfold dfiEquation27C hughesYoungPureReducedStaticWeight
  simp [not_lt.mpr hy']

/-- Pointwise product majorant for the lower-endpoint joint kernel. -/
theorem norm_hughesYoungLowerBoundaryCentralHeightIntegrand_le
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (a b qx qy : ℕ) (y t : ℝ) :
    ‖hughesYoungLowerBoundaryCentralHeightIntegrand
        T c u h k r a b qx qy y t‖ ≤
      ‖dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖ *
        ‖hughesYoungHeightFourierInput T c u t‖ := by
  rw [hughesYoungLowerBoundaryCentralHeightIntegrand_eq
    T c u hh hk hr a b qx qy]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  have hm0 := hughesYoungLowerBoundaryMultiplier_nonneg (y + r) y
  have hm1 := hughesYoungLowerBoundaryMultiplier_le_one (y + r) y
  rw [abs_of_nonneg hm0]
  calc
    hughesYoungLowerBoundaryMultiplier (y + r) y *
          ‖dfiEquation27C a b qx qy
            (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖ *
          ‖hughesYoungHeightFourierInput T c u t‖ ≤
        1 * ‖dfiEquation27C a b qx qy
            (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖ *
          ‖hughesYoungHeightFourierInput T c u t‖ := by
      gcongr
    _ = _ := by ring

/-- Absolute integrability on the full physical-height product.  This is
the Tonelli/Fubini gate for the noncompact lower endpoint. -/
theorem integrable_uncurry_hughesYoungLowerBoundaryCentralHeightIntegrand
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hcHalf : c < 1 / 2) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (a b qx qy : ℕ) :
    Integrable (Function.uncurry
      (hughesYoungLowerBoundaryCentralHeightIntegrand
        T c u h k r a b qx qy)) := by
  let f : ℝ → ℂ := fun y => dfiEquation27C a b qx qy
    (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y
  let H : ℝ → ℂ := hughesYoungHeightFourierInput T c u
  have hf : Integrable f := by
    simpa only [f] using
      integrable_dfiEquation27C_pureReducedStaticWeight_posShift
        hc hcHalf T u hh hk a b qx qy hr
  have hH : Integrable (fun t : ℝ => ‖H t‖) := by
    simpa [H] using
      integrable_heightFourierInput_moment hT hc u 0
  have hmajor : Integrable (fun z : ℝ × ℝ => ‖f z.1‖ * ‖H z.2‖) :=
    hf.norm.mul_prod hH
  have hmult : Continuous (fun y : ℝ =>
      hughesYoungLowerBoundaryMultiplier (y + r) y) := by
    unfold hughesYoungLowerBoundaryMultiplier
    have hs : Continuous hughesYoungDyadicStep :=
      contDiff_hughesYoungDyadicStep.continuous
    have hsR : Continuous (fun y : ℝ =>
        hughesYoungDyadicStep ((y + r) * hughesYoungDyadicRatio)) :=
      hs.comp (by fun_prop)
    have hsY : Continuous (fun y : ℝ =>
        hughesYoungDyadicStep (y * hughesYoungDyadicRatio)) :=
      hs.comp (by fun_prop)
    exact (hsR.add hsY).sub (hsR.mul hsY)
  have hphase : StronglyMeasurable (fun z : ℝ × ℝ =>
      Complex.exp ((((z.2 * Real.log (z.1 / (z.1 + r)) : ℝ) : ℂ)) * I)) := by
    measurability
  have hmeas : AEStronglyMeasurable (Function.uncurry
      (hughesYoungLowerBoundaryCentralHeightIntegrand
        T c u h k r a b qx qy)) := by
    rw [show Function.uncurry
        (hughesYoungLowerBoundaryCentralHeightIntegrand
          T c u h k r a b qx qy) = fun z : ℝ × ℝ =>
        ((hughesYoungLowerBoundaryMultiplier (z.1 + r) z.1 : ℝ) : ℂ) *
          f z.1 *
          Complex.exp ((((z.2 * Real.log (z.1 / (z.1 + r)) : ℝ) : ℂ)) * I) *
          H z.2 by
      funext z
      exact hughesYoungLowerBoundaryCentralHeightIntegrand_eq
        T c u hh hk hr a b qx qy z.1 z.2]
    exact (((Complex.ofRealCLM.continuous.comp hmult).aestronglyMeasurable.comp_fst.mul
      hf.aestronglyMeasurable.comp_fst).mul
        hphase.aestronglyMeasurable).mul
          (continuous_hughesYoungHeightFourierInput T hc u).aestronglyMeasurable.comp_snd
  apply hmajor.mono' hmeas
  filter_upwards with z
  simpa only [f, H, Function.uncurry_apply_pair] using
    norm_hughesYoungLowerBoundaryCentralHeightIntegrand_le
      T c u hh hk hr a b qx qy z.1 z.2

theorem hughesYoungLowerBoundaryReducedMellinCorrection_eq_zero_of_nonpos_left
    (T t c u : ℝ) (h k : ℕ) {x y : ℝ} (hx : x ≤ 0) :
    hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k x y = 0 := by
  rw [hughesYoungLowerBoundaryReducedMellinCorrection_eq_multiplier_mul]
  rw [hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_left
    T t c u h k hx]
  simp

/-- Joint endpoint kernel in the exact coordinate-swapped convention used
for a negative signed DFI shift. -/
noncomputable def hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
    (T c u : ℝ) (h k : ℕ) (r : ℝ) (a b qx qy : ℕ)
    (y t : ℝ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    dfiEquation27C b a qy qx
      (dfiSwapWeight
        (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k))
      (y + r) y

/-- Exact separated form of the negative signed endpoint kernel. -/
theorem hughesYoungSwappedLowerBoundaryCentralHeightIntegrand_eq
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (a b qx qy : ℕ) (y t : ℝ) :
    hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
        T c u h k r a b qx qy y t =
      ((hughesYoungLowerBoundaryMultiplier y (y + r) : ℝ) : ℂ) *
        dfiEquation27C b a qy qx
          (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
          (y + r) y *
        Complex.exp ((((t * Real.log ((y + r) / y) : ℝ) : ℂ)) * I) *
        hughesYoungHeightFourierInput T c u t := by
  by_cases hy : 0 < y
  · have hyr : 0 < y + r := add_pos hy hr
    unfold hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
    rw [dfiEquation27C_swap, dfiEquation27C_swap]
    unfold dfiEquation27C
    calc
      (hughesYoungHeightWeight T t : ℂ) *
          (dfiEquation27LogFactor a qx y *
            dfiEquation27LogFactor b qy (y + r) *
            hughesYoungLowerBoundaryReducedMellinCorrection
              T t c u h k y (y + r)) =
        (dfiEquation27LogFactor a qx y *
          dfiEquation27LogFactor b qy (y + r)) *
          ((hughesYoungHeightWeight T t : ℂ) *
            hughesYoungLowerBoundaryReducedMellinCorrection
              T t c u h k y (y + r)) := by ring
      _ = _ := by
        rw [heightWeight_mul_hughesYoungLowerBoundaryReducedMellinCorrection_eq
          T t c u hh hk hy hyr]
        ring
  · have hy' : y ≤ 0 := le_of_not_gt hy
    unfold hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
    rw [dfiEquation27C_swap]
    unfold dfiEquation27C
    rw [hughesYoungLowerBoundaryReducedMellinCorrection_eq_zero_of_nonpos_left
      T t c u h k hy']
    unfold dfiSwapWeight hughesYoungPureReducedStaticWeight
    simp [hy]

/-- Whole-line integrability of the swapped pure critical-beta kernel. -/
theorem integrable_dfiEquation27C_swappedPureReducedStaticWeight_posShift
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (T u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b qx qy : ℕ)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : ℝ => dfiEquation27C b a qy qx
      (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
      (y + r) y) := by
  apply (integrableOn_dfiEquation27C_swappedPureReducedStaticWeight_posShift
    hc hcHalf T u hh hk a b qx qy hr).integrable_of_forall_notMem_eq_zero
  intro y hy
  have hy' : y ≤ 0 := le_of_not_gt hy
  rw [dfiEquation27C_swap]
  unfold dfiEquation27C hughesYoungPureReducedStaticWeight
  simp [not_lt.mpr hy']

theorem norm_hughesYoungSwappedLowerBoundaryCentralHeightIntegrand_le
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (a b qx qy : ℕ) (y t : ℝ) :
    ‖hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
        T c u h k r a b qx qy y t‖ ≤
      ‖dfiEquation27C b a qy qx
        (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
        (y + r) y‖ * ‖hughesYoungHeightFourierInput T c u t‖ := by
  rw [hughesYoungSwappedLowerBoundaryCentralHeightIntegrand_eq
    T c u hh hk hr a b qx qy]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  have hm0 := hughesYoungLowerBoundaryMultiplier_nonneg y (y + r)
  have hm1 := hughesYoungLowerBoundaryMultiplier_le_one y (y + r)
  rw [abs_of_nonneg hm0]
  calc
    hughesYoungLowerBoundaryMultiplier y (y + r) *
          ‖dfiEquation27C b a qy qx
            (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
            (y + r) y‖ * ‖hughesYoungHeightFourierInput T c u t‖ ≤
        1 * ‖dfiEquation27C b a qy qx
            (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
            (y + r) y‖ * ‖hughesYoungHeightFourierInput T c u t‖ := by
      gcongr
    _ = _ := by ring

/-- Absolute integrability of the negative signed endpoint joint kernel. -/
theorem integrable_uncurry_hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hcHalf : c < 1 / 2) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (a b qx qy : ℕ) :
    Integrable (Function.uncurry
      (hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
        T c u h k r a b qx qy)) := by
  let f : ℝ → ℂ := fun y => dfiEquation27C b a qy qx
    (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
    (y + r) y
  let H : ℝ → ℂ := hughesYoungHeightFourierInput T c u
  have hf : Integrable f := by
    simpa only [f] using
      integrable_dfiEquation27C_swappedPureReducedStaticWeight_posShift
        hc hcHalf T u hh hk a b qx qy hr
  have hH : Integrable (fun t : ℝ => ‖H t‖) := by
    simpa [H] using integrable_heightFourierInput_moment hT hc u 0
  have hmajor : Integrable (fun z : ℝ × ℝ => ‖f z.1‖ * ‖H z.2‖) :=
    hf.norm.mul_prod hH
  have hmult : Continuous (fun y : ℝ =>
      hughesYoungLowerBoundaryMultiplier y (y + r)) := by
    unfold hughesYoungLowerBoundaryMultiplier
    have hs : Continuous hughesYoungDyadicStep :=
      contDiff_hughesYoungDyadicStep.continuous
    have hsY : Continuous (fun y : ℝ =>
        hughesYoungDyadicStep (y * hughesYoungDyadicRatio)) :=
      hs.comp (by fun_prop)
    have hsR : Continuous (fun y : ℝ =>
        hughesYoungDyadicStep ((y + r) * hughesYoungDyadicRatio)) :=
      hs.comp (by fun_prop)
    exact (hsY.add hsR).sub (hsY.mul hsR)
  have hphase : StronglyMeasurable (fun z : ℝ × ℝ =>
      Complex.exp ((((z.2 * Real.log ((z.1 + r) / z.1) : ℝ) : ℂ)) * I)) := by
    measurability
  have hmeas : AEStronglyMeasurable (Function.uncurry
      (hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
        T c u h k r a b qx qy)) := by
    rw [show Function.uncurry
        (hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
          T c u h k r a b qx qy) = fun z : ℝ × ℝ =>
        ((hughesYoungLowerBoundaryMultiplier z.1 (z.1 + r) : ℝ) : ℂ) *
          f z.1 *
          Complex.exp ((((z.2 * Real.log ((z.1 + r) / z.1) : ℝ) : ℂ)) * I) *
          H z.2 by
      funext z
      exact hughesYoungSwappedLowerBoundaryCentralHeightIntegrand_eq
        T c u hh hk hr a b qx qy z.1 z.2]
    exact (((Complex.ofRealCLM.continuous.comp hmult).aestronglyMeasurable.comp_fst.mul
      hf.aestronglyMeasurable.comp_fst).mul
        hphase.aestronglyMeasurable).mul
          (continuous_hughesYoungHeightFourierInput T hc u).aestronglyMeasurable.comp_snd
  apply hmajor.mono' hmeas
  filter_upwards with z
  simpa only [f, H, Function.uncurry_apply_pair] using
    norm_hughesYoungSwappedLowerBoundaryCentralHeightIntegrand_le
      T c u hh hk hr a b qx qy z.1 z.2

theorem hughesYoungLowerBoundaryHeightIntegratedWeight_eq_zero_of_nonpos_right
    (T c u : ℝ) (h k : ℕ) {x y : ℝ} (hy : y ≤ 0) :
    hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k x y = 0 := by
  unfold hughesYoungLowerBoundaryHeightIntegratedWeight
    hughesYoungPureReducedStaticWeight
  simp [not_lt.mpr hy]

theorem hughesYoungLowerBoundaryHeightIntegratedWeight_eq_zero_of_nonpos_left
    (T c u : ℝ) (h k : ℕ) {x y : ℝ} (hx : x ≤ 0) :
    hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k x y = 0 := by
  unfold hughesYoungLowerBoundaryHeightIntegratedWeight
    hughesYoungPureReducedStaticWeight
  simp [not_lt.mpr hx]

/-- Pointwise height evaluation in the exact swapped convention of a
negative signed DFI shift. -/
theorem integral_heightWeight_mul_dfiEquation27C_swappedLowerBoundaryCorrection_eq
    (T c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
      dfiEquation27C b a qy qx
        (dfiSwapWeight
          (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k))
        x y) =
      dfiEquation27C b a qy qx
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k))
        x y := by
  simp_rw [dfiEquation27C_swap]
  exact integral_heightWeight_mul_dfiEquation27C_lowerBoundaryCorrection_eq
    T c u hh hk a b qx qy hy hx

/-- Equation-(65) gives a uniform bound for the complete height-integrated
lower-endpoint weight on a positive signed central line. -/
theorem norm_hughesYoungLowerBoundaryHeightIntegratedWeight_posShift_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u x y r : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hu : |u| ≤ T / 8) (hx : 0 < x) (hy : 0 < y)
    (hr : 1 ≤ r) (hshift : x - y = r) (h k : ℕ) :
    ‖hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k x y‖ ≤
      ‖hughesYoungPureReducedStaticWeight T c u h k x y‖ *
        ((2 : ℝ) ^ j *
          ((15 * T / 4) *
            (c⁻¹ * Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
              (25 + 8 * u ^ 2) ^ 4 *
              hughesYoungHeightInputDerivativeConstant Cw j *
              (((T / 16)⁻¹ * (1 + |u|)) ^ j)))) := by
  have hmajorNonneg : 0 ≤
      (15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)) := by
    exact (mul_nonneg (pow_nonneg (abs_nonneg (0 : ℝ)) j)
      (norm_nonneg (hughesYoungHeightTransform T c u 0))).trans
        (h65 j T c u 0 hT hc hc1 hu)
  by_cases hstep :
    hughesYoungDyadicStep (y * hughesYoungDyadicRatio) = 0
  · unfold hughesYoungLowerBoundaryHeightIntegratedWeight
    rw [hughesYoungLowerBoundaryMultiplier_posShift hy hr hshift, hstep]
    calc
      ‖((0 : ℝ) : ℂ) *
          hughesYoungPureReducedStaticWeight T c u h k x y *
          hughesYoungHeightTransform T c u (Real.log (y / x))‖ = 0 := by simp
      _ ≤ _ := mul_nonneg
        (norm_nonneg (hughesYoungPureReducedStaticWeight T c u h k x y))
        (mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) j)
          hmajorNonneg)
  · have htransform :=
      norm_hughesYoungHeightTransform_lowerEndpoint_posShift_le
        h65 j hT hc hc1 hu hx hy hr hshift hstep
    unfold hughesYoungLowerBoundaryHeightIntegratedWeight
    rw [hughesYoungLowerBoundaryMultiplier_posShift hy hr hshift]
    simp only [norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hughesYoungDyadicStep_nonneg _)]
    calc
      hughesYoungDyadicStep (y * hughesYoungDyadicRatio) *
          ‖hughesYoungPureReducedStaticWeight T c u h k x y‖ *
          ‖hughesYoungHeightTransform T c u (Real.log (y / x))‖ ≤
        1 * ‖hughesYoungPureReducedStaticWeight T c u h k x y‖ *
          ((2 : ℝ) ^ j *
            ((15 * T / 4) *
              (c⁻¹ * Real.exp
                (100 * c ^ 2 - 84 * u ^ 2 +
                  4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
                (25 + 8 * u ^ 2) ^ 4 *
                hughesYoungHeightInputDerivativeConstant Cw j *
                (((T / 16)⁻¹ * (1 + |u|)) ^ j)))) := by
          gcongr
          exact hughesYoungDyadicStep_le_one _
      _ = _ := by ring

/-- Equation-(65) domination after the two literal DFI logarithmic factors
have been restored.  The majorant is the absolutely integrable pure static
DFI slice, so this inequality can be integrated without discarding any
arithmetic cancellation in the later modulus sum. -/
theorem norm_dfiEquation27C_lowerBoundaryHeightIntegrated_posShift_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u x y r : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hu : |u| ≤ T / 8) (hx : 0 < x) (hy : 0 < y)
    (hr : 1 ≤ r) (hshift : x - y = r) (h k a b qx qy : ℕ) :
    ‖dfiEquation27C a b qx qy
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) x y‖ ≤
      ‖dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k) x y‖ *
        ((2 : ℝ) ^ j *
          ((15 * T / 4) *
            (c⁻¹ * Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
              (25 + 8 * u ^ 2) ^ 4 *
              hughesYoungHeightInputDerivativeConstant Cw j *
              (((T / 16)⁻¹ * (1 + |u|)) ^ j)))) := by
  have hweight := norm_hughesYoungLowerBoundaryHeightIntegratedWeight_posShift_le
    h65 j hT hc hc1 hu hx hy hr hshift h k
  unfold dfiEquation27C
  simp only [norm_mul]
  calc
    ‖dfiEquation27LogFactor a qx x‖ *
          ‖dfiEquation27LogFactor b qy y‖ *
          ‖hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k x y‖ ≤
        ‖dfiEquation27LogFactor a qx x‖ *
          ‖dfiEquation27LogFactor b qy y‖ *
          (‖hughesYoungPureReducedStaticWeight T c u h k x y‖ *
            ((2 : ℝ) ^ j *
              ((15 * T / 4) *
                (c⁻¹ * Real.exp
                  (100 * c ^ 2 - 84 * u ^ 2 +
                    4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
                  (25 + 8 * u ^ 2) ^ 4 *
                  hughesYoungHeightInputDerivativeConstant Cw j *
                  (((T / 16)⁻¹ * (1 + |u|)) ^ j))))) := by
          gcongr
    _ = (‖dfiEquation27LogFactor a qx x‖ *
          ‖dfiEquation27LogFactor b qy y‖ *
          ‖hughesYoungPureReducedStaticWeight T c u h k x y‖) *
            ((2 : ℝ) ^ j *
              ((15 * T / 4) *
                (c⁻¹ * Real.exp
                  (100 * c ^ 2 - 84 * u ^ 2 +
                    4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
                  (25 + 8 * u ^ 2) ^ 4 *
                  hughesYoungHeightInputDerivativeConstant Cw j *
                  (((T / 16)⁻¹ * (1 + |u|)) ^ j)))) := by ring

/-- Measurability is not inferred from the equation-(65) norm bound: the
literal lower-endpoint central slice is continuous on its physical
positive half-line. -/
theorem continuousOn_dfiEquation27C_lowerBoundaryHeightIntegrated_posShift
    {T c : ℝ} (hT : 0 < T) (hc : 0 < c) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b qx qy : ℕ)
    {r : ℝ} (hr : 0 < r) :
    ContinuousOn
      (fun y : ℝ => dfiEquation27C a b qx qy
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)
        (y + r) y)
      (Set.Ioi 0) := by
  intro y hy
  have hy0 : 0 < y := hy
  let s : ℂ := -((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))
  let g : ℝ → ℂ := fun z =>
    dfiEquation27LogFactor a qx (z + r) *
      dfiEquation27LogFactor b qy z *
      (((hughesYoungLowerBoundaryMultiplier (z + r) z : ℝ) : ℂ) *
        (hughesYoungPureReducedStaticScaleConstant T c u h k *
          ((z + r : ℝ) : ℂ) ^ s * (z : ℂ) ^ s) *
        hughesYoungHeightTransform T c u (Real.log (z / (z + r))))
  have htransform : Continuous
      (hughesYoungHeightTransform T c u) :=
    (contDiff_hughesYoungHeightTransform hT hc u).continuous
  have hg : ContinuousAt g y := by
    have hyr : 0 < y + r := add_pos hy0 hr
    have hzrAt : ContinuousAt (fun z : ℝ => z + r) y := by fun_prop
    have hlogR : ContinuousAt (fun z : ℝ => Real.log (z + r)) y :=
      hzrAt.log hyr.ne'
    have hlogY : ContinuousAt (fun z : ℝ => Real.log z) y :=
      continuousAt_id.log hy0.ne'
    have hfactorA : ContinuousAt
        (fun z : ℝ => dfiEquation27LogFactor a qx (z + r)) y := by
      unfold dfiEquation27LogFactor
      exact ((((Complex.ofRealCLM.continuous.continuousAt.comp hlogR).sub
        continuousAt_const).add continuousAt_const).sub continuousAt_const)
    have hfactorB : ContinuousAt
        (fun z : ℝ => dfiEquation27LogFactor b qy z) y := by
      unfold dfiEquation27LogFactor
      exact ((((Complex.ofRealCLM.continuous.continuousAt.comp hlogY).sub
        continuousAt_const).add continuousAt_const).sub continuousAt_const)
    have hstepR : ContinuousAt (fun z : ℝ =>
        hughesYoungDyadicStep ((z + r) * hughesYoungDyadicRatio)) y :=
      contDiff_hughesYoungDyadicStep.continuous.continuousAt.comp (by fun_prop)
    have hstepY : ContinuousAt (fun z : ℝ =>
        hughesYoungDyadicStep (z * hughesYoungDyadicRatio)) y :=
      contDiff_hughesYoungDyadicStep.continuous.continuousAt.comp (by fun_prop)
    have hmult : ContinuousAt (fun z : ℝ =>
        hughesYoungLowerBoundaryMultiplier (z + r) z) y := by
      unfold hughesYoungLowerBoundaryMultiplier
      exact (hstepR.add hstepY).sub (hstepR.mul hstepY)
    have hmultC : ContinuousAt (fun z : ℝ =>
        ((hughesYoungLowerBoundaryMultiplier (z + r) z : ℝ) : ℂ)) y :=
      Complex.ofRealCLM.continuous.continuousAt.comp hmult
    have hpowR : ContinuousAt (fun z : ℝ =>
        ((z + r : ℝ) : ℂ) ^ s) y := by
      have hbase := Complex.continuousAt_ofReal_cpow_const
        (y + r) s (Or.inr hyr.ne')
      have hcomp := ContinuousAt.comp
        (f := fun z : ℝ => z + r)
        (g := fun w : ℝ => (w : ℂ) ^ s) hbase hzrAt
      simpa only [Function.comp_apply] using hcomp
    have hpowY : ContinuousAt (fun z : ℝ => (z : ℂ) ^ s) y :=
      Complex.continuousAt_ofReal_cpow_const y s (Or.inr hy0.ne')
    have hratio : ContinuousAt (fun z : ℝ => z / (z + r)) y :=
      continuousAt_id.div hzrAt hyr.ne'
    have hratio0 : y / (y + r) ≠ 0 := div_ne_zero hy0.ne' hyr.ne'
    have hlogRatio : ContinuousAt
        (fun z : ℝ => Real.log (z / (z + r))) y :=
      hratio.log hratio0
    have hheight : ContinuousAt (fun z : ℝ =>
        hughesYoungHeightTransform T c u (Real.log (z / (z + r)))) y :=
      htransform.continuousAt.comp hlogRatio
    dsimp only [g]
    exact (hfactorA.mul hfactorB).mul
      (((hmultC.mul ((continuousAt_const.mul hpowR).mul hpowY)).mul hheight))
  refine hg.continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ hy
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : 0 < z := hz
  have hzr : 0 < z + r := add_pos hz0 hr
  unfold dfiEquation27C hughesYoungLowerBoundaryHeightIntegratedWeight
  rw [hughesYoungPureReducedStaticWeight_eq_scaled_powers
    T c u hh hk hzr hz0]

/-- The literal height-integrated lower-endpoint DFI slice is absolutely
integrable.  This closes the measurability/integrability obligation needed
before applying Bochner integral linearity to the endpoint correction. -/
theorem integrableOn_dfiEquation27C_lowerBoundaryHeightIntegrated_posShift
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u r : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hcHalf : c < 1 / 2)
    (hc1 : c ≤ 1) (hu : |u| ≤ T / 8) (hr : 1 ≤ r)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b qx qy : ℕ) :
    IntegrableOn
      (fun y : ℝ => dfiEquation27C a b qx qy
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)
        (y + r) y)
      (Set.Ioi 0) := by
  let M : ℝ :=
    (2 : ℝ) ^ j *
      ((15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
  have hpure :=
    integrableOn_dfiEquation27C_pureReducedStaticWeight_posShift
      hc hcHalf T u hh hk a b qx qy (lt_of_lt_of_le zero_lt_one hr)
  have hmajor : IntegrableOn (fun y : ℝ =>
      ‖dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖ * M)
      (Set.Ioi 0) := by
    simpa only [mul_comm] using hpure.norm.const_mul M
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => dfiEquation27C a b qx qy
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)
        (y + r) y)
      (volume.restrict (Set.Ioi 0)) :=
    (continuousOn_dfiEquation27C_lowerBoundaryHeightIntegrated_posShift
      (lt_of_lt_of_le (by norm_num) hT) hc u hh hk a b qx qy
      (lt_of_lt_of_le zero_lt_one hr)).aestronglyMeasurable measurableSet_Ioi
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : 0 < y := hy
  have hyr : 0 < y + r := add_pos hy0 (lt_of_lt_of_le zero_lt_one hr)
  simpa only [M] using
    norm_dfiEquation27C_lowerBoundaryHeightIntegrated_posShift_le
      h65 j hT hc hc1 hu hyr hy0 hr (by ring) h k a b qx qy

/-- Symmetric equation-(65) bound on a negative signed central line. -/
theorem norm_hughesYoungLowerBoundaryHeightIntegratedWeight_negShift_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u x y r : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hu : |u| ≤ T / 8) (hx : 0 < x) (hy : 0 < y)
    (hr : r ≤ -1) (hshift : x - y = r) (h k : ℕ) :
    ‖hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k x y‖ ≤
      ‖hughesYoungPureReducedStaticWeight T c u h k x y‖ *
        ((2 : ℝ) ^ j *
          ((15 * T / 4) *
            (c⁻¹ * Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
              (25 + 8 * u ^ 2) ^ 4 *
              hughesYoungHeightInputDerivativeConstant Cw j *
              (((T / 16)⁻¹ * (1 + |u|)) ^ j)))) := by
  have hmajorNonneg : 0 ≤
      (15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)) := by
    exact (mul_nonneg (pow_nonneg (abs_nonneg (0 : ℝ)) j)
      (norm_nonneg (hughesYoungHeightTransform T c u 0))).trans
        (h65 j T c u 0 hT hc hc1 hu)
  by_cases hstep :
      hughesYoungDyadicStep (x * hughesYoungDyadicRatio) = 0
  · unfold hughesYoungLowerBoundaryHeightIntegratedWeight
    rw [hughesYoungLowerBoundaryMultiplier_negShift hx hr hshift, hstep]
    calc
      ‖((0 : ℝ) : ℂ) *
          hughesYoungPureReducedStaticWeight T c u h k x y *
          hughesYoungHeightTransform T c u (Real.log (y / x))‖ = 0 := by simp
      _ ≤ _ := mul_nonneg
        (norm_nonneg (hughesYoungPureReducedStaticWeight T c u h k x y))
        (mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) j)
          hmajorNonneg)
  · have htransform :=
      norm_hughesYoungHeightTransform_lowerEndpoint_negShift_le
        h65 j hT hc hc1 hu hx hy hr hshift hstep
    unfold hughesYoungLowerBoundaryHeightIntegratedWeight
    rw [hughesYoungLowerBoundaryMultiplier_negShift hx hr hshift]
    simp only [norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hughesYoungDyadicStep_nonneg _)]
    calc
      hughesYoungDyadicStep (x * hughesYoungDyadicRatio) *
          ‖hughesYoungPureReducedStaticWeight T c u h k x y‖ *
          ‖hughesYoungHeightTransform T c u (Real.log (y / x))‖ ≤
        1 * ‖hughesYoungPureReducedStaticWeight T c u h k x y‖ *
          ((2 : ℝ) ^ j *
            ((15 * T / 4) *
              (c⁻¹ * Real.exp
                (100 * c ^ 2 - 84 * u ^ 2 +
                  4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
                (25 + 8 * u ^ 2) ^ 4 *
                hughesYoungHeightInputDerivativeConstant Cw j *
                (((T / 16)⁻¹ * (1 + |u|)) ^ j)))) := by
          gcongr
          exact hughesYoungDyadicStep_le_one _
      _ = _ := by ring

/-- Equation-(65) domination for the coordinate-swapped kernel which is
the negative branch of `dfiSignedCentralSeries`. -/
theorem norm_dfiEquation27C_swappedLowerBoundaryHeightIntegrated_posShift_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u x y r : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hu : |u| ≤ T / 8) (hx : 0 < x) (hy : 0 < y)
    (hr : 1 ≤ r) (hshift : x - y = r)
    (h k a b qx qy : ℕ) :
    ‖dfiEquation27C b a qy qx
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) x y‖ ≤
      ‖dfiEquation27C b a qy qx
        (dfiSwapWeight
          (hughesYoungPureReducedStaticWeight T c u h k)) x y‖ *
        ((2 : ℝ) ^ j *
          ((15 * T / 4) *
            (c⁻¹ * Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
              (25 + 8 * u ^ 2) ^ 4 *
              hughesYoungHeightInputDerivativeConstant Cw j *
              (((T / 16)⁻¹ * (1 + |u|)) ^ j)))) := by
  rw [dfiEquation27C_swap, dfiEquation27C_swap]
  have hweight :=
    norm_hughesYoungLowerBoundaryHeightIntegratedWeight_negShift_le
      h65 j hT hc hc1 hu hy hx (show -r ≤ (-1 : ℝ) by linarith)
        (show y - x = -r by linarith) h k
  let M : ℝ :=
    (2 : ℝ) ^ j *
      ((15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
  change ‖hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k y x‖ ≤
    ‖hughesYoungPureReducedStaticWeight T c u h k y x‖ * M at hweight
  change ‖dfiEquation27C a b qx qy
      (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) y x‖ ≤
    ‖dfiEquation27C a b qx qy
      (hughesYoungPureReducedStaticWeight T c u h k) y x‖ * M
  unfold dfiEquation27C
  simp only [norm_mul]
  calc
    ‖dfiEquation27LogFactor a qx y‖ *
        ‖dfiEquation27LogFactor b qy x‖ *
        ‖hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k y x‖ ≤
      ‖dfiEquation27LogFactor a qx y‖ *
        ‖dfiEquation27LogFactor b qy x‖ *
        (‖hughesYoungPureReducedStaticWeight T c u h k y x‖ * M) := by
        exact mul_le_mul_of_nonneg_left hweight
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖dfiEquation27LogFactor a qx y‖ *
          ‖dfiEquation27LogFactor b qy x‖ *
          ‖hughesYoungPureReducedStaticWeight T c u h k y x‖) * M := by ring

/-- The swapped lower-endpoint central integral is supported on the same
translated positive half-line as its pure majorant. -/
theorem dfiEquation27CentralIntegral_swappedLowerBoundaryHeightIntegrated_eq_Ioi
    (T c u : ℝ) (h k a b qx qy : ℕ) (r : ℝ) :
    dfiEquation27CentralIntegral b a qy qx
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) r =
      ∫ y in Set.Ioi (0 : ℝ),
        dfiEquation27C b a qy qx
          (dfiSwapWeight
            (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k))
          (y + r) y := by
  apply dfiEquation27CentralIntegral_eq_Ioi_shift
  intro y hy
  unfold dfiSwapWeight
  exact hughesYoungLowerBoundaryHeightIntegratedWeight_eq_zero_of_nonpos_left
    T c u h k hy

/-- Exact noncompact endpoint Fubini theorem for the negative signed
branch, retaining the DFI coordinate swap throughout. -/
theorem dfiEquation27CentralIntegral_swappedLowerBoundaryHeightIntegrated_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hcHalf : c < 1 / 2) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (a b qx qy : ℕ) :
    dfiEquation27CentralIntegral b a qy qx
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) r =
      ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralIntegral b a qy qx
          (dfiSwapWeight
            (hughesYoungLowerBoundaryReducedMellinCorrection
              T t c u h k)) r := by
  let J : ℝ → ℝ → ℂ :=
    hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
      T c u h k r a b qx qy
  have hJFull : Integrable (Function.uncurry J) := by
    simpa only [J] using
      integrable_uncurry_hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
        hT hc hcHalf u hh hk hr a b qx qy
  have hJOn : IntegrableOn (Function.uncurry J)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := hJFull.integrableOn
  have hJ : Integrable (Function.uncurry J)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    simpa only [Measure.volume_eq_prod] using hJOn
  rw [dfiEquation27CentralIntegral_swappedLowerBoundaryHeightIntegrated_eq_Ioi]
  calc
    (∫ y in Set.Ioi (0 : ℝ),
        dfiEquation27C b a qy qx
          (dfiSwapWeight
            (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k))
          (y + r) y) =
        ∫ y in Set.Ioi (0 : ℝ), ∫ t : ℝ, J y t := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact
        (integral_heightWeight_mul_dfiEquation27C_swappedLowerBoundaryCorrection_eq
          T c u hh hk a b qx qy (add_pos hy hr) hy).symm
    _ = ∫ t : ℝ, ∫ y in Set.Ioi (0 : ℝ), J y t := by
      exact MeasureTheory.integral_integral_swap hJ
    _ = ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralIntegral b a qy qx
          (dfiSwapWeight
            (hughesYoungLowerBoundaryReducedMellinCorrection
              T t c u h k)) r := by
      apply integral_congr_ae
      filter_upwards with t
      rw [dfiEquation27CentralIntegral_eq_Ioi_shift]
      · unfold J hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
        rw [MeasureTheory.integral_const_mul]
      · intro y hy
        unfold dfiSwapWeight
        exact hughesYoungLowerBoundaryReducedMellinCorrection_eq_zero_of_nonpos_left
          T t c u h k hy

noncomputable def hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
    (T t c u : ℝ) (h k a b r q : ℕ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    dfiEquation27CentralSummand b a r
      (dfiSwapWeight
        (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k)) q

theorem hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_eq_setIntegral
    (T t c u : ℝ) (h k a b r q : ℕ) :
    hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q =
      (((b : ℂ) * a)⁻¹ * dfiEquation27ArithmeticCoefficient b a r q) *
        ∫ y in Set.Ioi (0 : ℝ),
          hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
            T c u h k (r : ℝ) a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q) y t := by
  unfold hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
    dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_eq_Ioi_shift]
  · unfold hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
    rw [MeasureTheory.integral_const_mul]
    ring
  · intro y hy
    unfold dfiSwapWeight
    exact hughesYoungLowerBoundaryReducedMellinCorrection_eq_zero_of_nonpos_left
      T t c u h k hy

theorem integrable_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hcHalf : c < 1 / 2) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b q : ℕ) :
    Integrable (fun t : ℝ =>
      hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q) := by
  let J : ℝ → ℝ → ℂ :=
    hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
      T c u h k (r : ℝ) a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
  have hJFull : Integrable (Function.uncurry J) := by
    simpa only [J] using
      integrable_uncurry_hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
        hT hc hcHalf u hh hk (by exact_mod_cast hr) a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
  have hJOn : IntegrableOn (Function.uncurry J)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := hJFull.integrableOn
  have hJ : Integrable (Function.uncurry J)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    simpa only [Measure.volume_eq_prod] using hJOn
  have hphysical : Integrable
      (fun t : ℝ => ∫ y in Set.Ioi (0 : ℝ), J y t) :=
    hJ.integral_prod_right
  let A : ℂ := (((b : ℂ) * a)⁻¹ *
    dfiEquation27ArithmeticCoefficient b a r q)
  have heq : (fun t : ℝ =>
      hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q) =
      fun t => A * ∫ y in Set.Ioi (0 : ℝ), J y t := by
    funext t
    simpa only [A, J] using
      hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_eq_setIntegral
        T t c u h k a b r q
  rw [heq]
  exact hphysical.const_mul A

theorem dfiEquation27CentralSummand_swappedLowerBoundaryHeightIntegrated_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hcHalf : c < 1 / 2) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b q : ℕ) :
    dfiEquation27CentralSummand b a r
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) q =
      ∫ t : ℝ, hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q := by
  let A : ℂ := (((b : ℂ) * a)⁻¹ *
    dfiEquation27ArithmeticCoefficient b a r q)
  unfold dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_swappedLowerBoundaryHeightIntegrated_eq_heightIntegral
    hT hc hcHalf u hh hk (by exact_mod_cast hr) a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)]
  calc
    A * (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralIntegral b a
          (dfiReducedDenominator b q) (dfiReducedDenominator a q)
          (dfiSwapWeight
            (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k)) r) =
      ∫ t : ℝ, A * ((hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralIntegral b a
          (dfiReducedDenominator b q) (dfiReducedDenominator a q)
          (dfiSwapWeight
            (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k)) r) := by
        rw [MeasureTheory.integral_const_mul]
    _ = ∫ t : ℝ, hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q := by
      apply integral_congr_ae
      filter_upwards with t
      unfold A hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        dfiEquation27CentralSummand
      ring

theorem integral_norm_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_le
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hcHalf : c < 1 / 2) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b q : ℕ) :
    (∫ t : ℝ, ‖hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q‖) ≤
      ‖((b : ℂ) * a)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
        ((∫ y in Set.Ioi (0 : ℝ),
            ‖dfiEquation27C b a
              (dfiReducedDenominator b q) (dfiReducedDenominator a q)
              (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
              (y + r) y‖) *
          ∫ t : ℝ, ‖hughesYoungHeightFourierInput T c u t‖) := by
  let J : ℝ → ℝ → ℂ :=
    hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
      T c u h k (r : ℝ) a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
  let f : ℝ → ℂ := fun y => dfiEquation27C b a
    (dfiReducedDenominator b q) (dfiReducedDenominator a q)
    (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
    (y + r) y
  let H : ℝ → ℂ := hughesYoungHeightFourierInput T c u
  let A : ℂ := (((b : ℂ) * a)⁻¹ *
    dfiEquation27ArithmeticCoefficient b a r q)
  have hJFull : Integrable (Function.uncurry J) := by
    simpa only [J] using
      integrable_uncurry_hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
        hT hc hcHalf u hh hk (by exact_mod_cast hr) a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
  have hJOn : IntegrableOn (Function.uncurry J)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := hJFull.integrableOn
  have hJ : Integrable (Function.uncurry J)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    simpa only [Measure.volume_eq_prod] using hJOn
  have hf : Integrable f := by
    simpa only [f] using
      integrable_dfiEquation27C_swappedPureReducedStaticWeight_posShift
        hc hcHalf T u hh hk a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (by exact_mod_cast hr)
  have hH : Integrable (fun t : ℝ => ‖H t‖) := by
    simpa [H] using integrable_heightFourierInput_moment hT hc u 0
  have hmajorFull : Integrable
      (fun z : ℝ × ℝ => ‖f z.1‖ * ‖H z.2‖) := hf.norm.mul_prod hH
  have hmajorOn : IntegrableOn
      (fun z : ℝ × ℝ => ‖f z.1‖ * ‖H z.2‖)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := hmajorFull.integrableOn
  have hmajor : Integrable
      (fun z : ℝ × ℝ => ‖f z.1‖ * ‖H z.2‖)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    simpa only [Measure.volume_eq_prod] using hmajorOn
  have hprod :
      (∫ z : ℝ × ℝ, ‖Function.uncurry J z‖
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) ≤
        ∫ z : ℝ × ℝ, ‖f z.1‖ * ‖H z.2‖
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    apply integral_mono hJ.norm hmajor
    intro z
    simpa only [J, f, H, Function.uncurry_apply_pair] using
      norm_hughesYoungSwappedLowerBoundaryCentralHeightIntegrand_le
        T c u hh hk (by exact_mod_cast hr) a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q) z.1 z.2
  have htermInt :=
    integrable_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
      hT hc hcHalf u hh hk hr a b q
  have hiterInt : Integrable (fun t : ℝ =>
      ‖A‖ * ∫ y in Set.Ioi (0 : ℝ), ‖J y t‖) :=
    hJ.norm.integral_prod_right.const_mul ‖A‖
  calc
    (∫ t : ℝ, ‖hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q‖) ≤
      ∫ t : ℝ, ‖A‖ * ∫ y in Set.Ioi (0 : ℝ), ‖J y t‖ := by
        apply integral_mono htermInt.norm hiterInt
        intro t
        change ‖hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
            T t c u h k a b r q‖ ≤
          ‖A‖ * ∫ y in Set.Ioi (0 : ℝ), ‖J y t‖
        rw [hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_eq_setIntegral]
        simp only [A, J, norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖A‖ * (∫ z : ℝ × ℝ, ‖Function.uncurry J z‖
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        exact (MeasureTheory.integral_prod_symm _ hJ.norm).symm
    _ ≤ ‖A‖ * (∫ z : ℝ × ℝ, ‖f z.1‖ * ‖H z.2‖
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) := by
        exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖A‖ * ((∫ y in Set.Ioi (0 : ℝ), ‖f y‖) *
          ∫ t : ℝ, ‖H t‖) := by
        apply congrArg (‖A‖ * ·)
        exact MeasureTheory.integral_prod_mul
          (fun y : ℝ => ‖f y‖) (fun t : ℝ => ‖H t‖)
    _ = _ := by
      dsimp only [A, f, H]
      rw [norm_mul]

set_option maxHeartbeats 2000000 in
theorem summable_integral_norm_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hc4 : c ≤ 1 / 4) (u : ℝ)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Summable (fun q : ℕ => ∫ t : ℝ,
      ‖hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q‖) := by
  let A : ℝ := hughesYoungEquation84LogBudget b a r
  let Hmass : ℝ := ∫ t : ℝ, ‖hughesYoungHeightFourierInput T c u t‖
  let K : ℝ := ‖((b : ℂ) * a)⁻¹‖ *
    ((b * a * r ^ 2 : ℕ) : ℝ) * Hmass *
    (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
      (r : ℝ) ^ (-2 * c) * (2312 + 9 * c⁻¹ ^ 3))
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget b a r)
  have hHmass : 0 ≤ Hmass := by
    dsimp only [Hmass]
    exact integral_nonneg (fun t => norm_nonneg _)
  have hmajor : Summable (fun q : ℕ =>
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left K
  apply hmajor.of_nonneg_of_le
  · intro q
    exact integral_nonneg (fun t => norm_nonneg _)
  · intro q
    by_cases hq0 : q = 0
    · subst q
      simp [hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm,
        dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
    · have hq : 0 < q := Nat.pos_of_ne_zero hq0
      letI : NeZero q := ⟨hq0⟩
      let S : ℝ :=
        1 +
          ‖(Real.log r : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q)‖ +
          ‖(Real.log r : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q)‖
      have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
        have hCA :=
          norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
        have hCB :=
          norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
        dsimp only [S, A]
        unfold hughesYoungEquation84LogBudget
        linarith
      have hS0 : 0 ≤ S := by dsimp only [S]; positivity
      have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
        zero_le_one.trans
          (one_le_hughesYoungEquation84LogBudget_add_four_log b a r q hq)
      have hcInv3 : 0 ≤ c⁻¹ ^ 3 := by positivity
      have hCoeff :=
        norm_dfiEquation27ArithmeticCoefficient_le_inv_sq b a r q hb ha hr
      have hPhysical :=
        integral_norm_dfiEquation27C_swappedPureReducedStaticWeight_posShift_le
          hc hc4 T u hh hk a b (dfiReducedDenominator a q)
            (dfiReducedDenominator b q)
            (show (1 : ℝ) ≤ r by exact_mod_cast hr)
      have hTerm :=
        integral_norm_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_le
          hT hc (hc4.trans_lt (by norm_num)) u hh hk hr a b q
      change (∫ t : ℝ,
          ‖hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
            T t c u h k a b r q‖) ≤ _ at hTerm
      change (∫ y in Set.Ioi (0 : ℝ),
          ‖dfiEquation27C b a
            (dfiReducedDenominator b q) (dfiReducedDenominator a q)
            (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
            (y + r) y‖) ≤
        ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          (r : ℝ) ^ (-2 * c) *
          (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3) at hPhysical
      calc
        (∫ t : ℝ, ‖hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
            T t c u h k a b r q‖) ≤
          ‖((b : ℂ) * a)⁻¹‖ *
            ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
            ((∫ y in Set.Ioi (0 : ℝ),
                ‖dfiEquation27C b a
                  (dfiReducedDenominator b q) (dfiReducedDenominator a q)
                  (dfiSwapWeight
                    (hughesYoungPureReducedStaticWeight T c u h k))
                  (y + r) y‖) * Hmass) := by
              simpa only [Hmass] using hTerm
        _ ≤ ‖((b : ℂ) * a)⁻¹‖ *
            (((b * a * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
            ((‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
                (r : ℝ) ^ (-2 * c) *
                (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3)) * Hmass) := by
              gcongr
        _ ≤ ‖((b : ℂ) * a)⁻¹‖ *
            (((b * a * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
            ((‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
                (r : ℝ) ^ (-2 * c) *
                ((2312 + 9 * c⁻¹ ^ 3) *
                  (A + 4 * Real.log (q : ℝ)) ^ 2)) * Hmass) := by
              gcongr
              calc
                2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3 =
                    (2312 + 9 * c⁻¹ ^ 3) * S ^ 2 := by ring
                _ ≤ (2312 + 9 * c⁻¹ ^ 3) *
                    (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
        _ = K * (((q : ℝ) ^ 2)⁻¹ *
            (A + 4 * Real.log (q : ℝ)) ^ 2) := by
              dsimp only [K]
              ring

theorem dfiEquation27CentralSeries_swappedLowerBoundaryHeightIntegrated_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hc4 : c ≤ 1 / 4) (u : ℝ)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    dfiEquation27CentralSeries b a r
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) =
      ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralSeries b a r
          (dfiSwapWeight
            (hughesYoungLowerBoundaryReducedMellinCorrection
              T t c u h k)) := by
  let F : ℕ → ℝ → ℂ := fun q t =>
    hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
      T t c u h k a b r q
  have hInt : ∀ q : ℕ, Integrable (F q) := by
    intro q
    simpa only [F] using
      integrable_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        hT hc (hc4.trans_lt (by norm_num)) u hh hk hr a b q
  have hNormSum : Summable (fun q : ℕ => ∫ t : ℝ, ‖F q t‖) := by
    simpa only [F] using
      summable_integral_norm_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        hT hc hc4 u hh hk ha hb hr
  have hswap : (∑' q : ℕ, ∫ t : ℝ, F q t) =
      ∫ t : ℝ, ∑' q : ℕ, F q t :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hInt hNormSum
  unfold dfiEquation27CentralSeries
  simp_rw [dfiEquation27CentralSummand_swappedLowerBoundaryHeightIntegrated_eq_heightIntegral
    hT hc (hc4.trans_lt (by norm_num)) u hh hk hr]
  calc
    (∑' q : ℕ, ∫ t : ℝ,
        hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
          T t c u h k a b r q) =
      ∫ t : ℝ, ∑' q : ℕ, F q t := by
        simpa only [F] using hswap
    _ = ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        ∑' q : ℕ, dfiEquation27CentralSummand b a r
          (dfiSwapWeight
            (hughesYoungLowerBoundaryReducedMellinCorrection
              T t c u h k)) q := by
      apply integral_congr_ae
      filter_upwards with t
      unfold F hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
      rw [tsum_mul_left]

set_option maxHeartbeats 2000000 in
/-- Integrated equation-(65) bound for one negative signed DFI central
integral, written in the exact swapped convention of the signed series. -/
theorem norm_dfiEquation27CentralIntegral_swappedLowerBoundaryHeightIntegrated_posShift_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u r : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hc1 : c ≤ 1) (hu : |u| ≤ T / 8) (hr : 1 ≤ r)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b qx qy : ℕ) :
    ‖dfiEquation27CentralIntegral b a qy qx
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) r‖ ≤
      ((2 : ℝ) ^ j *
        ((15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))) *
        (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          r ^ (-2 * c) *
          (2312 *
              (1 +
                ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖ +
                ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖) ^ 2 +
            9 *
              (1 +
                ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖ +
                ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖) ^ 2 *
              c⁻¹ ^ 3)) := by
  let M : ℝ :=
    (2 : ℝ) ^ j *
      ((15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
  let B : ℝ :=
    ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
      r ^ (-2 * c) *
      (2312 *
          (1 +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖ +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖) ^ 2 +
        9 *
          (1 +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖ +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖) ^ 2 *
          c⁻¹ ^ 3)
  have hBase : 0 ≤
      (15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)) := by
    exact (mul_nonneg (pow_nonneg (abs_nonneg (0 : ℝ)) j)
      (norm_nonneg (hughesYoungHeightTransform T c u 0))).trans
        (h65 j T c u 0 hT hc hc1 hu)
  have hM0 : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j) hBase
  have hpure :=
    integrableOn_dfiEquation27C_swappedPureReducedStaticWeight_posShift
      hc (hc4.trans_lt (by norm_num)) T u hh hk a b qx qy
        (zero_lt_one.trans_le hr)
  have hmajor : IntegrableOn (fun y : ℝ => M *
      ‖dfiEquation27C b a qy qx
        (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
        (y + r) y‖) (Set.Ioi 0) := hpure.norm.const_mul M
  rw [dfiEquation27CentralIntegral_swappedLowerBoundaryHeightIntegrated_eq_Ioi]
  have hnorm :
      ‖∫ y in Set.Ioi (0 : ℝ),
        dfiEquation27C b a qy qx
          (dfiSwapWeight
            (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k))
          (y + r) y‖ ≤
        ∫ y in Set.Ioi (0 : ℝ), M *
          ‖dfiEquation27C b a qy qx
            (dfiSwapWeight
              (hughesYoungPureReducedStaticWeight T c u h k))
            (y + r) y‖ := by
    apply norm_integral_le_of_norm_le hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    have hyr : 0 < y + r := add_pos hy0 (zero_lt_one.trans_le hr)
    have hpoint :=
      norm_dfiEquation27C_swappedLowerBoundaryHeightIntegrated_posShift_le
        h65 j hT hc hc1 hu hyr hy0 hr (by ring) h k a b qx qy
    change ‖dfiEquation27C b a qy qx
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k))
        (y + r) y‖ ≤
      ‖dfiEquation27C b a qy qx
        (dfiSwapWeight
          (hughesYoungPureReducedStaticWeight T c u h k))
        (y + r) y‖ * M at hpoint
    exact hpoint.trans_eq (mul_comm _ _)
  calc
    _ ≤ ∫ y in Set.Ioi (0 : ℝ), M *
        ‖dfiEquation27C b a qy qx
          (dfiSwapWeight
            (hughesYoungPureReducedStaticWeight T c u h k))
          (y + r) y‖ := hnorm
    _ = M * (∫ y in Set.Ioi (0 : ℝ),
        ‖dfiEquation27C b a qy qx
          (dfiSwapWeight
            (hughesYoungPureReducedStaticWeight T c u h k))
          (y + r) y‖) := by rw [MeasureTheory.integral_const_mul]
    _ ≤ M * B := by
      apply mul_le_mul_of_nonneg_left _ hM0
      exact
        integral_norm_dfiEquation27C_swappedPureReducedStaticWeight_posShift_le
          hc hc4 T u hh hk a b qx qy hr
    _ = _ := by rfl

/-- The positive-shift endpoint central integral is supported on the
translated positive half-line. -/
theorem dfiEquation27CentralIntegral_lowerBoundaryHeightIntegrated_eq_Ioi
    (T c u : ℝ) (h k a b qx qy : ℕ) (r : ℝ) :
    dfiEquation27CentralIntegral a b qx qy
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) r =
      ∫ y in Set.Ioi (0 : ℝ),
        dfiEquation27C a b qx qy
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)
          (y + r) y := by
  apply dfiEquation27CentralIntegral_eq_Ioi_shift
  intro y hy
  exact hughesYoungLowerBoundaryHeightIntegratedWeight_eq_zero_of_nonpos_right
    T c u h k hy

/-- Exact Fubini theorem for the noncompact lower endpoint on a positive
shift.  Both orders of integration are justified by the product
critical-beta majorant, rather than by a formal manipulation of an
improper integral. -/
theorem dfiEquation27CentralIntegral_lowerBoundaryHeightIntegrated_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hcHalf : c < 1 / 2) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (a b qx qy : ℕ) :
    dfiEquation27CentralIntegral a b qx qy
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) r =
      ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralIntegral a b qx qy
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k) r := by
  let J : ℝ → ℝ → ℂ :=
    hughesYoungLowerBoundaryCentralHeightIntegrand
      T c u h k r a b qx qy
  have hJFull : Integrable (Function.uncurry J) := by
    simpa only [J] using
      integrable_uncurry_hughesYoungLowerBoundaryCentralHeightIntegrand
        hT hc hcHalf u hh hk hr a b qx qy
  have hJOn : IntegrableOn (Function.uncurry J)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := hJFull.integrableOn
  have hJ : Integrable (Function.uncurry J)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    simpa only [Measure.volume_eq_prod] using hJOn
  rw [dfiEquation27CentralIntegral_lowerBoundaryHeightIntegrated_eq_Ioi]
  calc
    (∫ y in Set.Ioi (0 : ℝ),
        dfiEquation27C a b qx qy
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)
          (y + r) y) =
        ∫ y in Set.Ioi (0 : ℝ), ∫ t : ℝ, J y t := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact (integral_heightWeight_mul_dfiEquation27C_lowerBoundaryCorrection_eq
        T c u hh hk a b qx qy (add_pos hy hr) hy).symm
    _ = ∫ t : ℝ, ∫ y in Set.Ioi (0 : ℝ), J y t := by
      exact MeasureTheory.integral_integral_swap hJ
    _ = ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralIntegral a b qx qy
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k) r := by
      apply integral_congr_ae
      filter_upwards with t
      rw [dfiEquation27CentralIntegral_eq_Ioi_shift]
      · unfold J hughesYoungLowerBoundaryCentralHeightIntegrand
        rw [MeasureTheory.integral_const_mul]
      · intro y hy
        exact hughesYoungLowerBoundaryReducedMellinCorrection_eq_zero_of_nonpos_right
          T t c u h k hy

/-- One modulus term in the positive-shift lower-endpoint height family. -/
noncomputable def hughesYoungLowerBoundaryCentralSeriesHeightTerm
    (T t c u : ℝ) (h k a b r q : ℕ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    dfiEquation27CentralSummand a b r
      (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k) q

/-- Source-faithful representation of one endpoint modulus term as the
physical integral of the joint kernel. -/
theorem hughesYoungLowerBoundaryCentralSeriesHeightTerm_eq_setIntegral
    (T t c u : ℝ) (h k a b r q : ℕ) :
    hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q =
      (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b r q) *
        ∫ y in Set.Ioi (0 : ℝ),
          hughesYoungLowerBoundaryCentralHeightIntegrand T c u h k (r : ℝ)
            a b (dfiReducedDenominator a q) (dfiReducedDenominator b q) y t := by
  unfold hughesYoungLowerBoundaryCentralSeriesHeightTerm
    dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_eq_Ioi_shift]
  · unfold hughesYoungLowerBoundaryCentralHeightIntegrand
    rw [MeasureTheory.integral_const_mul]
    ring
  · intro y hy
    exact hughesYoungLowerBoundaryReducedMellinCorrection_eq_zero_of_nonpos_right
      T t c u h k hy

/-- Each endpoint modulus term is integrable in the height variable. -/
theorem integrable_hughesYoungLowerBoundaryCentralSeriesHeightTerm
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hcHalf : c < 1 / 2) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b q : ℕ) :
    Integrable (fun t : ℝ =>
      hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q) := by
  let J : ℝ → ℝ → ℂ :=
    hughesYoungLowerBoundaryCentralHeightIntegrand T c u h k (r : ℝ)
      a b (dfiReducedDenominator a q) (dfiReducedDenominator b q)
  have hJFull : Integrable (Function.uncurry J) := by
    simpa only [J] using
      integrable_uncurry_hughesYoungLowerBoundaryCentralHeightIntegrand
        hT hc hcHalf u hh hk (by exact_mod_cast hr) a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
  have hJOn : IntegrableOn (Function.uncurry J)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := hJFull.integrableOn
  have hJ : Integrable (Function.uncurry J)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    simpa only [Measure.volume_eq_prod] using hJOn
  have hphysical : Integrable
      (fun t : ℝ => ∫ y in Set.Ioi (0 : ℝ), J y t) :=
    hJ.integral_prod_right
  let A : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  have heq : (fun t : ℝ =>
      hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q) =
      fun t => A * ∫ y in Set.Ioi (0 : ℝ), J y t := by
    funext t
    simpa only [A, J] using
      hughesYoungLowerBoundaryCentralSeriesHeightTerm_eq_setIntegral
        T t c u h k a b r q
  rw [heq]
  exact hphysical.const_mul A

/-- The fixed-modulus endpoint Fubini identity after restoring the exact
DFI arithmetic coefficient. -/
theorem dfiEquation27CentralSummand_lowerBoundaryHeightIntegrated_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hcHalf : c < 1 / 2) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b q : ℕ) :
    dfiEquation27CentralSummand a b r
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) q =
      ∫ t : ℝ, hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q := by
  let A : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  unfold dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_lowerBoundaryHeightIntegrated_eq_heightIntegral
    hT hc hcHalf u hh hk (by exact_mod_cast hr) a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)]
  calc
    A * (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k) r) =
      ∫ t : ℝ, A * ((hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k) r) := by
        rw [MeasureTheory.integral_const_mul]
    _ = ∫ t : ℝ, hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q := by
      apply integral_congr_ae
      filter_upwards with t
      unfold A hughesYoungLowerBoundaryCentralSeriesHeightTerm
        dfiEquation27CentralSummand
      ring

/-- L1-height bound for one endpoint modulus term.  The right side
factorizes into the exact DFI arithmetic coefficient, the physical
critical-beta mass, and the compact height-input mass. -/
theorem integral_norm_hughesYoungLowerBoundaryCentralSeriesHeightTerm_le
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hcHalf : c < 1 / 2) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b q : ℕ) :
    (∫ t : ℝ, ‖hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q‖) ≤
      ‖((a : ℂ) * b)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
        ((∫ y in Set.Ioi (0 : ℝ),
            ‖dfiEquation27C a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (hughesYoungPureReducedStaticWeight T c u h k)
              (y + r) y‖) *
          ∫ t : ℝ, ‖hughesYoungHeightFourierInput T c u t‖) := by
  let J : ℝ → ℝ → ℂ :=
    hughesYoungLowerBoundaryCentralHeightIntegrand T c u h k (r : ℝ)
      a b (dfiReducedDenominator a q) (dfiReducedDenominator b q)
  let f : ℝ → ℂ := fun y => dfiEquation27C a b
    (dfiReducedDenominator a q) (dfiReducedDenominator b q)
    (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y
  let H : ℝ → ℂ := hughesYoungHeightFourierInput T c u
  let A : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  have hJFull : Integrable (Function.uncurry J) := by
    simpa only [J] using
      integrable_uncurry_hughesYoungLowerBoundaryCentralHeightIntegrand
        hT hc hcHalf u hh hk (by exact_mod_cast hr) a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
  have hJOn : IntegrableOn (Function.uncurry J)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := hJFull.integrableOn
  have hJ : Integrable (Function.uncurry J)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    simpa only [Measure.volume_eq_prod] using hJOn
  have hf : Integrable f := by
    simpa only [f] using
      integrable_dfiEquation27C_pureReducedStaticWeight_posShift
        hc hcHalf T u hh hk a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (by exact_mod_cast hr)
  have hH : Integrable (fun t : ℝ => ‖H t‖) := by
    simpa [H] using integrable_heightFourierInput_moment hT hc u 0
  have hmajorFull : Integrable
      (fun z : ℝ × ℝ => ‖f z.1‖ * ‖H z.2‖) := hf.norm.mul_prod hH
  have hmajorOn : IntegrableOn
      (fun z : ℝ × ℝ => ‖f z.1‖ * ‖H z.2‖)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := hmajorFull.integrableOn
  have hmajor : Integrable
      (fun z : ℝ × ℝ => ‖f z.1‖ * ‖H z.2‖)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    simpa only [Measure.volume_eq_prod] using hmajorOn
  have hprod :
      (∫ z : ℝ × ℝ, ‖Function.uncurry J z‖
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) ≤
        ∫ z : ℝ × ℝ, ‖f z.1‖ * ‖H z.2‖
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    apply integral_mono hJ.norm hmajor
    intro z
    simpa only [J, f, H, Function.uncurry_apply_pair] using
      norm_hughesYoungLowerBoundaryCentralHeightIntegrand_le
        T c u hh hk (by exact_mod_cast hr) a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q) z.1 z.2
  have htermInt :=
    integrable_hughesYoungLowerBoundaryCentralSeriesHeightTerm
      hT hc hcHalf u hh hk hr a b q
  have hiterInt : Integrable (fun t : ℝ =>
      ‖A‖ * ∫ y in Set.Ioi (0 : ℝ), ‖J y t‖) :=
    hJ.norm.integral_prod_right.const_mul ‖A‖
  calc
    (∫ t : ℝ, ‖hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q‖) ≤
      ∫ t : ℝ, ‖A‖ * ∫ y in Set.Ioi (0 : ℝ), ‖J y t‖ := by
        apply integral_mono htermInt.norm hiterInt
        intro t
        change ‖hughesYoungLowerBoundaryCentralSeriesHeightTerm
            T t c u h k a b r q‖ ≤
          ‖A‖ * ∫ y in Set.Ioi (0 : ℝ), ‖J y t‖
        rw [hughesYoungLowerBoundaryCentralSeriesHeightTerm_eq_setIntegral]
        simp only [A, J, norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖A‖ * (∫ z : ℝ × ℝ, ‖Function.uncurry J z‖
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        exact (MeasureTheory.integral_prod_symm _ hJ.norm).symm
    _ ≤ ‖A‖ * (∫ z : ℝ × ℝ, ‖f z.1‖ * ‖H z.2‖
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) := by
        exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖A‖ * ((∫ y in Set.Ioi (0 : ℝ), ‖f y‖) *
          ∫ t : ℝ, ‖H t‖) := by
        apply congrArg (‖A‖ * ·)
        exact MeasureTheory.integral_prod_mul
          (fun y : ℝ => ‖f y‖) (fun t : ℝ => ‖H t‖)
    _ = _ := by
      dsimp only [A, f, H]
      rw [norm_mul]

set_option maxHeartbeats 2000000 in
/-- Absolute L1 summability of the full positive-shift endpoint modulus
family.  This is the Tonelli condition needed to exchange the DFI
Ramanujan series with the Hughes--Young height integral. -/
theorem summable_integral_norm_hughesYoungLowerBoundaryCentralSeriesHeightTerm
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hc4 : c ≤ 1 / 4) (u : ℝ)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Summable (fun q : ℕ => ∫ t : ℝ,
      ‖hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q‖) := by
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let Hmass : ℝ := ∫ t : ℝ, ‖hughesYoungHeightFourierInput T c u t‖
  let K : ℝ := ‖((a : ℂ) * b)⁻¹‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * Hmass *
    (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
      (r : ℝ) ^ (-2 * c) * (2312 + 9 * c⁻¹ ^ 3))
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hHmass : 0 ≤ Hmass := by
    dsimp only [Hmass]
    exact integral_nonneg (fun t => norm_nonneg _)
  have hmajor : Summable (fun q : ℕ =>
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left K
  apply hmajor.of_nonneg_of_le
  · intro q
    exact integral_nonneg (fun t => norm_nonneg _)
  · intro q
    by_cases hq0 : q = 0
    · subst q
      simp [hughesYoungLowerBoundaryCentralSeriesHeightTerm,
        dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
    · have hq : 0 < q := Nat.pos_of_ne_zero hq0
      letI : NeZero q := ⟨hq0⟩
      let S : ℝ :=
        1 +
          ‖(Real.log r : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q)‖ +
          ‖(Real.log r : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q)‖
      have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
        have hCX :=
          norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
        have hCOne :=
          norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
        dsimp only [S, A]
        unfold hughesYoungEquation84LogBudget
        linarith
      have hS0 : 0 ≤ S := by dsimp only [S]; positivity
      have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
        zero_le_one.trans
          (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
      have hcInv3 : 0 ≤ c⁻¹ ^ 3 := by positivity
      have hCoeff :=
        norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
      have hPhysical :=
        integral_norm_dfiEquation27C_pureReducedStaticWeight_posShift_le
          hc hc4 T u hh hk a b (dfiReducedDenominator a q)
            (dfiReducedDenominator b q)
            (show (1 : ℝ) ≤ r by exact_mod_cast hr)
      have hTerm :=
        integral_norm_hughesYoungLowerBoundaryCentralSeriesHeightTerm_le
          hT hc (hc4.trans_lt (by norm_num)) u hh hk hr a b q
      change (∫ t : ℝ,
          ‖hughesYoungLowerBoundaryCentralSeriesHeightTerm
            T t c u h k a b r q‖) ≤ _ at hTerm
      change (∫ y in Set.Ioi (0 : ℝ),
          ‖dfiEquation27C a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (hughesYoungPureReducedStaticWeight T c u h k)
            (y + r) y‖) ≤
        ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          (r : ℝ) ^ (-2 * c) *
          (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3) at hPhysical
      calc
        (∫ t : ℝ, ‖hughesYoungLowerBoundaryCentralSeriesHeightTerm
            T t c u h k a b r q‖) ≤
          ‖((a : ℂ) * b)⁻¹‖ *
            ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
            ((∫ y in Set.Ioi (0 : ℝ),
                ‖dfiEquation27C a b
                  (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                  (hughesYoungPureReducedStaticWeight T c u h k)
                  (y + r) y‖) * Hmass) := by
              simpa only [Hmass] using hTerm
        _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
            (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
            ((‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
                (r : ℝ) ^ (-2 * c) *
                (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3)) * Hmass) := by
              gcongr
        _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
            (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
            ((‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
                (r : ℝ) ^ (-2 * c) *
                ((2312 + 9 * c⁻¹ ^ 3) *
                  (A + 4 * Real.log (q : ℝ)) ^ 2)) * Hmass) := by
              gcongr
              calc
                2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3 =
                    (2312 + 9 * c⁻¹ ^ 3) * S ^ 2 := by ring
                _ ≤ (2312 + 9 * c⁻¹ ^ 3) *
                    (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
        _ = K * (((q : ℝ) ^ 2)⁻¹ *
            (A + 4 * Real.log (q : ℝ)) ^ 2) := by
              dsimp only [K]
              ring

/-- Unconditional series-level Fubini for the positive-shift lower
endpoint.  This is the exact bridge from the height integral of the DFI
series occurring in Hughes--Young to the already evaluated endpoint
weight. -/
theorem dfiEquation27CentralSeries_lowerBoundaryHeightIntegrated_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hc4 : c ≤ 1 / 4) (u : ℝ)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    dfiEquation27CentralSeries a b r
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) =
      ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralSeries a b r
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k) := by
  let F : ℕ → ℝ → ℂ := fun q t =>
    hughesYoungLowerBoundaryCentralSeriesHeightTerm
      T t c u h k a b r q
  have hInt : ∀ q : ℕ, Integrable (F q) := by
    intro q
    simpa only [F] using
      integrable_hughesYoungLowerBoundaryCentralSeriesHeightTerm
        hT hc (hc4.trans_lt (by norm_num)) u hh hk hr a b q
  have hNormSum : Summable (fun q : ℕ => ∫ t : ℝ, ‖F q t‖) := by
    simpa only [F] using
      summable_integral_norm_hughesYoungLowerBoundaryCentralSeriesHeightTerm
        hT hc hc4 u hh hk ha hb hr
  have hswap : (∑' q : ℕ, ∫ t : ℝ, F q t) =
      ∫ t : ℝ, ∑' q : ℕ, F q t :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hInt hNormSum
  unfold dfiEquation27CentralSeries
  simp_rw [dfiEquation27CentralSummand_lowerBoundaryHeightIntegrated_eq_heightIntegral
    hT hc (hc4.trans_lt (by norm_num)) u hh hk hr]
  calc
    (∑' q : ℕ, ∫ t : ℝ,
        hughesYoungLowerBoundaryCentralSeriesHeightTerm
          T t c u h k a b r q) =
      ∫ t : ℝ, ∑' q : ℕ, F q t := by
        simpa only [F] using hswap
    _ = ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        ∑' q : ℕ, dfiEquation27CentralSummand a b r
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k) q := by
      apply integral_congr_ae
      filter_upwards with t
      unfold F hughesYoungLowerBoundaryCentralSeriesHeightTerm
      rw [tsum_mul_left]

/-- Exact signed-shift height decomposition of the complete lower-endpoint
DFI series. -/
theorem dfiSignedCentralSeries_lowerBoundaryHeightIntegrated_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hc4 : c ≤ 1 / 4) (u : ℝ)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) :
    dfiSignedCentralSeries a b r
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) =
      ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k) := by
  cases r with
  | ofNat r =>
      have hrPos : 0 < r := by
        by_contra hzero
        exact hr (congrArg Int.ofNat (Nat.eq_zero_of_not_pos hzero))
      exact dfiEquation27CentralSeries_lowerBoundaryHeightIntegrated_eq_heightIntegral
        hT hc hc4 u hh hk ha hb hrPos
  | negSucc n =>
      let r : ℕ := n + 1
      have hrPos : 0 < r := by dsimp only [r]; omega
      have hrEq : Int.negSucc n = -((r : ℕ) : ℤ) := by
        dsimp only [r]
        omega
      rw [hrEq]
      simp_rw [dfiSignedCentralSeries_neg_ofNat a b r hrPos]
      exact
        dfiEquation27CentralSeries_swappedLowerBoundaryHeightIntegrated_eq_heightIntegral
          hT hc hc4 u hh hk ha hb hrPos

/-- The positive lower-boundary DFI series is genuinely integrable in the
physical height.  This is stronger than the series-level integral identity:
it records the `L¹` fact needed by finite signed-shift additivity. -/
theorem integrable_heightWeight_mul_dfiEquation27CentralSeries_lowerBoundary
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hc4 : c ≤ 1 / 4) (u : ℝ)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      dfiEquation27CentralSeries a b r
        (hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k)) := by
  let F : ℕ → ℝ → ℂ := fun q t =>
    hughesYoungLowerBoundaryCentralSeriesHeightTerm
      T t c u h k a b r q
  have hInt : ∀ q : ℕ, Integrable (F q) := by
    intro q
    simpa only [F] using
      integrable_hughesYoungLowerBoundaryCentralSeriesHeightTerm
        hT hc (hc4.trans_lt (by norm_num)) u hh hk hr a b q
  have hNormSum : Summable (fun q : ℕ => ∫ t : ℝ, ‖F q t‖) := by
    simpa only [F] using
      summable_integral_norm_hughesYoungLowerBoundaryCentralSeriesHeightTerm
        hT hc hc4 u hh hk ha hb hr
  have hSeries : Integrable (fun t : ℝ => ∑' q : ℕ, F q t) :=
    integrable_tsum_of_summable_integral_norm hInt hNormSum
  apply hSeries.congr
  filter_upwards with t
  unfold F hughesYoungLowerBoundaryCentralSeriesHeightTerm
    dfiEquation27CentralSeries
  rw [tsum_mul_left]

/-- The negative lower-boundary DFI series, with the source-mandated
coordinate swap, is genuinely integrable in the physical height. -/
theorem integrable_heightWeight_mul_dfiEquation27CentralSeries_swappedLowerBoundary
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hc4 : c ≤ 1 / 4) (u : ℝ)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      dfiEquation27CentralSeries b a r
        (dfiSwapWeight
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k))) := by
  let F : ℕ → ℝ → ℂ := fun q t =>
    hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
      T t c u h k a b r q
  have hInt : ∀ q : ℕ, Integrable (F q) := by
    intro q
    simpa only [F] using
      integrable_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        hT hc (hc4.trans_lt (by norm_num)) u hh hk hr a b q
  have hNormSum : Summable (fun q : ℕ => ∫ t : ℝ, ‖F q t‖) := by
    simpa only [F] using
      summable_integral_norm_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        hT hc hc4 u hh hk ha hb hr
  have hSeries : Integrable (fun t : ℝ => ∑' q : ℕ, F q t) :=
    integrable_tsum_of_summable_integral_norm hInt hNormSum
  apply hSeries.congr
  filter_upwards with t
  unfold F hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
    dfiEquation27CentralSeries
  rw [tsum_mul_left]

/-- Both sign conventions of a nonzero endpoint shift are integrable before
the finite shift window is summed. -/
theorem integrable_heightWeight_mul_dfiSignedCentralSeries_lowerBoundary
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hc4 : c ≤ 1 / 4) (u : ℝ)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      dfiSignedCentralSeries a b r
        (hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k)) := by
  cases r with
  | ofNat r =>
      have hrPos : 0 < r := by
        by_contra hzero
        exact hr (congrArg Int.ofNat (Nat.eq_zero_of_not_pos hzero))
      exact
        integrable_heightWeight_mul_dfiEquation27CentralSeries_lowerBoundary
          hT hc hc4 u hh hk ha hb hrPos
  | negSucc n =>
      let r : ℕ := n + 1
      have hrPos : 0 < r := by dsimp only [r]; omega
      have hrEq : Int.negSucc n = -((r : ℕ) : ℤ) := by
        dsimp only [r]
        omega
      rw [hrEq]
      simp_rw [dfiSignedCentralSeries_neg_ofNat a b r hrPos]
      exact
        integrable_heightWeight_mul_dfiEquation27CentralSeries_swappedLowerBoundary
          hT hc hc4 u hh hk ha hb hrPos

set_option maxHeartbeats 2000000 in
/-- Integrated equation-(65) bound for one positive DFI central integral.
The right side is completely explicit: a Fourier-decay factor times the
critical-beta absolute mass and the exact static Mellin scale. -/
theorem norm_dfiEquation27CentralIntegral_lowerBoundaryHeightIntegrated_posShift_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u r : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hc1 : c ≤ 1) (hu : |u| ≤ T / 8) (hr : 1 ≤ r)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b qx qy : ℕ) :
    ‖dfiEquation27CentralIntegral a b qx qy
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) r‖ ≤
      ((2 : ℝ) ^ j *
        ((15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))) *
        (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          r ^ (-2 * c) *
          (2312 *
              (1 +
                ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
                ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) ^ 2 +
            9 *
              (1 +
                ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
                ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) ^ 2 *
              c⁻¹ ^ 3)) := by
  let M : ℝ :=
    (2 : ℝ) ^ j *
      ((15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
  let B : ℝ :=
    ‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
      r ^ (-2 * c) *
      (2312 *
          (1 +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) ^ 2 +
        9 *
          (1 +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) ^ 2 *
          c⁻¹ ^ 3)
  have hE0 : 0 ≤
      (15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)) := by
    exact (mul_nonneg (pow_nonneg (abs_nonneg (0 : ℝ)) j)
      (norm_nonneg (hughesYoungHeightTransform T c u 0))).trans
        (h65 j T c u 0 hT hc hc1 hu)
  have hM0 : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j) hE0
  have hpure :=
    integrableOn_dfiEquation27C_pureReducedStaticWeight_posShift
      hc (hc4.trans_lt (by norm_num)) T u hh hk a b qx qy
        (zero_lt_one.trans_le hr)
  have hmajor : IntegrableOn (fun y : ℝ => M *
      ‖dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖)
      (Set.Ioi 0) := hpure.norm.const_mul M
  rw [dfiEquation27CentralIntegral_lowerBoundaryHeightIntegrated_eq_Ioi]
  have hnorm :
      ‖∫ y in Set.Ioi (0 : ℝ),
        dfiEquation27C a b qx qy
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)
          (y + r) y‖ ≤
        ∫ y in Set.Ioi (0 : ℝ), M *
          ‖dfiEquation27C a b qx qy
            (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖ := by
    apply norm_integral_le_of_norm_le hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    have hyr : 0 < y + r := add_pos hy0 (zero_lt_one.trans_le hr)
    have hpoint :=
      norm_dfiEquation27C_lowerBoundaryHeightIntegrated_posShift_le
        h65 j hT hc hc1 hu hyr hy0 hr (by ring) h k a b qx qy
    change ‖dfiEquation27C a b qx qy
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)
        (y + r) y‖ ≤
      ‖dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖ * M at hpoint
    exact hpoint.trans_eq (mul_comm _ _)
  calc
    _ ≤ ∫ y in Set.Ioi (0 : ℝ), M *
        ‖dfiEquation27C a b qx qy
          (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖ := hnorm
    _ = M * (∫ y in Set.Ioi (0 : ℝ),
        ‖dfiEquation27C a b qx qy
          (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ M * B := by
      apply mul_le_mul_of_nonneg_left _ hM0
      exact integral_norm_dfiEquation27C_pureReducedStaticWeight_posShift_le
        hc hc4 T u hh hk a b qx qy hr
    _ = _ := by rfl

set_option maxHeartbeats 2000000 in
/-- Absolute summability in the DFI modulus of the literal positive-shift
lower-endpoint central summands.  The proof keeps the exact equation-(27)
arithmetic coefficient and uses its inverse-square bound only after the
physical central integral has been estimated. -/
theorem summable_dfiEquation27CentralSummand_lowerBoundaryHeightIntegrated_posShift
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hc1 : c ≤ 1) (hu : |u| ≤ T / 8)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) q) := by
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let E : ℝ :=
    (2 : ℝ) ^ j *
      ((15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
  let K : ℝ := ‖((a : ℂ) * b)⁻¹‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * E *
    (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
      (r : ℝ) ^ (-2 * c) * (2312 + 9 * c⁻¹ ^ 3))
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hBase : 0 ≤
      (15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)) := by
    exact (mul_nonneg (pow_nonneg (abs_nonneg (0 : ℝ)) j)
      (norm_nonneg (hughesYoungHeightTransform T c u 0))).trans
        (h65 j T c u 0 hT hc hc1 hu)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j) hBase
  have hmajor : Summable (fun q : ℕ =>
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left K
  apply Summable.of_norm_bounded hmajor
  intro q
  by_cases hq0 : q = 0
  · subst q
    simp [dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    let S : ℝ :=
      1 +
        ‖(Real.log r : ℂ) +
          dfiEquation27LogConstant b (dfiReducedDenominator b q)‖ +
        ‖(Real.log r : ℂ) +
          dfiEquation27LogConstant a (dfiReducedDenominator a q)‖
    have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
      have hCX :=
        norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
      have hCOne :=
        norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
      dsimp only [S, A]
      unfold hughesYoungEquation84LogBudget
      linarith
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
      zero_le_one.trans
        (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
    have hcInv3 : 0 ≤ c⁻¹ ^ 3 := by positivity
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
    have hIntegral :=
      norm_dfiEquation27CentralIntegral_lowerBoundaryHeightIntegrated_posShift_le
        h65 j hT hc hc4 hc1 hu (show (1 : ℝ) ≤ r by exact_mod_cast hr)
        hh hk a b (dfiReducedDenominator a q)
          (dfiReducedDenominator b q)
    unfold dfiEquation27CentralSummand
    simp only [norm_mul]
    change ‖((a : ℂ) * b)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
        ‖dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) r‖ ≤ _
    change ‖dfiEquation27CentralIntegral a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) r‖ ≤
      E * (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
        (r : ℝ) ^ (-2 * c) *
        (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3)) at hIntegral
    calc
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          (E * (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
            (r : ℝ) ^ (-2 * c) *
            (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3))) := by
        gcongr
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          (E * (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
            (r : ℝ) ^ (-2 * c) *
            ((2312 + 9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2))) := by
        gcongr
        calc
          2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3 =
              (2312 + 9 * c⁻¹ ^ 3) * S ^ 2 := by ring
          _ ≤ (2312 + 9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
      _ = K * (((q : ℝ) ^ 2)⁻¹ *
          (A + 4 * Real.log (q : ℝ)) ^ 2) := by
        dsimp only [K]
        ring

set_option maxHeartbeats 3000000 in
/-- Quantitative positive-shift endpoint bound after the complete DFI
modulus sum.  This is the first assembled endpoint estimate: the modulus
sum is no longer a theorem parameter, and its entire cost is the explicit
equation-(84) logarithmic-profile mass. -/
theorem norm_dfiEquation27CentralSeries_lowerBoundaryHeightIntegrated_posShift_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hc1 : c ≤ 1) (hu : |u| ≤ T / 8)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ‖dfiEquation27CentralSeries a b r
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)‖ ≤
      ‖((a : ℂ) * b)⁻¹‖ *
        ((a * b * r ^ 2 : ℕ) : ℝ) *
        ((2 : ℝ) ^ j *
          ((15 * T / 4) *
            (c⁻¹ * Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
              (25 + 8 * u ^ 2) ^ 4 *
              hughesYoungHeightInputDerivativeConstant Cw j *
              (((T / 16)⁻¹ * (1 + |u|)) ^ j))) *
        (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          (r : ℝ) ^ (-2 * c) * (2312 + 9 * c⁻¹ ^ 3))) *
        (hughesYoungEquation84LogBudget a b r ^ 2 *
          hughesYoungEquation84LogProfileMass) := by
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let E : ℝ :=
    (2 : ℝ) ^ j *
      ((15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
  let K : ℝ := ‖((a : ℂ) * b)⁻¹‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * E *
    (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
      (r : ℝ) ^ (-2 * c) * (2312 + 9 * c⁻¹ ^ 3))
  have hA1 : 1 ≤ A := one_le_hughesYoungEquation84LogBudget a b r
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hBase : 0 ≤
      (15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)) := by
    exact (mul_nonneg (pow_nonneg (abs_nonneg (0 : ℝ)) j)
      (norm_nonneg (hughesYoungHeightTransform T c u 0))).trans
        (h65 j T c u 0 hT hc hc1 hu)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j) hBase
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hs :=
    summable_dfiEquation27CentralSummand_lowerBoundaryHeightIntegrated_posShift
      h65 j hT hc hc4 hc1 hu hh hk ha hb hr
  have hmajorSummable : Summable (fun q : ℕ =>
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A hA0).mul_left K
  have hterm : ∀ q : ℕ,
      ‖dfiEquation27CentralSummand a b r
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) q‖ ≤
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2) := by
    intro q
    by_cases hq0 : q = 0
    · subst q
      simp [dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
    · have hq : 0 < q := Nat.pos_of_ne_zero hq0
      letI : NeZero q := ⟨hq0⟩
      let S : ℝ :=
        1 +
          ‖(Real.log r : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q)‖ +
          ‖(Real.log r : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q)‖
      have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
        have hCX :=
          norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
        have hCOne :=
          norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
        dsimp only [S, A]
        unfold hughesYoungEquation84LogBudget
        linarith
      have hS0 : 0 ≤ S := by dsimp only [S]; positivity
      have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
        zero_le_one.trans
          (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
      have hcInv3 : 0 ≤ c⁻¹ ^ 3 := by positivity
      have hCoeff :=
        norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
      have hIntegral :=
        norm_dfiEquation27CentralIntegral_lowerBoundaryHeightIntegrated_posShift_le
          h65 j hT hc hc4 hc1 hu (show (1 : ℝ) ≤ r by exact_mod_cast hr)
          hh hk a b (dfiReducedDenominator a q)
            (dfiReducedDenominator b q)
      unfold dfiEquation27CentralSummand
      simp only [norm_mul]
      change ‖((a : ℂ) * b)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ‖dfiEquation27CentralIntegral a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) r‖ ≤ _
      change ‖dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) r‖ ≤
        E * (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
          (r : ℝ) ^ (-2 * c) *
          (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3)) at hIntegral
      calc
        _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
            (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
            (E * (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
              (r : ℝ) ^ (-2 * c) *
              (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3))) := by
          gcongr
        _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
            (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
            (E * (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
              (r : ℝ) ^ (-2 * c) *
              ((2312 + 9 * c⁻¹ ^ 3) *
                (A + 4 * Real.log (q : ℝ)) ^ 2))) := by
          gcongr
          calc
            2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3 =
                (2312 + 9 * c⁻¹ ^ 3) * S ^ 2 := by ring
            _ ≤ (2312 + 9 * c⁻¹ ^ 3) *
                (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
        _ = K * (((q : ℝ) ^ 2)⁻¹ *
            (A + 4 * Real.log (q : ℝ)) ^ 2) := by
          dsimp only [K]
          ring
  unfold dfiEquation27CentralSeries
  calc
    ‖∑' q : ℕ, dfiEquation27CentralSummand a b r
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) q‖ ≤
        ∑' q : ℕ, ‖dfiEquation27CentralSummand a b r
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k) q‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' q : ℕ, K * (((q : ℝ) ^ 2)⁻¹ *
          (A + 4 * Real.log (q : ℝ)) ^ 2) :=
      hs.norm.tsum_le_tsum hterm hmajorSummable
    _ = K * (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (A + 4 * Real.log (q : ℝ)) ^ 2) := by rw [tsum_mul_left]
    _ ≤ K * (A ^ 2 * hughesYoungEquation84LogProfileMass) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_natCast_inv_sq_mul_four_log_profile_sq_le hA1) hK
    _ = _ := by
      dsimp only [K, E, A]
      ring

/-- The complete equation-(65) factor used by both signed endpoint
branches. -/
noncomputable def hughesYoungEndpointEquation65Majorant
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ) (T c u : ℝ) : ℝ :=
  (2 : ℝ) ^ j *
    ((15 * T / 4) *
      (c⁻¹ * Real.exp
        (100 * c ^ 2 - 84 * u ^ 2 +
          4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
        (25 + 8 * u ^ 2) ^ 4 *
        hughesYoungHeightInputDerivativeConstant Cw j *
        (((T / 16)⁻¹ * (1 + |u|)) ^ j)))

theorem hughesYoungEndpointEquation65Majorant_eq
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ) (T c u : ℝ) :
    hughesYoungEndpointEquation65Majorant Cγ Cw j T c u =
      (2 : ℝ) ^ j * hughesYoungEquation65Bound Cγ Cw j T c u := by
  rfl

/-- Common arithmetic, Fourier and physical-scale prefactor before the
summable inverse-square/log-square modulus profile is inserted. -/
noncomputable def hughesYoungEndpointDFIPrefactor
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ) (T c u : ℝ)
    (h k a b r : ℕ) : ℝ :=
  ‖((a : ℂ) * b)⁻¹‖ * ((a * b * r ^ 2 : ℕ) : ℝ) *
    hughesYoungEndpointEquation65Majorant Cγ Cw j T c u *
    (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
      (r : ℝ) ^ (-2 * c) * (2312 + 9 * c⁻¹ ^ 3))

/-- The positive series estimate in the common signed-branch prefactor
notation. -/
theorem norm_dfiEquation27CentralSeries_lowerBoundaryHeightIntegrated_posShift_le_prefactor
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hc1 : c ≤ 1) (hu : |u| ≤ T / 8)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ‖dfiEquation27CentralSeries a b r
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)‖ ≤
      hughesYoungEndpointDFIPrefactor Cγ Cw j T c u h k a b r *
        (hughesYoungEquation84LogBudget a b r ^ 2 *
          hughesYoungEquation84LogProfileMass) := by
  have hpos :=
    norm_dfiEquation27CentralSeries_lowerBoundaryHeightIntegrated_posShift_le
      h65 j hT hc hc4 hc1 hu hh hk ha hb hr
  convert hpos using 1
  unfold hughesYoungEndpointDFIPrefactor
    hughesYoungEndpointEquation65Majorant
  ring

set_option maxHeartbeats 2500000 in
/-- Pointwise inverse-square/log-square majorant for the negative signed
endpoint summand.  The theorem is stated for the actual coordinate-swapped
DFI summand, so subsequent summation introduces no convention change. -/
theorem norm_dfiEquation27CentralSummand_swappedLowerBoundaryHeightIntegrated_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hc1 : c ≤ 1) (hu : |u| ≤ T / 8)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (q : ℕ) :
    ‖dfiEquation27CentralSummand b a r
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) q‖ ≤
      hughesYoungEndpointDFIPrefactor Cγ Cw j T c u h k b a r *
        (((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget b a r +
            4 * Real.log (q : ℝ)) ^ 2) := by
  let A : ℝ := hughesYoungEquation84LogBudget b a r
  let E : ℝ :=
    (2 : ℝ) ^ j *
      ((15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
  let K : ℝ :=
    hughesYoungEndpointDFIPrefactor Cγ Cw j T c u h k b a r
  change _ ≤ K * (((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2)
  by_cases hq0 : q = 0
  · subst q
    simp [dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    let S : ℝ :=
      1 +
        ‖(Real.log r : ℂ) +
          dfiEquation27LogConstant a (dfiReducedDenominator a q)‖ +
        ‖(Real.log r : ℂ) +
          dfiEquation27LogConstant b (dfiReducedDenominator b q)‖
    have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
      have hCA :=
        norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
      have hCB :=
        norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
      dsimp only [S, A]
      unfold hughesYoungEquation84LogBudget
      linarith
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
      zero_le_one.trans
        (one_le_hughesYoungEquation84LogBudget_add_four_log b a r q hq)
    have hcInv3 : 0 ≤ c⁻¹ ^ 3 := by positivity
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq b a r q hb ha hr
    have hIntegral :=
      norm_dfiEquation27CentralIntegral_swappedLowerBoundaryHeightIntegrated_posShift_le
        h65 j hT hc hc4 hc1 hu (show (1 : ℝ) ≤ r by exact_mod_cast hr)
        hh hk a b (dfiReducedDenominator a q)
          (dfiReducedDenominator b q)
    unfold dfiEquation27CentralSummand
    simp only [norm_mul]
    change ‖((b : ℂ) * a)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
        ‖dfiEquation27CentralIntegral b a
          (dfiReducedDenominator b q) (dfiReducedDenominator a q)
          (dfiSwapWeight
            (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) r‖ ≤ _
    change ‖dfiEquation27CentralIntegral b a
        (dfiReducedDenominator b q) (dfiReducedDenominator a q)
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) r‖ ≤
      E * (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
        (r : ℝ) ^ (-2 * c) *
        (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3)) at hIntegral
    calc
      _ ≤ ‖((b : ℂ) * a)⁻¹‖ *
          (((b * a * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          (E * (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
            (r : ℝ) ^ (-2 * c) *
            (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3))) := by
        gcongr
      _ ≤ ‖((b : ℂ) * a)⁻¹‖ *
          (((b * a * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          (E * (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
            (r : ℝ) ^ (-2 * c) *
            ((2312 + 9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2))) := by
        have hBase : 0 ≤
            (15 * T / 4) *
              (c⁻¹ * Real.exp
                (100 * c ^ 2 - 84 * u ^ 2 +
                  4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
                (25 + 8 * u ^ 2) ^ 4 *
                hughesYoungHeightInputDerivativeConstant Cw j *
                (((T / 16)⁻¹ * (1 + |u|)) ^ j)) := by
          exact (mul_nonneg (pow_nonneg (abs_nonneg (0 : ℝ)) j)
            (norm_nonneg (hughesYoungHeightTransform T c u 0))).trans
              (h65 j T c u 0 hT hc hc1 hu)
        have hE : 0 ≤ E := by
          dsimp only [E]
          exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j) hBase
        gcongr
        calc
          2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3 =
              (2312 + 9 * c⁻¹ ^ 3) * S ^ 2 := by ring
          _ ≤ (2312 + 9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
      _ = K * (((q : ℝ) ^ 2)⁻¹ *
          (A + 4 * Real.log (q : ℝ)) ^ 2) := by
        dsimp only [K, hughesYoungEndpointDFIPrefactor,
          hughesYoungEndpointEquation65Majorant, E]
        ring

/-- Absolute convergence of the negative signed endpoint modulus series. -/
theorem summable_dfiEquation27CentralSummand_swappedLowerBoundaryHeightIntegrated
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hc1 : c ≤ 1) (hu : |u| ≤ T / 8)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Summable (fun q : ℕ =>
      dfiEquation27CentralSummand b a r
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) q) := by
  let A : ℝ := hughesYoungEquation84LogBudget b a r
  let K : ℝ :=
    hughesYoungEndpointDFIPrefactor Cγ Cw j T c u h k b a r
  have hA0 : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget b a r)
  have hm : Summable (fun q : ℕ =>
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A hA0).mul_left K
  apply Summable.of_norm_bounded hm
  intro q
  simpa only [K, A] using
    norm_dfiEquation27CentralSummand_swappedLowerBoundaryHeightIntegrated_le
      h65 j hT hc hc4 hc1 hu hh hk ha hb hr q

set_option maxHeartbeats 2000000 in
/-- Quantitative negative signed endpoint bound after the complete DFI
modulus sum. -/
theorem norm_dfiEquation27CentralSeries_swappedLowerBoundaryHeightIntegrated_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hc1 : c ≤ 1) (hu : |u| ≤ T / 8)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ‖dfiEquation27CentralSeries b a r
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k))‖ ≤
      hughesYoungEndpointDFIPrefactor Cγ Cw j T c u h k b a r *
        (hughesYoungEquation84LogBudget b a r ^ 2 *
          hughesYoungEquation84LogProfileMass) := by
  let A : ℝ := hughesYoungEquation84LogBudget b a r
  let K : ℝ :=
    hughesYoungEndpointDFIPrefactor Cγ Cw j T c u h k b a r
  have hA1 : 1 ≤ A := one_le_hughesYoungEquation84LogBudget b a r
  have hBase : 0 ≤
      (15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)) := by
    exact (mul_nonneg (pow_nonneg (abs_nonneg (0 : ℝ)) j)
      (norm_nonneg (hughesYoungHeightTransform T c u 0))).trans
        (h65 j T c u 0 hT hc hc1 hu)
  have hEndpoint0 : 0 ≤
      hughesYoungEndpointEquation65Majorant Cγ Cw j T c u := by
    unfold hughesYoungEndpointEquation65Majorant
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j) hBase
  have hK0 : 0 ≤ K := by
    dsimp only [K, hughesYoungEndpointDFIPrefactor]
    positivity
  have hs :=
    summable_dfiEquation27CentralSummand_swappedLowerBoundaryHeightIntegrated
      h65 j hT hc hc4 hc1 hu hh hk ha hb hr
  have hm : Summable (fun q : ℕ =>
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A
      (zero_le_one.trans hA1)).mul_left K
  have hterm : ∀ q : ℕ,
      ‖dfiEquation27CentralSummand b a r
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) q‖ ≤
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2) := by
    intro q
    simpa only [K, A] using
      (norm_dfiEquation27CentralSummand_swappedLowerBoundaryHeightIntegrated_le
        (Cγ := Cγ) (Cw := Cw) h65 j hT hc hc4 hc1 hu
          hh hk ha hb hr q)
  unfold dfiEquation27CentralSeries
  calc
    ‖∑' q : ℕ, dfiEquation27CentralSummand b a r
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) q‖ ≤
      ∑' q : ℕ, ‖dfiEquation27CentralSummand b a r
        (dfiSwapWeight
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) q‖ :=
        norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' q : ℕ, K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2) :=
      hs.norm.tsum_le_tsum hterm hm
    _ = K * (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2) := by rw [tsum_mul_left]
    _ ≤ K * (A ^ 2 * hughesYoungEquation84LogProfileMass) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_natCast_inv_sq_mul_four_log_profile_sq_le hA1) hK0
    _ = _ := by
      dsimp only [K, A]

/-- The branch-correct quantitative majorant for a nonzero signed endpoint
shift. -/
noncomputable def hughesYoungEndpointSignedShiftMajorant
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ) (T c u : ℝ)
    (h k a b : ℕ) (r : ℤ) : ℝ :=
  if 0 ≤ r then
    hughesYoungEndpointDFIPrefactor Cγ Cw j T c u h k a b r.toNat *
      (hughesYoungEquation84LogBudget a b r.toNat ^ 2 *
        hughesYoungEquation84LogProfileMass)
  else
    hughesYoungEndpointDFIPrefactor Cγ Cw j T c u h k b a (-r).toNat *
      (hughesYoungEquation84LogBudget b a (-r).toNat ^ 2 *
        hughesYoungEquation84LogProfileMass)

/-- At the native contour, the full lower-endpoint majorant is exactly the
already-normalized signed-shift coefficient times the Fourier-decay factor
and the remaining beta-integral constant.  This identity is what permits
the whole finite shift family to reuse the established polynomial mass
bound instead of being estimated a second time. -/
theorem hughesYoungEndpointSignedShiftMajorant_eq_smallContourCoefficient
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ) (T u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {r : ℤ} (hr : r ≠ 0) :
    hughesYoungEndpointSignedShiftMajorant Cγ Cw j T
        (hughesYoungSmallContour T) u h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r =
      hughesYoungEndpointEquation65Majorant Cγ Cw j T
          (hughesYoungSmallContour T) u *
        ((2312 + 9 * (hughesYoungSmallContour T)⁻¹ ^ 3) / 4) *
        hughesYoungSmallContourSignedShiftCoefficient T h k r := by
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  have hnorm :
      ‖(((a : ℂ) * (b : ℂ))⁻¹)‖ *
          ‖hughesYoungPureReducedStaticScaleConstant T
            (hughesYoungSmallContour T) u h k‖ =
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
          (b : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) := by
    simpa only [a, b] using
      norm_inverse_reducedProduct_mul_pureStaticScale_eq
        T (hughesYoungSmallContour T) u hh hk
  by_cases hsign : 0 ≤ r
  · have hrpos : 0 < r := lt_of_le_of_ne hsign (Ne.symm hr)
    have hrnat : 0 < r.toNat := by omega
    unfold hughesYoungEndpointSignedShiftMajorant
      hughesYoungEndpointDFIPrefactor
      hughesYoungSmallContourSignedShiftCoefficient
    simp only [hsign, if_true, hr, if_false]
    rw [← hnorm]
    ring
  · have hrneg : r < 0 := lt_of_not_ge hsign
    have hrnat : 0 < (-r).toNat := by omega
    have hnormSwap :
        ‖(((b : ℂ) * (a : ℂ))⁻¹)‖ *
            ‖hughesYoungPureReducedStaticScaleConstant T
              (hughesYoungSmallContour T) u h k‖ =
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            (a : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) *
            (b : ℝ) ^ (hughesYoungSmallContour T - 1 / 2) := by
      simpa only [mul_comm] using hnorm
    unfold hughesYoungEndpointSignedShiftMajorant
      hughesYoungEndpointDFIPrefactor
      hughesYoungSmallContourSignedShiftCoefficient
    simp only [hsign, if_false, hr]
    rw [← hnormSwap]
    ring

/-- Summing the exact endpoint normalization over the literal finite
Hughes--Young shift window introduces no further arithmetic loss.  The
zero shift vanishes on both sides, and every nonzero shift is the common
equation-(65) factor times the already assembled small-contour mass. -/
theorem sum_hughesYoungEndpointSignedShiftMajorant_eq
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ) (T u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (K : ℕ) :
    ∑ r ∈ hughesYoungShiftInterval
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound (K + 1))
          (hughesYoungFullDyadicBound (K + 1)),
        (if r = 0 then 0 else
          hughesYoungEndpointSignedShiftMajorant Cγ Cw j T
            (hughesYoungSmallContour T) u h k
            (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) r) =
      hughesYoungEndpointEquation65Majorant Cγ Cw j T
          (hughesYoungSmallContour T) u *
        ((2312 + 9 * (hughesYoungSmallContour T)⁻¹ ^ 3) / 4) *
        hughesYoungFiniteSmallContourShiftMass T h k K := by
  let S := hughesYoungShiftInterval
    (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
    (hughesYoungFullDyadicBound (K + 1))
    (hughesYoungFullDyadicBound (K + 1))
  let A := hughesYoungEndpointEquation65Majorant Cγ Cw j T
    (hughesYoungSmallContour T) u *
      ((2312 + 9 * (hughesYoungSmallContour T)⁻¹ ^ 3) / 4)
  calc
    ∑ r ∈ S, (if r = 0 then 0 else
          hughesYoungEndpointSignedShiftMajorant Cγ Cw j T
            (hughesYoungSmallContour T) u h k
            (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) r) =
        ∑ r ∈ S, A *
          hughesYoungSmallContourSignedShiftCoefficient T h k r := by
      apply Finset.sum_congr rfl
      intro r _hrmem
      by_cases hr : r = 0
      · subst r
        simp [hughesYoungSmallContourSignedShiftCoefficient]
      · simp only [hr, if_false]
        exact hughesYoungEndpointSignedShiftMajorant_eq_smallContourCoefficient
          Cγ Cw j T u hh hk hr
    _ = A * hughesYoungFiniteSmallContourShiftMass T h k K := by
      rw [← Finset.mul_sum]
      rfl
    _ = _ := rfl

set_option maxHeartbeats 2000000 in
/-- Both signed branches of the lower-endpoint DFI central series satisfy
one literal branch-correct bound. -/
theorem norm_dfiSignedCentralSeries_lowerBoundaryHeightIntegrated_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hc1 : c ≤ 1) (hu : |u| ≤ T / 8)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) :
    ‖dfiSignedCentralSeries a b r
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)‖ ≤
      hughesYoungEndpointSignedShiftMajorant Cγ Cw j T c u h k a b r := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        by_contra hn0
        apply hr
        simp_all
      have hpos :=
        norm_dfiEquation27CentralSeries_lowerBoundaryHeightIntegrated_posShift_le_prefactor
          h65 j hT hc hc4 hc1 hu hh hk ha hb hn
      simpa [dfiSignedCentralSeries,
        hughesYoungEndpointSignedShiftMajorant] using hpos
  | negSucc n =>
      let m : ℕ := n + 1
      have hm : 0 < m := Nat.succ_pos n
      have hrEq : Int.negSucc n = -(m : ℤ) := by omega
      have hnonneg : ¬ (0 : ℤ) ≤ Int.negSucc n := by omega
      have hneg :=
        norm_dfiEquation27CentralSeries_swappedLowerBoundaryHeightIntegrated_le
          h65 j hT hc hc4 hc1 hu hh hk ha hb hm
      simpa [m, dfiSignedCentralSeries,
        hughesYoungEndpointSignedShiftMajorant, hnonneg] using hneg

/-- The literal finite signed-shift lower-boundary source after the
physical-height integral has been evaluated. -/
noncomputable def hughesYoungFiniteLowerBoundaryHeightIntegratedCentral
    (T c u : ℝ) (h k a b K : ℕ) : ℂ :=
  let B := hughesYoungFullDyadicBound (K + 1)
  ∑ r ∈ hughesYoungShiftInterval a b B B,
    if r = 0 then 0 else
      dfiSignedCentralSeries a b r
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)

/-- The same finite signed lower-boundary source before the physical-height
integral.  It uses exactly the common shift window of the finite
Hughes--Young equation-(83) source. -/
noncomputable def hughesYoungFiniteLowerBoundarySignedCentralAtHeight
    (T t c u : ℝ) (h k a b K : ℕ) : ℂ :=
  let B := hughesYoungFullDyadicBound (K + 1)
  ∑ r ∈ hughesYoungShiftInterval a b B B,
    if r = 0 then 0 else
      dfiSignedCentralSeries a b r
        (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k)

/-- The upper endpoint of the finite signed source, retained as the exact
remainder after the already isolated lower endpoint is removed from the
full endpoint discrepancy.  The preceding multiplier theorem identifies
the underlying pointwise Mellin cutoff; this definition keeps the signed
shift cancellation intact until the terminal contour estimate is applied.
-/
noncomputable def hughesYoungFiniteTerminalSignedCentralAtHeight
    (T t c u : ℝ) (h k a b K : ℕ) : ℂ :=
  hughesYoungFiniteEndpointSignedCentralAtHeight T t c u h k a b K -
    hughesYoungFiniteLowerBoundarySignedCentralAtHeight
      T t c u h k a b K

/-- Exact two-endpoint decomposition of the finite signed central source at
fixed physical height and Mellin ordinate. -/
theorem hughesYoungFiniteEndpointSignedCentralAtHeight_eq_lower_add_terminal
    (T t c u : ℝ) (h k a b K : ℕ) :
    hughesYoungFiniteEndpointSignedCentralAtHeight T t c u h k a b K =
      hughesYoungFiniteLowerBoundarySignedCentralAtHeight
          T t c u h k a b K +
        hughesYoungFiniteTerminalSignedCentralAtHeight
          T t c u h k a b K := by
  unfold hughesYoungFiniteTerminalSignedCentralAtHeight
  ring

/-- The finite lower-boundary signed source is integrable in the physical
height.  The proof consumes the branch-correct `L¹` theorem for every
nonzero shift before using finite additivity. -/
theorem integrable_heightWeight_mul_hughesYoungFiniteLowerBoundarySignedCentralAtHeight
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hc4 : c ≤ 1 / 4) (u : ℝ)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungFiniteLowerBoundarySignedCentralAtHeight
        T t c u h k a b K) := by
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  have hsum : Integrable (fun t : ℝ =>
      ∑ r ∈ S, if r = 0 then 0 else
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungLowerBoundaryReducedMellinCorrection
              T t c u h k)) := by
    apply integrable_finsetSum S
    intro r _hrmem
    by_cases hr0 : r = 0
    · simp [hr0]
    · simp only [hr0, if_false]
      exact integrable_heightWeight_mul_dfiSignedCentralSeries_lowerBoundary
        hT hc hc4 u hh hk ha hb hr0
  apply hsum.congr
  filter_upwards with t
  unfold hughesYoungFiniteLowerBoundarySignedCentralAtHeight
  simp only [B, S, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hrmem
  by_cases hr0 : r = 0 <;> simp [hr0]

/-- Exact finite-shift Fubini identity for the lower dyadic endpoint.  The
left side is the source after evaluating the physical integral in each DFI
series; the right side is the literal finite signed correction appearing
before that integral. -/
theorem hughesYoungFiniteLowerBoundaryHeightIntegratedCentral_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hc4 : c ≤ 1 / 4) (u : ℝ)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    hughesYoungFiniteLowerBoundaryHeightIntegratedCentral
        T c u h k a b K =
      ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteLowerBoundarySignedCentralAtHeight
          T t c u h k a b K := by
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  let F : ℤ → ℝ → ℂ := fun r t =>
    if r = 0 then 0 else
      (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k)
  have hInt : ∀ r ∈ S, Integrable (F r) := by
    intro r _hrmem
    by_cases hr0 : r = 0
    · simp [F, hr0]
    · simp only [F, hr0, if_false]
      exact integrable_heightWeight_mul_dfiSignedCentralSeries_lowerBoundary
        hT hc hc4 u hh hk ha hb hr0
  unfold hughesYoungFiniteLowerBoundaryHeightIntegratedCentral
  change (∑ r ∈ S, if r = 0 then 0 else
      dfiSignedCentralSeries a b r
        (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) = _
  calc
    (∑ r ∈ S, if r = 0 then 0 else
        dfiSignedCentralSeries a b r
          (hughesYoungLowerBoundaryHeightIntegratedWeight T c u h k)) =
        ∑ r ∈ S, ∫ t : ℝ, F r t := by
      apply Finset.sum_congr rfl
      intro r _hrmem
      by_cases hr0 : r = 0
      · simp [F, hr0]
      · simp only [F, hr0, if_false]
        exact dfiSignedCentralSeries_lowerBoundaryHeightIntegrated_eq_heightIntegral
          hT hc hc4 u hh hk ha hb hr0
    _ = ∫ t : ℝ, ∑ r ∈ S, F r t := by
      exact (MeasureTheory.integral_finsetSum S hInt).symm
    _ = ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteLowerBoundarySignedCentralAtHeight
          T t c u h k a b K := by
      apply integral_congr_ae
      filter_upwards with t
      unfold F hughesYoungFiniteLowerBoundarySignedCentralAtHeight
      simp only [B, S, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hrmem
      by_cases hr0 : r = 0 <;> simp [hr0]

/-- Finite additivity converts the signed one-shift endpoint theorem into
a bound for the exact Hughes--Young shift window. -/
theorem norm_hughesYoungFiniteLowerBoundaryHeightIntegratedCentral_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T c u : ℝ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hc1 : c ≤ 1) (hu : |u| ≤ T / 8)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    ‖hughesYoungFiniteLowerBoundaryHeightIntegratedCentral
        T c u h k a b K‖ ≤
      ∑ r ∈ hughesYoungShiftInterval a b
          (hughesYoungFullDyadicBound (K + 1))
          (hughesYoungFullDyadicBound (K + 1)),
        if r = 0 then 0 else
          hughesYoungEndpointSignedShiftMajorant
            Cγ Cw j T c u h k a b r := by
  unfold hughesYoungFiniteLowerBoundaryHeightIntegratedCentral
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r hrmem
  by_cases hr0 : r = 0
  · simp [hr0]
  · simp only [hr0, if_false]
    exact norm_dfiSignedCentralSeries_lowerBoundaryHeightIntegrated_le
      h65 j hT hc hc4 hc1 hu hh hk ha hb hr0

/-- At the native reduced coordinates, the exact finite lower endpoint is
bounded by one equation-(65) factor times the already assembled arithmetic
shift mass. -/
theorem norm_hughesYoungFiniteLowerBoundaryHeightIntegratedCentral_native_le
    {Cγ : ℝ} {Cw : ℕ → ℝ}
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) {T u : ℝ}
    (hT : 16 ≤ T) (hu : |u| ≤ T / 8)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (K : ℕ)
    (hc4 : hughesYoungSmallContour T ≤ 1 / 4) :
    ‖hughesYoungFiniteLowerBoundaryHeightIntegratedCentral T
        (hughesYoungSmallContour T) u h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K‖ ≤
      hughesYoungEndpointEquation65Majorant Cγ Cw j T
          (hughesYoungSmallContour T) u *
        ((2312 + 9 * (hughesYoungSmallContour T)⁻¹ ^ 3) / 4) *
        hughesYoungFiniteSmallContourShiftMass T h k K := by
  have hTexp : Real.exp 1 ≤ T := by
    linarith [Real.exp_one_lt_three]
  have hc := hughesYoungSmallContour_spec hTexp
  have hraw := norm_hughesYoungFiniteLowerBoundaryHeightIntegratedCentral_le
    (a := hughesYoungReducedLeft h k)
      (b := hughesYoungReducedRight h k)
      h65 j hT hc.1 hc4 hc.2.1 hu hh hk
      (hughesYoungReducedLeft_pos (k := k) hh)
      (hughesYoungReducedRight_pos hh hk) K
  rw [sum_hughesYoungEndpointSignedShiftMajorant_eq Cγ Cw j T u hh hk K]
    at hraw
  exact hraw

/-- The lower endpoint after the native finite Mellin-ordinate integral.
The physical-height integral has already been evaluated inside the DFI
series, so equation (65) supplies its full Fourier saving. -/
noncomputable def hughesYoungFiniteLowerBoundaryContourIntegral
    (T : ℝ) (h k K : ℕ) : ℂ :=
  ∫ u in -(T / 8)..T / 8,
    hughesYoungFiniteLowerBoundaryHeightIntegratedCentral T
      (hughesYoungSmallContour T) u h k
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K

/-- Uniform equation-(65) bound for one mollifier pair after the native
Mellin-ordinate integration. -/
theorem exists_norm_hughesYoungFiniteLowerBoundaryContourIntegral_le
    {Cγ : ℝ} (hCγ : 0 < Cγ) {Cw : ℕ → ℝ}
    (hCw : ∀ i, 0 < Cw i)
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) :
    ∃ L : ℝ, 0 < L ∧ ∀ {T : ℝ} {h k K : ℕ},
      16 ≤ T → 4 * Cγ * hughesYoungSmallContour T ≤ 1 →
      hughesYoungSmallContour T ≤ 1 / 4 →
      0 < h → 0 < k →
      ‖hughesYoungFiniteLowerBoundaryContourIntegral T h k K‖ ≤
        ((2 : ℝ) ^ j *
          ((2312 + 9 * (hughesYoungSmallContour T)⁻¹ ^ 3) / 4) *
          hughesYoungFiniteSmallContourShiftMass T h k K) *
        (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ *
          Real.exp 100 * (6 * T) *
          hughesYoungHeightInputDerivativeConstant Cw j *
          ((T / 16)⁻¹) ^ j) * L) := by
  obtain ⟨L, hL, hEq65⟩ :=
    exists_intervalIntegral_hughesYoungEquation65Bound_le hCγ hCw j
  refine ⟨L, hL, ?_⟩
  intro T h k K hT hsmall hc4 hh hk
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hTexp : Real.exp 1 ≤ T := by
    linarith [Real.exp_one_lt_three]
  have hc := hughesYoungSmallContour_spec hTexp
  let A : ℝ := (2 : ℝ) ^ j *
    ((2312 + 9 * (hughesYoungSmallContour T)⁻¹ ^ 3) / 4) *
    hughesYoungFiniteSmallContourShiftMass T h k K
  let g : ℝ → ℝ := fun u =>
    A * hughesYoungEquation65Bound Cγ Cw j T
      (hughesYoungSmallContour T) u
  have hA : 0 ≤ A := by
    dsimp only [A]
    have hbeta :
        0 ≤ (2312 + 9 * (hughesYoungSmallContour T)⁻¹ ^ 3) / 4 := by
      exact div_nonneg
        (add_nonneg (by norm_num)
          (mul_nonneg (by norm_num)
            (pow_nonneg (inv_nonneg.mpr hc.1.le) 3)))
        (by norm_num)
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (by norm_num) j) hbeta)
      (hughesYoungFiniteSmallContourShiftMass_nonneg T h k K)
  have hg : IntervalIntegrable g volume (-(T / 8)) (T / 8) := by
    apply IntervalIntegrable.const_mul
    exact (continuous_hughesYoungEquation65Bound Cγ Cw j hT0.le
      (hughesYoungSmallContour T)).intervalIntegrable _ _
  have hpoint : ∀ᵐ u : ℝ ∂volume,
      u ∈ Set.Ioc (-(T / 8)) (T / 8) →
        ‖hughesYoungFiniteLowerBoundaryHeightIntegratedCentral T
          (hughesYoungSmallContour T) u h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K‖ ≤
            g u := by
    filter_upwards with u
    intro huMem
    have hu : |u| ≤ T / 8 := by
      rw [abs_le]
      exact ⟨huMem.1.le, huMem.2⟩
    have hbound :=
      norm_hughesYoungFiniteLowerBoundaryHeightIntegratedCentral_native_le
        h65 j hT hu hh hk K hc4
    rw [hughesYoungEndpointEquation65Majorant_eq] at hbound
    calc
      _ ≤ 2 ^ j * hughesYoungEquation65Bound Cγ Cw j T
          (hughesYoungSmallContour T) u *
          ((2312 + 9 * (hughesYoungSmallContour T)⁻¹ ^ 3) / 4) *
          hughesYoungFiniteSmallContourShiftMass T h k K := hbound
      _ = g u := by dsimp only [A, g]; ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (show -(T / 8) ≤ T / 8 by linarith) hpoint hg
  have hEq := hEq65 hT1 hc.1 hc.2.1 hsmall (by positivity : 0 ≤ T / 8)
  unfold hughesYoungFiniteLowerBoundaryContourIntegral
  calc
    ‖∫ u in -(T / 8)..T / 8,
        hughesYoungFiniteLowerBoundaryHeightIntegratedCentral T
          (hughesYoungSmallContour T) u h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K‖ ≤
        ∫ u in -(T / 8)..T / 8, g u := hnorm
    _ = A * ∫ u in -(T / 8)..T / 8,
        hughesYoungEquation65Bound Cγ Cw j T
          (hughesYoungSmallContour T) u := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ A * (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ *
          Real.exp 100 * (6 * T) *
          hughesYoungHeightInputDerivativeConstant Cw j *
          ((T / 16)⁻¹) ^ j) * L) :=
      mul_le_mul_of_nonneg_left hEq hA
    _ = _ := rfl

/-- The complete lower-endpoint family after summing the actual mollifier
indices.  This is still the source-faithful endpoint object; no asymptotic
claim is built into the definition. -/
noncomputable def hughesYoungFiniteLowerBoundaryIntegratedCentral
    (T : ℝ) (K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungFiniteLowerBoundaryContourIntegral T h k K

/-- The complete upper-endpoint family after all native integrations and
mollifier sums.  It is defined as the exact residual endpoint so that the
large signed cancellation is preserved; no norm estimate is embedded in
the definition. -/
noncomputable def hughesYoungFiniteTerminalIntegratedCentral
    (T : ℝ) (K : ℕ) : ℂ :=
  hughesYoungFiniteEndpointIntegratedCentral T K -
    hughesYoungFiniteLowerBoundaryIntegratedCentral T K

/-- Exact global two-endpoint decomposition.  The lower term is controlled
by equation (65); the terminal term is the sole remaining contour-transfer
obligation for the finite equation-(83) source. -/
theorem hughesYoungFiniteEndpointIntegratedCentral_eq_lower_add_terminal
    (T : ℝ) (K : ℕ) :
    hughesYoungFiniteEndpointIntegratedCentral T K =
      hughesYoungFiniteLowerBoundaryIntegratedCentral T K +
        hughesYoungFiniteTerminalIntegratedCentral T K := by
  unfold hughesYoungFiniteTerminalIntegratedCentral
  ring

/-- The whole source omitted by the active product truncation is exactly
the finite-rectangle endpoint together with the inactive boxes inside that
rectangle.  This identity is the cancellation-preserving replacement for
estimating the terminal endpoint and inactive family separately. -/
theorem hughesYoungActiveComplementIntegratedCentral_eq_endpoint_add_inactive
    {T : ℝ} (hT : Real.exp 3 ≤ T) (R K : ℕ) :
    hughesYoungActiveComplementIntegratedCentral T R K =
      hughesYoungFiniteEndpointIntegratedCentral T K +
        hughesYoungInactiveIntegratedCompleteCentral T R K := by
  rw [hughesYoungActiveComplementIntegratedCentral_eq_pure_sub_active hT]
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 3)).trans hT
  rw [← hughesYoungActiveIntegratedCompleteCentral_eq_reassembledSource
    hT1]
  have hrectangle :=
    hughesYoungRectangularIntegratedCompleteCentral_eq_active_add_inactive
      T R K
  have hpure :=
    hughesYoungRectangularIntegratedCompleteCentral_eq_pure_sub_endpoint
      T K
  rw [hrectangle] at hpure
  linear_combination -hpure

/-- The unresolved native source is one already-controlled non-large DFI
difference minus the single cancellation-preserving active complement.  In
particular, the endpoint and inactive terms must be moved together. -/
theorem hughesYoungNativeComplementarySource_eq_nonLargeDifference_sub_activeComplement
    {T P : ℝ} (hT : Real.exp 3 ≤ T) (R K : ℕ) :
    hughesYoungNativeComplementarySource T P R K =
      hughesYoungActiveNonLargeDFIOffDiagonal T P R K -
        hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T P R K -
        hughesYoungActiveComplementIntegratedCentral T R K := by
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 3)).trans hT
  rw [hughesYoungNativeComplementarySource_eq_nonLargePair_add_activeSourceDiscrepancy
    hT1]
  rw [hughesYoungActiveSourceDiscrepancy_eq_neg_activeComplement hT]
  ring

/-! ## The lower-boundary-removed active complement

The contour move used before Hughes--Young equation (61) cannot be applied
to the lower endpoint, where one central variable approaches zero.  That
endpoint has already been bounded above by equation (65).  The remaining
complement is the complete nonnegative-index partition minus the active
finite family; it is the object that can be moved to the source line.
-/

/-- The exact complementary Mellin weight after removing the lower dyadic
endpoint. -/
noncomputable def hughesYoungNonLowerActiveComplementReducedMellinWeight
    (T t c u : ℝ) (h k a b R K : ℕ) (x y : ℝ) : ℂ :=
  hughesYoungLowerCompleteReducedMellinWeight T t c u h k x y -
    hughesYoungActiveReassembledReducedMellinWeight
      T t c u h k a b R K x y

/-- The active complement splits exactly into the separately controlled
lower endpoint and the source-line complement. -/
theorem hughesYoungActiveComplementReducedMellinWeight_eq_lower_add_nonLower
    (T t c u : ℝ) (h k a b R K : ℕ) (x y : ℝ) :
    hughesYoungActiveComplementReducedMellinWeight
        T t c u h k a b R K x y =
      hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k x y +
        hughesYoungNonLowerActiveComplementReducedMellinWeight
          T t c u h k a b R K x y := by
  unfold hughesYoungActiveComplementReducedMellinWeight
    hughesYoungLowerBoundaryReducedMellinCorrection
    hughesYoungNonLowerActiveComplementReducedMellinWeight
  ring

/-- The globally integrated complement after the already-controlled lower
endpoint has been removed.  This is an exact residual object, not an
estimate: the subsequent contour argument must identify it with the
integral of `hughesYoungNonLowerActiveComplementReducedMellinWeight` and
bound that integral on the source line. -/
noncomputable def hughesYoungNonLowerActiveComplementIntegratedCentral
    (T : ℝ) (R K : ℕ) : ℂ :=
  hughesYoungActiveComplementIntegratedCentral T R K -
    hughesYoungFiniteLowerBoundaryIntegratedCentral T K

/-- Exact lower/non-lower decomposition of the integrated active
complement. -/
theorem hughesYoungActiveComplementIntegratedCentral_eq_lower_add_nonLower
    (T : ℝ) (R K : ℕ) :
    hughesYoungActiveComplementIntegratedCentral T R K =
      hughesYoungFiniteLowerBoundaryIntegratedCentral T K +
        hughesYoungNonLowerActiveComplementIntegratedCentral T R K := by
  unfold hughesYoungNonLowerActiveComplementIntegratedCentral
  ring

/-- Algebraic identification of the non-lower complement with the terminal
finite-depth endpoint and the inactive dyadic central family.  This keeps
those two large-looking terms together until their common source-line
estimate is available. -/
theorem hughesYoungNonLowerActiveComplementIntegratedCentral_eq_terminal_add_inactive
    {T : ℝ} (hT : Real.exp 3 ≤ T) (R K : ℕ) :
    hughesYoungNonLowerActiveComplementIntegratedCentral T R K =
      hughesYoungFiniteTerminalIntegratedCentral T K +
        hughesYoungInactiveIntegratedCompleteCentral T R K := by
  unfold hughesYoungNonLowerActiveComplementIntegratedCentral
  rw [hughesYoungActiveComplementIntegratedCentral_eq_endpoint_add_inactive
    hT]
  unfold hughesYoungFiniteTerminalIntegratedCentral
  ring

/-- The real cutoff multiplier carried by the lower-boundary-removed
complement. -/
noncomputable def hughesYoungNonLowerActiveComplementMultiplier
    (a b R K : ℕ) (x y : ℝ) : ℝ :=
  (1 - hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) *
      (1 - hughesYoungDyadicStep (y * hughesYoungDyadicRatio)) -
    hughesYoungActiveContinuousDyadicWeight a b R K x y

/-- Exact positive-quadrant factorization of the non-lower complement.
The dependence on the Mellin variable remains entirely in the common
Hughes--Young monomial. -/
theorem hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_scaled
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b R K : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hughesYoungNonLowerActiveComplementReducedMellinWeight
        T t c u h k a b R K x y =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        (hughesYoungNonLowerActiveComplementMultiplier
          a b R K x y : ℂ) *
        (x : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (y : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) := by
  unfold hughesYoungNonLowerActiveComplementReducedMellinWeight
    hughesYoungLowerCompleteReducedMellinWeight
    hughesYoungNonLowerActiveComplementMultiplier
  rw [if_pos ⟨hx, hy⟩,
    hughesYoungActiveReassembledReducedMellinWeight_eq_scaled_powers
      T t c u hh hk a b R K hx hy]
  push_cast
  ring

/-- The source-line complement multiplier is nonnegative on the positive
quadrant.  This is the continuous, DFI-integral version of the omitted
dyadic subpartition. -/
theorem hughesYoungNonLowerActiveComplementMultiplier_nonneg
    (a b R K : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ hughesYoungNonLowerActiveComplementMultiplier a b R K x y := by
  unfold hughesYoungNonLowerActiveComplementMultiplier
  exact sub_nonneg.mpr
    (hughesYoungActiveContinuousDyadicWeight_le_lowerComplete
      a b R K hx hy)

/-- If both continuous variables lie below the terminal dyadic scale and
their product lies in the retained conductor range, the active boxes equal
the complete lower-cutoff partition exactly. -/
theorem hughesYoungActiveContinuousDyadicWeight_eq_lowerComplete_of_product_le
    {a b R K : ℕ} {x y : ℝ}
    (hx : 0 ≤ x) (_hy : 0 ≤ y)
    (hxUpper : x ≤ hughesYoungDyadicRatio ^ (K + 1))
    (hyUpper : y ≤ hughesYoungDyadicRatio ^ (K + 1))
    (hxy : x * y ≤ ((a * b * R : ℕ) : ℝ)) :
    hughesYoungActiveContinuousDyadicWeight a b R K x y =
      (1 - hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) *
        (1 - hughesYoungDyadicStep (y * hughesYoungDyadicRatio)) := by
  classical
  let S := (Finset.range (K + 2)).product (Finset.range (K + 2))
  let F : ℕ × ℕ → ℝ := fun ij =>
    hughesYoungFullDyadicCutoff ij.1 x *
      hughesYoungFullDyadicCutoff ij.2 y
  have hsubset : hughesYoungActiveDyadicBoxes a b R K ⊆ S := by
    intro ij hij
    exact (Finset.mem_filter.mp hij).1
  have houtside : ∀ ij ∈ S, ij ∉ hughesYoungActiveDyadicBoxes a b R K →
      F ij = 0 := by
    intro ij hijS hijActive
    have hnotScale : ¬ (hughesYoungFullDyadicScale ij.1 *
        hughesYoungFullDyadicScale ij.2 ≤ ((a * b * R : ℕ) : ℝ)) := by
      intro hscale
      apply hijActive
      exact Finset.mem_filter.mpr ⟨hijS, hscale⟩
    by_cases hcutX : hughesYoungFullDyadicCutoff ij.1 x = 0
    · dsimp only [F]
      rw [hcutX, zero_mul]
    · by_cases hcutY : hughesYoungFullDyadicCutoff ij.2 y = 0
      · dsimp only [F]
        rw [hcutY, mul_zero]
      · have hsuppX := support_hughesYoungDyadicCutoffAt_subset
          (hughesYoungFullDyadicScale_pos ij.1) hcutX
        have hsuppY := support_hughesYoungDyadicCutoffAt_subset
          (hughesYoungFullDyadicScale_pos ij.2) hcutY
        exact (hnotScale ((mul_le_mul hsuppX.1 hsuppY.1
          (hughesYoungFullDyadicScale_pos ij.2).le hx).trans hxy)).elim
  have hsum : (∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K, F ij) =
      ∑ ij ∈ S, F ij := by
    rw [Finset.sum_subset hsubset houtside]
  have hfull : (∑ ij ∈ S, F ij) =
      (1 - hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) *
        (1 - hughesYoungDyadicStep (y * hughesYoungDyadicRatio)) := by
    dsimp only [S, F]
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    rw [sum_range_hughesYoungFullDyadicCutoff_eq K x,
      sum_range_hughesYoungFullDyadicCutoff_eq K y]
    have hpow : 0 < hughesYoungDyadicRatio ^ (K + 1) :=
      pow_pos hughesYoungDyadicRatio_pos _
    rw [hughesYoungDyadicStep_eq_one ((div_le_one hpow).2 hxUpper),
      hughesYoungDyadicStep_eq_one ((div_le_one hpow).2 hyUpper)]
  unfold hughesYoungActiveContinuousDyadicWeight
  exact hsum.trans hfull

/-- Hence the lower-boundary-removed complement vanishes exactly in the
retained product range whenever the two variables lie in the represented
finite rectangle. -/
theorem hughesYoungNonLowerActiveComplementMultiplier_eq_zero_of_product_le
    {a b R K : ℕ} {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxUpper : x ≤ hughesYoungDyadicRatio ^ (K + 1))
    (hyUpper : y ≤ hughesYoungDyadicRatio ^ (K + 1))
    (hxy : x * y ≤ ((a * b * R : ℕ) : ℝ)) :
    hughesYoungNonLowerActiveComplementMultiplier a b R K x y = 0 := by
  unfold hughesYoungNonLowerActiveComplementMultiplier
  rw [hughesYoungActiveContinuousDyadicWeight_eq_lowerComplete_of_product_le
    hx hy hxUpper hyUpper hxy]
  ring

/-- A one-extra-dyadic-step cover removes the artificial separate upper
bounds on the two continuous source variables.  Nonvanishing of the
lower-complete partition forces both variables above `1 / sqrt 2`; hence a
bound on their product bounds each variable by one further dyadic step. -/
theorem hughesYoungNonLowerActiveComplementMultiplier_eq_zero_of_product_le_of_strongCover
    {a b R K : ℕ} {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (hxy : x * y ≤ ((a * b * R : ℕ) : ℝ)) :
    hughesYoungNonLowerActiveComplementMultiplier a b R K x y = 0 := by
  let L : ℝ :=
    (1 - hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) *
      (1 - hughesYoungDyadicStep (y * hughesYoungDyadicRatio))
  have hactive0 : 0 ≤ hughesYoungActiveContinuousDyadicWeight a b R K x y :=
    hughesYoungActiveContinuousDyadicWeight_nonneg a b R K hx hy
  have hactiveLe : hughesYoungActiveContinuousDyadicWeight a b R K x y ≤ L := by
    dsimp only [L]
    exact hughesYoungActiveContinuousDyadicWeight_le_lowerComplete
      a b R K hx hy
  by_cases hL : L = 0
  · have hactive : hughesYoungActiveContinuousDyadicWeight a b R K x y = 0 :=
      le_antisymm (hactiveLe.trans_eq hL) hactive0
    unfold hughesYoungNonLowerActiveComplementMultiplier
    change L - hughesYoungActiveContinuousDyadicWeight a b R K x y = 0
    rw [hL, hactive]
    norm_num
  · have hxFactor : 1 - hughesYoungDyadicStep
        (x * hughesYoungDyadicRatio) ≠ 0 := by
      intro hz
      apply hL
      dsimp only [L]
      rw [hz, zero_mul]
    have hyFactor : 1 - hughesYoungDyadicStep
        (y * hughesYoungDyadicRatio) ≠ 0 := by
      intro hz
      apply hL
      dsimp only [L]
      rw [hz, mul_zero]
    have hxLower : 1 / hughesYoungDyadicRatio < x := by
      by_contra hnot
      have hxStep : hughesYoungDyadicStep
          (x * hughesYoungDyadicRatio) = 1 := by
        apply hughesYoungDyadicStep_eq_one
        have hρ := hughesYoungDyadicRatio_pos
        have := le_of_not_gt hnot
        calc
          x * hughesYoungDyadicRatio ≤
              (1 / hughesYoungDyadicRatio) * hughesYoungDyadicRatio :=
            mul_le_mul_of_nonneg_right this hρ.le
          _ = 1 := by field_simp
      exact hxFactor (by rw [hxStep]; ring)
    have hyLower : 1 / hughesYoungDyadicRatio < y := by
      by_contra hnot
      have hyStep : hughesYoungDyadicStep
          (y * hughesYoungDyadicRatio) = 1 := by
        apply hughesYoungDyadicStep_eq_one
        have hρ := hughesYoungDyadicRatio_pos
        have := le_of_not_gt hnot
        calc
          y * hughesYoungDyadicRatio ≤
              (1 / hughesYoungDyadicRatio) * hughesYoungDyadicRatio :=
            mul_le_mul_of_nonneg_right this hρ.le
          _ = 1 := by field_simp
      exact hyFactor (by rw [hyStep]; ring)
    have hxOne : 1 ≤ y * hughesYoungDyadicRatio := by
      have hρ := hughesYoungDyadicRatio_pos
      calc
        1 = (1 / hughesYoungDyadicRatio) * hughesYoungDyadicRatio := by
          field_simp
        _ ≤ y * hughesYoungDyadicRatio :=
          mul_le_mul_of_nonneg_right hyLower.le hρ.le
    have hyOne : 1 ≤ x * hughesYoungDyadicRatio := by
      have hρ := hughesYoungDyadicRatio_pos
      calc
        1 = (1 / hughesYoungDyadicRatio) * hughesYoungDyadicRatio := by
          field_simp
        _ ≤ x * hughesYoungDyadicRatio :=
          mul_le_mul_of_nonneg_right hxLower.le hρ.le
    have hxUpper : x ≤ hughesYoungDyadicRatio ^ (K + 1) := by
      calc
        x = x * 1 := by ring
        _ ≤ x * (y * hughesYoungDyadicRatio) :=
          mul_le_mul_of_nonneg_left hxOne hx
        _ = hughesYoungDyadicRatio * (x * y) := by ring
        _ ≤ hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hxy hughesYoungDyadicRatio_pos.le
        _ ≤ hughesYoungDyadicRatio ^ (K + 1) := hstrong
    have hyUpper : y ≤ hughesYoungDyadicRatio ^ (K + 1) := by
      calc
        y = y * 1 := by ring
        _ ≤ y * (x * hughesYoungDyadicRatio) :=
          mul_le_mul_of_nonneg_left hyOne hy
        _ = hughesYoungDyadicRatio * (x * y) := by ring
        _ ≤ hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hxy hughesYoungDyadicRatio_pos.le
        _ ≤ hughesYoungDyadicRatio ^ (K + 1) := hstrong
    exact hughesYoungNonLowerActiveComplementMultiplier_eq_zero_of_product_le
      hx hy hxUpper hyUpper hxy

/-- On the positive source quadrant, the active complementary Mellin
weight vanishes identically throughout the retained conductor product
range.  Thus the non-lower-boundary part of this weight is a genuine AFE
tail, rather than an independently estimated central main term. -/
theorem hughesYoungActiveComplementReducedMellinWeight_eq_zero_of_product_le
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b R K : ℕ) {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxy : x * y ≤ ((a * b * R : ℕ) : ℝ))
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1)) :
    hughesYoungActiveComplementReducedMellinWeight
        T t c u h k a b R K x y = 0 := by
  rw [hughesYoungActiveComplementReducedMellinWeight_eq_scaled_one_sub
    T t c u hh hk a b R K (by linarith) (by linarith)]
  rw [hughesYoungActiveContinuousDyadicWeight_eq_one hx hy hxy hcover]
  norm_num

/-- Contrapositive support form of the preceding exact vanishing theorem.
It is the source support statement used when the equation-(83) contour is
moved back to the Hughes--Young opening line. -/
theorem hughesYoungActiveComplementReducedMellinWeight_support
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b R K : ℕ) {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (hne : hughesYoungActiveComplementReducedMellinWeight
      T t c u h k a b R K x y ≠ 0) :
    ((a * b * R : ℕ) : ℝ) < x * y := by
  by_contra hnot
  exact hne
    (hughesYoungActiveComplementReducedMellinWeight_eq_zero_of_product_le
      T t c u hh hk a b R K hx hy (le_of_not_gt hnot) hcover)

/-- Equation (65) and the exact finite-shift normalization bound the whole
lower endpoint by the previously estimated total arithmetic shift mass. -/
theorem exists_norm_hughesYoungFiniteLowerBoundaryIntegratedCentral_le
    {Cγ : ℝ} (hCγ : 0 < Cγ) {Cw : ℕ → ℝ}
    (hCw : ∀ i, 0 < Cw i)
    (h65 : ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 4 *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
    (j : ℕ) :
    ∃ L : ℝ, 0 < L ∧ ∀ {T : ℝ} {K : ℕ},
      16 ≤ T → 4 * Cγ * hughesYoungSmallContour T ≤ 1 →
      hughesYoungSmallContour T ≤ 1 / 4 →
      ‖hughesYoungFiniteLowerBoundaryIntegratedCentral T K‖ ≤
        ((2 : ℝ) ^ j *
          ((2312 + 9 * (hughesYoungSmallContour T)⁻¹ ^ 3) / 4) *
          (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ *
            Real.exp 100 * (6 * T) *
            hughesYoungHeightInputDerivativeConstant Cw j *
            ((T / 16)⁻¹) ^ j) * L)) *
          (∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
              hughesYoungFiniteSmallContourShiftMass T h k K) := by
  obtain ⟨L, hL, hpair⟩ :=
    exists_norm_hughesYoungFiniteLowerBoundaryContourIntegral_le
      hCγ hCw h65 j
  refine ⟨L, hL, ?_⟩
  intro T K hT hsmall hc4
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let A : ℝ := (2 : ℝ) ^ j *
    ((2312 + 9 * (hughesYoungSmallContour T)⁻¹ ^ 3) / 4) *
    (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ *
      Real.exp 100 * (6 * T) *
      hughesYoungHeightInputDerivativeConstant Cw j *
      ((T / 16)⁻¹) ^ j) * L)
  have hsum :
      ∑ h ∈ S, ∑ k ∈ S,
          ‖hughesYoungFiniteLowerBoundaryContourIntegral T h k K‖ ≤
        ∑ h ∈ S, ∑ k ∈ S,
          A * hughesYoungFiniteSmallContourShiftMass T h k K := by
    apply Finset.sum_le_sum
    intro h hhmem
    apply Finset.sum_le_sum
    intro k hkmem
    have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
    have hp := hpair (K := K) hT hsmall hc4 hh hk
    calc
      ‖hughesYoungFiniteLowerBoundaryContourIntegral T h k K‖ ≤
          ((2 : ℝ) ^ j *
            ((2312 + 9 * (hughesYoungSmallContour T)⁻¹ ^ 3) / 4) *
            hughesYoungFiniteSmallContourShiftMass T h k K) *
          (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ *
            Real.exp 100 * (6 * T) *
            hughesYoungHeightInputDerivativeConstant Cw j *
            ((T / 16)⁻¹) ^ j) * L) := hp
      _ = A * hughesYoungFiniteSmallContourShiftMass T h k K := by
        dsimp only [A]
        ring
  unfold hughesYoungFiniteLowerBoundaryIntegratedCentral
  calc
    ‖∑ h ∈ S, ∑ k ∈ S,
        hughesYoungFiniteLowerBoundaryContourIntegral T h k K‖ ≤
      ∑ h ∈ S, ‖∑ k ∈ S,
        hughesYoungFiniteLowerBoundaryContourIntegral T h k K‖ :=
      norm_sum_le _ _
    _ ≤ ∑ h ∈ S, ∑ k ∈ S,
        ‖hughesYoungFiniteLowerBoundaryContourIntegral T h k K‖ := by
      apply Finset.sum_le_sum
      intro h _hhmem
      exact norm_sum_le _ _
    _ ≤ ∑ h ∈ S, ∑ k ∈ S,
        A * hughesYoungFiniteSmallContourShiftMass T h k K := hsum
    _ = ∑ h ∈ S, A * (∑ k ∈ S,
        hughesYoungFiniteSmallContourShiftMass T h k K) := by
      apply Finset.sum_congr rfl
      intro h _hhmem
      rw [Finset.mul_sum]
    _ = A * (∑ h ∈ S, ∑ k ∈ S,
        hughesYoungFiniteSmallContourShiftMass T h k K) := by
      rw [Finset.mul_sum]
    _ = A * (∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          hughesYoungFiniteSmallContourShiftMass T h k K) := by rfl
    _ = _ := rfl

set_option maxRecDepth 20000 in
/-- The exact lower dyadic endpoint is negligible on the native
Hughes--Young fourth-moment scale.  A fixed high Fourier derivative order
retains enough of equation (65) to absorb the deliberately coarse terminal
arithmetic cutoff. -/
theorem hughesYoungFiniteLowerBoundaryIntegratedCentral_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungFiniteLowerBoundaryIntegratedCentral T
        (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  obtain ⟨Cγ, hCγ, Cw, hCw, h65⟩ := hughesYoung_equation65
  obtain ⟨L, hL, hendpoint⟩ :=
    exists_norm_hughesYoungFiniteLowerBoundaryIntegratedCentral_le
      hCγ hCw h65 600
  let M : ℝ :=
    12 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
      hughesYoungEquation84LogProfileMass * 9 ^ (11 : ℕ) * 7 ^ (5 : ℕ)
  let C : ℝ :=
    (2 : ℝ) ^ (600 : ℕ) * (2321 / 4) *
      ((15 / 4) * Real.exp 100 * 6 *
        hughesYoungHeightInputDerivativeConstant Cw 600 *
        (16 : ℝ) ^ (600 : ℕ) * L) * M
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (pow_nonneg (by positivity) 2))
          hughesYoungEquation84LogProfileMass_pos.le)
        (pow_nonneg (by norm_num) 11))
      (pow_nonneg (by norm_num) 5)
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hderiv :=
      (hughesYoungHeightInputDerivativeConstant_pos hCw 600).le
    have hInner : 0 ≤
        (15 / 4 : ℝ) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant Cw 600 *
          (16 : ℝ) ^ (600 : ℕ) * L := by
      positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg (by norm_num) 600) (by norm_num)) hInner)
      hM
  intro ε hε
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop
      (max (Real.exp (max 4 (4 * Cγ))) 16)] with T hTlarge
  have hT16 : 16 ≤ T := le_trans (le_max_right _ _) hTlarge
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hExp4 : Real.exp 4 ≤ T :=
    (le_trans (Real.exp_le_exp.mpr (le_max_left 4 (4 * Cγ)))
      (le_max_left _ 16)).trans hTlarge
  have hExpC : Real.exp (4 * Cγ) ≤ T :=
    (le_trans (Real.exp_le_exp.mpr (le_max_right 4 (4 * Cγ)))
      (le_max_left _ 16)).trans hTlarge
  have hlog4 : 4 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 4) hExp4
  have hlogC : 4 * Cγ ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos (4 * Cγ)) hExpC
  have hc := hughesYoungSmallContour_spec
    ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hExp4)
  have hc4 : hughesYoungSmallContour T ≤ 1 / 4 := by
    unfold hughesYoungSmallContour
    exact inv_le_of_inv_le₀ (by norm_num) (by simpa using hlog4)
  have hsmall : 4 * Cγ * hughesYoungSmallContour T ≤ 1 := by
    unfold hughesYoungSmallContour
    rw [← div_eq_mul_inv]
    exact (div_le_one (by linarith : 0 < Real.log T)).2 hlogC
  have hraw := hendpoint (K := hughesYoungGlobalDepth T) hT16 hsmall hc4
  have hmass :=
    hughesYoungTerminalSmallContourTotalMass_le_pow_fiveHundredTwentyTwo hExp4
  have hlog : Real.log T ≤ T := Real.log_le_self hT0.le
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog3 : (Real.log T) ^ (3 : ℕ) ≤ T ^ (3 : ℕ) :=
    pow_le_pow_left₀ hlog0 hlog 3
  have hT3 : 1 ≤ T ^ (3 : ℕ) := one_le_pow₀ hT1
  have hbeta :
      (2312 + 9 * (hughesYoungSmallContour T)⁻¹ ^ 3) / 4 ≤
        (2321 / 4) * T ^ (3 : ℕ) := by
    rw [hc.2.2]
    nlinarith
  have hinv : (T / 16)⁻¹ = 16 / T := by
    field_simp
  have hmassEq :
      (∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          hughesYoungFiniteSmallContourShiftMass T h k
            (hughesYoungGlobalDepth T)) =
        hughesYoungTerminalSmallContourTotalMass T := by rfl
  rw [hc.2.2, hmassEq, hinv] at hraw
  have hmass0 : 0 ≤ hughesYoungTerminalSmallContourTotalMass T := by
    unfold hughesYoungTerminalSmallContourTotalMass
    apply Finset.sum_nonneg
    intro h _hhmem
    apply Finset.sum_nonneg
    intro k _hkmem
    exact hughesYoungFiniteSmallContourShiftMass_nonneg T h k
      (hughesYoungGlobalDepth T)
  have hderiv0 :
      0 ≤ hughesYoungHeightInputDerivativeConstant Cw 600 :=
    (hughesYoungHeightInputDerivativeConstant_pos hCw 600).le
  have hbetaLog :
      (2312 + 9 * Real.log T ^ 3) / 4 ≤
        (2321 / 4) * T ^ (3 : ℕ) := by
    simpa only [hc.2.2] using hbeta
  have hnew0 : 0 ≤
      2 ^ (600 : ℕ) * ((2321 / 4) * T ^ (3 : ℕ)) *
        ((15 * T / 4 * T * Real.exp 100 * (6 * T) *
          hughesYoungHeightInputDerivativeConstant Cw 600 *
          (16 / T) ^ (600 : ℕ)) * L) := by
    positivity
  have hbound :
      ‖hughesYoungFiniteLowerBoundaryIntegratedCentral T
          (hughesYoungGlobalDepth T)‖ ≤
        C * (T ^ (528 : ℕ) / T ^ (600 : ℕ)) := by
    calc
      _ ≤
          (2 ^ (600 : ℕ) *
            ((2312 + 9 * Real.log T ^ 3) / 4) *
            ((15 * T / 4 * Real.log T * Real.exp 100 * (6 * T) *
              hughesYoungHeightInputDerivativeConstant Cw 600 *
              (16 / T) ^ (600 : ℕ)) * L)) *
            hughesYoungTerminalSmallContourTotalMass T := hraw
      _ ≤
          (2 ^ (600 : ℕ) * ((2321 / 4) * T ^ (3 : ℕ)) *
            ((15 * T / 4 * T * Real.exp 100 * (6 * T) *
              hughesYoungHeightInputDerivativeConstant Cw 600 *
              (16 / T) ^ (600 : ℕ)) * L)) *
            (M * T ^ (522 : ℕ)) := by
        gcongr
      _ = C * (T ^ (528 : ℕ) / T ^ (600 : ℕ)) := by
        rw [div_pow]
        dsimp only [C]
        field_simp [hT0.ne']
  have hpow : T ^ (528 : ℕ) ≤ T ^ (600 : ℕ) :=
    pow_le_pow_right₀ hT1 (by norm_num)
  have hratio : T ^ (528 : ℕ) / T ^ (600 : ℕ) ≤ T := by
    calc
      _ ≤ 1 := (div_le_one (pow_pos hT0 600)).2 hpow
      _ ≤ T := hT1
  have hlinear :
      ‖hughesYoungFiniteLowerBoundaryIntegratedCentral T
          (hughesYoungGlobalDepth T)‖ ≤ C * T :=
    hbound.trans (mul_le_mul_of_nonneg_left hratio hC)
  have hpowEps : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungFiniteLowerBoundaryIntegratedCentral T
        (hughesYoungGlobalDepth T)))]
  calc
    ‖hughesYoungFiniteLowerBoundaryIntegratedCentral T
        (hughesYoungGlobalDepth T)‖ ≤ C * T := hlinear
    _ ≤ C * (T ^ ε * T) := by
      apply mul_le_mul_of_nonneg_left _ hC
      calc
        T = 1 * T := by ring
        _ ≤ T ^ ε * T := mul_le_mul_of_nonneg_right hpowEps hT0.le
    _ = C * ‖T ^ ε * |T|‖ := by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hT0.le ε) (abs_nonneg T)),
        abs_of_pos hT0]

end RiemannZeta.GuthMaynard
