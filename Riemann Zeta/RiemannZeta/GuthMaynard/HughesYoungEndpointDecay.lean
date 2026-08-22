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
      ‖((b : ℂ) * a)⁻¹‖ *
        ((b * a * r ^ 2 : ℕ) : ℝ) *
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
  let K : ℝ := ‖((b : ℂ) * a)⁻¹‖ *
    ((b * a * r ^ 2 : ℕ) : ℝ) * E *
    (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
      (r : ℝ) ^ (-2 * c) * (2312 + 9 * c⁻¹ ^ 3))
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
        dsimp only [K]
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
  let E : ℝ :=
    (2 : ℝ) ^ j *
      ((15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)))
  let K : ℝ := ‖((b : ℂ) * a)⁻¹‖ *
    ((b * a * r ^ 2 : ℕ) : ℝ) * E *
    (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
      (r : ℝ) ^ (-2 * c) * (2312 + 9 * c⁻¹ ^ 3))
  have hA0 : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget b a r)
  have hm : Summable (fun q : ℕ =>
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A hA0).mul_left K
  apply Summable.of_norm_bounded hm
  intro q
  simpa only [K, E, A] using
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
      ‖((b : ℂ) * a)⁻¹‖ *
        ((b * a * r ^ 2 : ℕ) : ℝ) *
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
        (hughesYoungEquation84LogBudget b a r ^ 2 *
          hughesYoungEquation84LogProfileMass) := by
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
  let K : ℝ := ‖((b : ℂ) * a)⁻¹‖ *
    ((b * a * r ^ 2 : ℕ) : ℝ) * E *
    (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
      (r : ℝ) ^ (-2 * c) * (2312 + 9 * c⁻¹ ^ 3))
  have hA1 : 1 ≤ A := one_le_hughesYoungEquation84LogBudget b a r
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hs :=
    summable_dfiEquation27CentralSummand_swappedLowerBoundaryHeightIntegrated
      h65 j hT hc hc4 hc1 hu hh hk ha hb hr
  have hm : Summable (fun q : ℕ =>
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A
      (zero_le_one.trans hA1)).mul_left K
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
      hs.norm.tsum_le_tsum
        (fun q => by simpa only [K, E, A] using
          norm_dfiEquation27CentralSummand_swappedLowerBoundaryHeightIntegrated_le
            h65 j hT hc hc4 hc1 hu hh hk ha hb hr q) hm
    _ = K * (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2) := by rw [tsum_mul_left]
    _ ≤ K * (A ^ 2 * hughesYoungEquation84LogProfileMass) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_natCast_inv_sq_mul_four_log_profile_sq_le hA1) hK0
    _ = _ := by
      dsimp only [K, E, A]
      ring

end RiemannZeta.GuthMaynard
