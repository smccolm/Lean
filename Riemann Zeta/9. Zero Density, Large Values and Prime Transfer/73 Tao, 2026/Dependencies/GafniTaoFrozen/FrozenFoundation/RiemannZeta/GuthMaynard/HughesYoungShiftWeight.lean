import RiemannZeta.GuthMaynard.HughesYoungCleaning

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The source-faithful fixed-shift Hughes--Young weight

Hughes--Young do not apply DFI to the unrestricted Fourier kernel
`log (y / x)`.  On the shifted surface `x - y = r` they replace it by
`-log (1 + r / y)` and use this formula as the off-surface extension of the
weight.  Its derivatives cost `T |r| / Y`, rather than `T`; this is the
mechanism behind the published parameter `P = (T / T₀) T^ε`.
-/

/-- Equation (70), before the remaining Mellin-ordinate integration, in the
unshifted project normalization. -/
noncomputable def hughesYoungCleanedShiftWeight
    (T c u X Y : ℝ) (h k : ℕ) (r : ℤ) (x y : ℝ) : ℂ :=
  (1 / (T : ℂ)) *
    hughesYoungLocalizedStaticWeight T c u X Y h k x y *
      hughesYoungHeightTransform T c u
        (-Real.log (1 + (r : ℝ) / y))

/-- On the actual quadratic-divisor surface, the source Fourier phase and
Hughes--Young's fixed-shift extension agree exactly. -/
theorem log_div_eq_neg_log_one_add_shift_div
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (r : ℤ)
    (hshift : x - y = (r : ℝ)) :
    Real.log (y / x) = -Real.log (1 + (r : ℝ) / y) := by
  have hratio : 1 + (r : ℝ) / y = x / y := by
    rw [← hshift]
    field_simp [hy.ne']
    ring
  rw [hratio, Real.log_div hy.ne' hx.ne', Real.log_div hx.ne' hy.ne']
  ring

theorem hughesYoungCleanedShiftWeight_eq_transform_source
    (T c u X Y : ℝ) {h k : ℕ} {r : ℤ} {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hshift : x - y = (r : ℝ)) :
    hughesYoungCleanedShiftWeight T c u X Y h k r x y =
      (1 / (T : ℂ)) *
        hughesYoungLocalizedStaticWeight T c u X Y h k x y *
          hughesYoungHeightTransform T c u (Real.log (y / x)) := by
  unfold hughesYoungCleanedShiftWeight
  rw [log_div_eq_neg_log_one_add_shift_div hx hy r hshift]

/-- The cleaned fixed-shift weight is exactly the height-integrated source
weight at every positive integral point selected by DFI. -/
theorem hughesYoungCleanedShiftWeight_eq_heightIntegral
    (T c u X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℤ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hshift : x - y = (r : ℝ)) :
    hughesYoungCleanedShiftWeight T c u X Y h k r x y =
      (1 / (T : ℂ)) *
        (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungLocalizedMellinWeight T t c u X Y h k x y) := by
  rw [hughesYoungCleanedShiftWeight_eq_transform_source
    T c u X Y hx hy hshift]
  rw [integral_heightWeight_mul_hughesYoungLocalizedMellinWeight_eq_transform
    T c u X Y hh hk hx hy]
  ring

/-- The height-free scalar multiplying the ordinary two-variable dyadic
Mellin kernel. -/
noncomputable def hughesYoungLocalizedStaticScalar
    (T : ℝ) (h k : ℕ) : ℂ :=
  shortMobiusSquareCoeff T h *
    hughesYoungLogPower (1 / 2 : ℂ) (h : ℝ) *
    shortMobiusSquareCoeff T k *
    hughesYoungLogPower (1 / 2 : ℂ) (k : ℝ) *
    (1 / (Real.pi : ℂ))

theorem hughesYoungLocalizedStaticWeight_eq_scalar_mul_kernel
    (T c u X Y : ℝ) (h k : ℕ) (x y : ℝ) :
    hughesYoungLocalizedStaticWeight T c u X Y h k x y =
      hughesYoungLocalizedStaticScalar T h k *
        hughesYoungLocalizedLogKernel X Y h k
          ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))
          ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) x y := by
  unfold hughesYoungLocalizedStaticWeight
    hughesYoungLocalizedStaticScalar hughesYoungLocalizedLogKernel
  dsimp only
  ring

theorem contDiff_uncurry_hughesYoungLocalizedStaticWeight
    (T c u : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ContDiff ℝ ∞ (Function.uncurry
      (hughesYoungLocalizedStaticWeight T c u X Y h k)) := by
  rw [show Function.uncurry
      (hughesYoungLocalizedStaticWeight T c u X Y h k) =
      fun p : ℝ × ℝ =>
        hughesYoungLocalizedStaticScalar T h k *
          hughesYoungLocalizedLogKernel X Y h k
            ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))
            ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) p.1 p.2 by
    funext p
    exact hughesYoungLocalizedStaticWeight_eq_scalar_mul_kernel
      T c u X Y h k p.1 p.2]
  exact contDiff_const.mul
    (contDiff_uncurry_hughesYoungLocalizedLogKernel hX hY hh hk _ _)

/-- The fixed-shift extension is globally smooth as long as the shift is
strictly shorter than the lower dyadic `y` scale.  At points below that scale
the dyadic cutoff vanishes on a neighborhood; above it, `1+r/y` is positive. -/
theorem contDiff_uncurry_hughesYoungCleanedShiftWeight
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ)
    (hr : |(r : ℝ)| < Y) :
    ContDiff ℝ ∞ (Function.uncurry
      (hughesYoungCleanedShiftWeight T c u X Y h k r)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hpY : p.2 < Y
  · have hnhds : Set.Iio Y ∈ 𝓝 p.2 := Iio_mem_nhds hpY
    have hpull : Prod.snd ⁻¹' Set.Iio Y ∈ 𝓝 p :=
      continuous_snd.continuousAt hnhds
    have hzero : Function.uncurry
        (hughesYoungCleanedShiftWeight T c u X Y h k r) =ᶠ[𝓝 p]
          (fun _ => 0) := by
      filter_upwards [hpull] with z hz
      change hughesYoungCleanedShiftWeight T c u X Y h k r z.1 z.2 = 0
      have hcut : hughesYoungDyadicCutoffAt Y z.2 = 0 :=
        hughesYoungDyadicCutoff_eq_zero_of_le_one
          ((div_le_one hY).2 hz.le)
      unfold hughesYoungCleanedShiftWeight
      rw [hughesYoungLocalizedStaticWeight_eq_scalar_mul_kernel]
      unfold hughesYoungLocalizedLogKernel
      rw [hcut]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hzero
  · have hpYle : Y ≤ p.2 := le_of_not_gt hpY
    have hp2 : 0 < p.2 := hY.trans_le hpYle
    have hrLower : -Y < (r : ℝ) := by
      have hneg : -(Y : ℝ) < -|(r : ℝ)| := neg_lt_neg hr
      exact hneg.trans_le (neg_abs_le (r : ℝ))
    have hsum : 0 < p.2 + (r : ℝ) := by linarith
    have harg : 0 < 1 + (r : ℝ) / p.2 := by
      rw [one_add_div hp2.ne']
      exact div_pos hsum hp2
    have hinner : ContDiffAt ℝ ∞
        (fun z : ℝ × ℝ => 1 + (r : ℝ) / z.2) p :=
      contDiffAt_const.add
        (contDiffAt_const.div contDiff_snd.contDiffAt hp2.ne')
    have hlog : ContDiffAt ℝ ∞
        (fun z : ℝ × ℝ => -Real.log (1 + (r : ℝ) / z.2)) p :=
      ((Real.contDiffAt_log.2 harg.ne').comp p hinner).neg
    have htransform : ContDiffAt ℝ ∞
        (fun z : ℝ × ℝ =>
          hughesYoungHeightTransform T c u
            (-Real.log (1 + (r : ℝ) / z.2))) p :=
      (contDiff_hughesYoungHeightTransform hT hc u).contDiffAt.comp p hlog
    exact (contDiffAt_const.mul
      (contDiff_uncurry_hughesYoungLocalizedStaticWeight
        T c u hX hY hh hk).contDiffAt).mul htransform

theorem support_uncurry_hughesYoungCleanedShiftWeight_subset
    (T c u : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (r : ℤ) :
    Function.support (Function.uncurry
      (hughesYoungCleanedShiftWeight T c u X Y h k r)) ⊆
        Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
  intro p hp
  have hstatic : hughesYoungLocalizedStaticWeight
      T c u X Y h k p.1 p.2 ≠ 0 := by
    intro hz
    apply hp
    unfold hughesYoungCleanedShiftWeight
    change (1 / (T : ℂ)) *
      hughesYoungLocalizedStaticWeight T c u X Y h k p.1 p.2 *
        hughesYoungHeightTransform T c u (-Real.log (1 + (r : ℝ) / p.2)) = 0
    rw [hz, mul_zero, zero_mul]
  rw [hughesYoungLocalizedStaticWeight_eq_scalar_mul_kernel] at hstatic
  have hkernel : hughesYoungLocalizedLogKernel X Y h k
      ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))
      ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) p.1 p.2 ≠ 0 := by
    intro hz
    exact hstatic (by rw [hz, mul_zero])
  exact support_uncurry_hughesYoungLocalizedLogKernel_subset
    hX hY h k _ _ hkernel

/-- The actual fixed-shift Hughes--Young weight satisfies DFI equation (2).
This is a source theorem, not the final uniform family estimate: the latter
also records constants independent of the dyadic and height parameters. -/
theorem hughesYoungCleanedShiftWeight_equation2
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {P X Y : ℝ} (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ)
    (hr : |(r : ℝ)| < Y) :
    DFIEquation2
      (hughesYoungCleanedShiftWeight T c u X Y h k r) P X Y := by
  apply DFIEquation2.of_smooth_dyadicBox hP hX hY
    (contDiff_uncurry_hughesYoungCleanedShiftWeight hT hc u
      (lt_of_lt_of_le (by norm_num) hX)
      (lt_of_lt_of_le (by norm_num) hY) hh hk r hr)
  exact ⟨support_uncurry_hughesYoungCleanedShiftWeight_subset
    T c u (lt_of_lt_of_le (by norm_num) hX)
      (lt_of_lt_of_le (by norm_num) hY) h k r⟩

/-- Termwise source bridge for the finite DFI box. -/
theorem dfiDyadicShiftedDivisorSum_hughesYoungCleaned_eq_heightIntegral
    (T c u X Y : ℝ) {a b M N : ℕ} (ha : 0 < a) (hb : 0 < b)
    (r : ℤ) :
    dfiDyadicShiftedDivisorSum
        (hughesYoungCleanedShiftWeight T c u X Y a b r) a b M N r =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        if quadraticDivisorShift a b m n = r then
          divisorWeight m * divisorWeight n *
            ((1 / (T : ℂ)) *
              (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungLocalizedMellinWeight T t c u X Y a b
                  (a * m) (b * n)))
        else 0 := by
  unfold dfiDyadicShiftedDivisorSum
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hs : quadraticDivisorShift a b m n = r
  · rw [if_pos hs, if_pos hs]
    congr 2
    simp only [Finset.mem_Icc] at hm hn
    have hmpos : 0 < m := by omega
    have hnpos : 0 < n := by omega
    have hamp : 0 < a * m := Nat.mul_pos ha hmpos
    have hbnp : 0 < b * n := Nat.mul_pos hb hnpos
    apply hughesYoungCleanedShiftWeight_eq_heightIntegral T c u X Y ha hb
    · exact_mod_cast hamp
    · exact_mod_cast hbnp
    · unfold quadraticDivisorShift at hs
      exact_mod_cast hs
  · simp [hs]

end RiemannZeta.GuthMaynard
