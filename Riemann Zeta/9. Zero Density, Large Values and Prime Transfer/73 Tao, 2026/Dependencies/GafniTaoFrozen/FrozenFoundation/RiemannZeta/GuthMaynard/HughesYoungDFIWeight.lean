import RiemannZeta.GuthMaynard.HughesYoungAFE
import RiemannZeta.GuthMaynard.HughesYoungDyadic

open Complex Filter Set Topology
open scoped ContDiff Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Localized Hughes--Young weights for the DFI theorem

This file supplies the analytic source-entry bridge missing between the
four-index Hughes--Young expansion and `DFIEquation2`.  The logarithmic form
of a positive real complex power is used only to expose smooth dependence on
the two physical variables.  A theorem below proves that it is exactly the
original complex power on the positive quadrant.
-/

/-- The logarithmic realization of `x ^ (-s)` on a positive real input. -/
noncomputable def hughesYoungLogPower (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-s * (Real.log x : ℂ))

theorem hughesYoungLogPower_eq_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    hughesYoungLogPower s x = (x : ℂ) ^ (-s) := by
  unfold hughesYoungLogPower
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  congr 1
  ring

/-- The part of one localized Hughes--Young source term that depends on the
physical variables `(x,y)`.  The scales `X,Y` are the exact DFI box scales;
`h,k` are the two mollifier indices. -/
noncomputable def hughesYoungLocalizedLogKernel
    (X Y : ℝ) (h k : ℕ) (s₁ s₂ : ℂ) (x y : ℝ) : ℂ :=
  (hughesYoungDyadicCutoffAt X x : ℂ) *
    (hughesYoungDyadicCutoffAt Y y : ℂ) *
    hughesYoungLogPower s₁ (x / h) *
    hughesYoungLogPower s₂ (y / k)

theorem hughesYoungLocalizedLogKernel_eq_cpow
    {X Y x y : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hx : 0 < x) (hy : 0 < y) (s₁ s₂ : ℂ) :
    hughesYoungLocalizedLogKernel X Y h k s₁ s₂ x y =
      (hughesYoungDyadicCutoffAt X x : ℂ) *
        (hughesYoungDyadicCutoffAt Y y : ℂ) *
        ((x / h : ℝ) : ℂ) ^ (-s₁) *
        ((y / k : ℝ) : ℂ) ^ (-s₂) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold hughesYoungLocalizedLogKernel
  rw [hughesYoungLogPower_eq_cpow (div_pos hx hhR),
    hughesYoungLogPower_eq_cpow (div_pos hy hkR)]

private theorem eventually_hughesYoungDyadicCutoffAt_eq_zero_at_zero
    {X : ℝ} (hX : 0 < X) :
    hughesYoungDyadicCutoffAt X =ᶠ[𝓝 0] 0 := by
  filter_upwards [Iio_mem_nhds hX] with z hz
  apply hughesYoungDyadicCutoff_eq_zero_of_le_one
  exact (div_le_one hX).2 hz.le

/-- The localized logarithmic kernel is globally smooth.  At either
coordinate axis the apparent logarithmic singularity is removable because
the corresponding box cutoff vanishes on a whole neighborhood. -/
theorem contDiff_uncurry_hughesYoungLocalizedLogKernel
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (s₁ s₂ : ℂ) :
    ContDiff ℝ ∞ (Function.uncurry
      (hughesYoungLocalizedLogKernel X Y h k s₁ s₂)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hx : p.1 = 0
  · have hcut :
        (fun z : ℝ × ℝ => hughesYoungDyadicCutoffAt X z.1) =ᶠ[𝓝 p]
          (fun _ => (0 : ℝ)) := by
      have hnhds : Set.Iio X ∈ 𝓝 p.1 := by
        rw [hx]
        exact Iio_mem_nhds hX
      have hpull : Prod.fst ⁻¹' Set.Iio X ∈ 𝓝 p :=
        continuous_fst.continuousAt hnhds
      filter_upwards [hpull] with z hz
      exact hughesYoungDyadicCutoff_eq_zero_of_le_one
        ((div_le_one hX).2 hz.le)
    have hzero : Function.uncurry
        (hughesYoungLocalizedLogKernel X Y h k s₁ s₂) =ᶠ[𝓝 p]
          (fun _ => 0) := by
      filter_upwards [hcut] with z hz
      change (hughesYoungDyadicCutoffAt X z.1 : ℂ) *
          (hughesYoungDyadicCutoffAt Y z.2 : ℂ) *
          hughesYoungLogPower s₁ (z.1 / h) *
          hughesYoungLogPower s₂ (z.2 / k) = 0
      rw [hz]
      norm_num
    exact contDiffAt_const.congr_of_eventuallyEq hzero
  · by_cases hy : p.2 = 0
    · have hcut :
          (fun z : ℝ × ℝ => hughesYoungDyadicCutoffAt Y z.2) =ᶠ[𝓝 p]
            (fun _ => (0 : ℝ)) := by
        have hnhds : Set.Iio Y ∈ 𝓝 p.2 := by
          rw [hy]
          exact Iio_mem_nhds hY
        have hpull : Prod.snd ⁻¹' Set.Iio Y ∈ 𝓝 p :=
          continuous_snd.continuousAt hnhds
        filter_upwards [hpull] with z hz
        exact hughesYoungDyadicCutoff_eq_zero_of_le_one
          ((div_le_one hY).2 hz.le)
      have hzero : Function.uncurry
          (hughesYoungLocalizedLogKernel X Y h k s₁ s₂) =ᶠ[𝓝 p]
            (fun _ => 0) := by
        filter_upwards [hcut] with z hz
        change (hughesYoungDyadicCutoffAt X z.1 : ℂ) *
            (hughesYoungDyadicCutoffAt Y z.2 : ℂ) *
            hughesYoungLogPower s₁ (z.1 / h) *
            hughesYoungLogPower s₂ (z.2 / k) = 0
        rw [hz]
        norm_num
      exact contDiffAt_const.congr_of_eventuallyEq hzero
    · have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      have hxDiv : p.1 / (h : ℝ) ≠ 0 := div_ne_zero hx hhR
      have hyDiv : p.2 / (k : ℝ) ≠ 0 := div_ne_zero hy hkR
      have hlogX : ContDiffAt ℝ ∞
          (fun z : ℝ × ℝ => Real.log (z.1 / (h : ℝ))) p :=
        (Real.contDiffAt_log.2 hxDiv).comp p
          (contDiff_fst.div_const (h : ℝ)).contDiffAt
      have hlogY : ContDiffAt ℝ ∞
          (fun z : ℝ × ℝ => Real.log (z.2 / (k : ℝ))) p :=
        (Real.contDiffAt_log.2 hyDiv).comp p
          (contDiff_snd.div_const (k : ℝ)).contDiffAt
      have hpowX : ContDiffAt ℝ ∞
          (fun z : ℝ × ℝ => hughesYoungLogPower s₁ (z.1 / h)) p := by
        unfold hughesYoungLogPower
        exact (contDiffAt_const.mul
          (Complex.ofRealCLM.contDiff.contDiffAt.comp p hlogX)).cexp
      have hpowY : ContDiffAt ℝ ∞
          (fun z : ℝ × ℝ => hughesYoungLogPower s₂ (z.2 / k)) p := by
        unfold hughesYoungLogPower
        exact (contDiffAt_const.mul
          (Complex.ofRealCLM.contDiff.contDiffAt.comp p hlogY)).cexp
      have hcutX : ContDiffAt ℝ ∞
          (fun z : ℝ × ℝ =>
            (hughesYoungDyadicCutoffAt X z.1 : ℂ)) p :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp p
          ((contDiff_hughesYoungDyadicCutoffAt X).comp
            contDiff_fst).contDiffAt
      have hcutY : ContDiffAt ℝ ∞
          (fun z : ℝ × ℝ =>
            (hughesYoungDyadicCutoffAt Y z.2 : ℂ)) p :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp p
          ((contDiff_hughesYoungDyadicCutoffAt Y).comp
            contDiff_snd).contDiffAt
      exact (((hcutX.mul hcutY).mul hpowX).mul hpowY)

theorem support_uncurry_hughesYoungLocalizedLogKernel_subset
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (s₁ s₂ : ℂ) :
    Function.support (Function.uncurry
      (hughesYoungLocalizedLogKernel X Y h k s₁ s₂)) ⊆
        Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
  intro p hp
  have hcutX : hughesYoungDyadicCutoffAt X p.1 ≠ 0 := by
    intro hz
    apply hp
    change (hughesYoungDyadicCutoffAt X p.1 : ℂ) *
        (hughesYoungDyadicCutoffAt Y p.2 : ℂ) *
        hughesYoungLogPower s₁ (p.1 / h) *
        hughesYoungLogPower s₂ (p.2 / k) = 0
    rw [hz]
    norm_num
  have hcutY : hughesYoungDyadicCutoffAt Y p.2 ≠ 0 := by
    intro hz
    apply hp
    change (hughesYoungDyadicCutoffAt X p.1 : ℂ) *
        (hughesYoungDyadicCutoffAt Y p.2 : ℂ) *
        hughesYoungLogPower s₁ (p.1 / h) *
        hughesYoungLogPower s₂ (p.2 / k) = 0
    rw [hz]
    norm_num
  exact ⟨support_hughesYoungDyadicCutoffAt_subset hX hcutX,
    support_hughesYoungDyadicCutoffAt_subset hY hcutY⟩

/-- The elementary localized Hughes--Young Mellin kernel is a genuine DFI
equation-(2) weight, constructed without an analytic hypothesis. -/
theorem hughesYoungLocalizedLogKernel_equation2
    {P X Y : ℝ} (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (s₁ s₂ : ℂ) :
    DFIEquation2
      (hughesYoungLocalizedLogKernel X Y h k s₁ s₂) P X Y := by
  apply DFIEquation2.of_smooth_dyadicBox hP hX hY
    (contDiff_uncurry_hughesYoungLocalizedLogKernel
      (lt_of_lt_of_le (by norm_num) hX)
      (lt_of_lt_of_le (by norm_num) hY) hh hk s₁ s₂)
  exact ⟨support_uncurry_hughesYoungLocalizedLogKernel_subset
    (lt_of_lt_of_le (by norm_num) hX)
    (lt_of_lt_of_le (by norm_num) hY) h k s₁ s₂⟩

/-! ## The literal localized Hughes--Young Mellin summand -/

/-- All factors of one `t,u,h,k` summand which do not depend on the two
physical divisor variables. -/
noncomputable def hughesYoungMellinScalar
    (T t c u : ℝ) (h k : ℕ) : ℂ :=
  shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
    shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t)) *
    (1 / (Real.pi : ℂ)) * hughesYoungRightContourWeight t c u

/-- One literal localized integrand before the compact Mellin-ordinate and
height integrations.  It is the source weight to which DFI can be applied
pointwise in the two auxiliary real parameters. -/
noncomputable def hughesYoungLocalizedMellinWeight
    (T t c u X Y : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  hughesYoungMellinScalar T t c u h k *
    hughesYoungLocalizedLogKernel X Y h k
      (afeCriticalPoint t + w) (afeCriticalPoint (-t) + w) x y

/-- On the positive quadrant, the localized logarithmic summand is exactly
the corresponding summand in the opened Hughes--Young source weight. -/
theorem hughesYoungLocalizedMellinWeight_eq_source_integrand
    (T t c u X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hughesYoungLocalizedMellinWeight T t c u X Y h k x y =
      (hughesYoungDyadicCutoffAt X x : ℂ) *
        (hughesYoungDyadicCutoffAt Y y : ℂ) *
        (shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
          shortMobiusSquareCoeff T k *
            (k : ℂ) ^ (-afeCriticalPoint (-t)) *
          (1 / (Real.pi : ℂ)) *
          (let w : ℂ := (c : ℂ) + (u : ℂ) * I
           hughesYoungRightContourWeight t c u *
             ((x / h : ℝ) : ℂ) ^ (-(afeCriticalPoint t + w)) *
             ((y / k : ℝ) : ℂ) ^ (-(afeCriticalPoint (-t) + w)))) := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  rw [hughesYoungLocalizedMellinWeight]
  dsimp only [w]
  rw [hughesYoungLocalizedLogKernel_eq_cpow hh hk hx hy]
  unfold hughesYoungMellinScalar
  ring

theorem contDiff_uncurry_hughesYoungLocalizedMellinWeight
    (T t c u : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ContDiff ℝ ∞ (Function.uncurry
      (hughesYoungLocalizedMellinWeight T t c u X Y h k)) := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  exact contDiff_const.mul
    (contDiff_uncurry_hughesYoungLocalizedLogKernel
      hX hY hh hk (afeCriticalPoint t + w) (afeCriticalPoint (-t) + w))

theorem support_uncurry_hughesYoungLocalizedMellinWeight_subset
    (T t c u : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) :
    Function.support (Function.uncurry
      (hughesYoungLocalizedMellinWeight T t c u X Y h k)) ⊆
        Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
  intro p hp
  have hkernel : hughesYoungLocalizedLogKernel X Y h k
      (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))
      (afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) p.1 p.2 ≠ 0 := by
    intro hz
    apply hp
    change hughesYoungMellinScalar T t c u h k *
      hughesYoungLocalizedLogKernel X Y h k
        (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))
        (afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) p.1 p.2 = 0
    rw [hz, mul_zero]
  exact support_uncurry_hughesYoungLocalizedLogKernel_subset
    hX hY h k _ _ hkernel

/-- Each literal localized Hughes--Young `t,u,h,k` summand satisfies DFI
equation (2); no source-weight hypothesis is passed to the consumer. -/
theorem hughesYoungLocalizedMellinWeight_equation2
    (T t c u : ℝ) {P X Y : ℝ}
    (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    DFIEquation2
      (hughesYoungLocalizedMellinWeight T t c u X Y h k) P X Y := by
  apply DFIEquation2.of_smooth_dyadicBox hP hX hY
    (contDiff_uncurry_hughesYoungLocalizedMellinWeight T t c u
      (lt_of_lt_of_le (by norm_num) hX)
      (lt_of_lt_of_le (by norm_num) hY) hh hk)
  exact ⟨support_uncurry_hughesYoungLocalizedMellinWeight_subset
    T t c u (lt_of_lt_of_le (by norm_num) hX)
      (lt_of_lt_of_le (by norm_num) hY) h k⟩

end RiemannZeta.GuthMaynard
