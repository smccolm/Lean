import RiemannZeta.GuthMaynard.HughesYoungReducedFubini
import RiemannZeta.GuthMaynard.HughesYoungReducedConsumer
import RiemannZeta.GuthMaynard.HughesYoungIntegratedConsumer
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Compact

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

set_option maxHeartbeats 2000000

namespace RiemannZeta.GuthMaynard

/-!
# Continuity of the Hughes--Young signed DFI central term

These lemmas justify the compact Mellin-ordinate integration of the
infinite DFI equation-(27) series.  The first step records the joint
continuity in the Mellin ordinate and Fourier variable which is implicit in
the compactly supported height integral.
-/

/-- The Hughes--Young height transform is jointly continuous in its Mellin
ordinate and Fourier variable. -/
theorem continuous_uncurry_hughesYoungHeightTransform
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) :
    Continuous (fun p : ℝ × ℝ =>
      hughesYoungHeightTransform T c p.1 p.2) := by
  let F : (ℝ × ℝ) → ℝ → ℂ := fun p t =>
    Complex.exp ((((t * p.2 : ℝ) : ℂ) * I)) *
      hughesYoungHeightFourierInput T c p.1 t
  have hF : Continuous F.uncurry := by
    unfold F hughesYoungHeightFourierInput
    have hright : Continuous (fun z : (ℝ × ℝ) × ℝ =>
        hughesYoungRightContourWeight z.2 c z.1.1) := by
      let swap : ((ℝ × ℝ) × ℝ) → ℝ × ℝ := fun z => (z.2, z.1.1)
      have hswap : Continuous swap :=
        continuous_snd.prodMk (continuous_fst.comp continuous_fst)
      have hbase : Continuous (Function.uncurry
          (fun t u : ℝ => hughesYoungRightContourWeight t c u)) :=
        continuous_uncurry_hughesYoungRightContourWeight hc
      have hcomp := hbase.comp hswap
      simpa only [swap, Function.uncurry_apply_pair] using hcomp
    have hmul : Continuous (fun z : (ℝ × ℝ) × ℝ => z.2 * z.1.2) :=
      continuous_snd.mul (continuous_snd.comp continuous_fst)
    have hreal : Continuous (fun z : (ℝ × ℝ) × ℝ =>
        ((z.2 * z.1.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.continuous.comp hmul
    have harg : Continuous (fun z : (ℝ × ℝ) × ℝ =>
        ((z.2 * z.1.2 : ℝ) : ℂ) * I) := hreal.mul continuous_const
    have hphase : Continuous (fun z : (ℝ × ℝ) × ℝ =>
        Complex.exp ((((z.2 * z.1.2 : ℝ) : ℂ) * I))) :=
      Complex.continuous_exp.comp harg
    have hcut : Continuous (fun z : (ℝ × ℝ) × ℝ =>
        (hughesYoungHeightWeight T z.2 : ℂ)) :=
      Complex.ofRealCLM.continuous.comp
        ((contDiff_hughesYoungHeightWeight T).continuous.comp continuous_snd)
    exact hphase.mul (hcut.mul hright)
  have hset : ∀ p : ℝ × ℝ,
      (∫ t : ℝ, F p t) = ∫ t in Set.Icc (T / 4) (4 * T), F p t := by
    intro p
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    unfold F hughesYoungHeightFourierInput
    have hzero : hughesYoungHeightWeight T t = 0 := by
      by_contra hn
      exact ht (hughesYoungHeightWeight_support hT hn)
    simp [hzero]
  have hrepr : (fun p : ℝ × ℝ => hughesYoungHeightTransform T c p.1 p.2) =
      fun p => ∫ t in Set.Icc (T / 4) (4 * T), F p t := by
    funext p
    rw [← hset p, hughesYoungHeightTransform_eq_integral]
  rw [hrepr]
  exact continuous_parametric_integral_of_continuous hF isCompact_Icc

/-- Joint continuity of one localized Mellin factor in the ordinate and
physical variable.  The cutoff removes the logarithmic singularity
uniformly in the ordinate. -/
theorem continuous_uncurry_hughesYoungLocalizedOneFactor_ordinate
    {X h : ℝ} (hX : 0 < X) (hh : 0 < h) (c : ℝ) :
    Continuous (fun p : ℝ × ℝ =>
      hughesYoungLocalizedOneFactor X h
        ((1 / 2 : ℂ) + ((c : ℂ) + (p.1 : ℂ) * I)) p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hx : p.2 < X
  · have hmem : Prod.snd ⁻¹' Set.Iio X ∈ nhds p :=
      continuous_snd.continuousAt (Iio_mem_nhds hx)
    have heq : (fun z : ℝ × ℝ =>
        hughesYoungLocalizedOneFactor X h
          ((1 / 2 : ℂ) + ((c : ℂ) + (z.1 : ℂ) * I)) z.2) =ᶠ[nhds p]
          fun _ => 0 := by
      filter_upwards [hmem] with z hz
      change z.2 < X at hz
      unfold hughesYoungLocalizedOneFactor
      have hcut : hughesYoungDyadicCutoffAt X z.2 = 0 :=
        hughesYoungDyadicCutoff_eq_zero_of_le_one
          ((div_le_one hX).2 hz.le)
      simp [hcut]
    exact continuousAt_const.congr_of_eventuallyEq heq
  · have hx0 : 0 < p.2 := hX.trans_le (le_of_not_gt hx)
    have hdiv0 : p.2 / h ≠ 0 := div_ne_zero hx0.ne' hh.ne'
    have hlog : ContinuousAt (fun z : ℝ × ℝ => Real.log (z.2 / h)) p :=
      (continuousAt_snd.div_const h).log hdiv0
    have hs : ContinuousAt (fun z : ℝ × ℝ =>
        (1 / 2 : ℂ) + ((c : ℂ) + (z.1 : ℂ) * I)) p := by
      fun_prop
    have hpow : ContinuousAt (fun z : ℝ × ℝ =>
        hughesYoungLogPower
          ((1 / 2 : ℂ) + ((c : ℂ) + (z.1 : ℂ) * I)) (z.2 / h)) p := by
      unfold hughesYoungLogPower
      exact Complex.continuous_exp.continuousAt.comp
        ((hs.neg.mul (Complex.ofRealCLM.continuous.continuousAt.comp hlog)))
    unfold hughesYoungLocalizedOneFactor
    exact (Complex.ofRealCLM.continuous.continuousAt.comp
      ((contDiff_hughesYoungDyadicCutoffAt X).continuous.continuousAt.comp
        continuousAt_snd)).mul hpow

/-- Along the physical shifted line `y = x - r`, the exact reduced
Hughes--Young equation-(70) weight is jointly continuous in the Mellin
ordinate and the remaining physical variable.  The two dyadic cutoffs
remove every apparent logarithmic singularity before continuity is used. -/
theorem continuous_uncurry_hughesYoungReducedCleanedShiftWeight_on_line
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ) :
    Continuous (fun p : ℝ × ℝ =>
      hughesYoungReducedCleanedShiftWeight T c p.1 X Y h k r
        p.2 (p.2 - (r : ℝ))) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hx : p.2 < X
  · have hmem : Prod.snd ⁻¹' Set.Iio X ∈ nhds p :=
      continuous_snd.continuousAt (Iio_mem_nhds hx)
    have heq : (fun z : ℝ × ℝ =>
        hughesYoungReducedCleanedShiftWeight T c z.1 X Y h k r
          z.2 (z.2 - (r : ℝ))) =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hmem] with z hz
      change z.2 < X at hz
      have hcut : hughesYoungDyadicCutoffAt X z.2 = 0 :=
        hughesYoungDyadicCutoff_eq_zero_of_le_one
          ((div_le_one hX).2 hz.le)
      unfold hughesYoungReducedCleanedShiftWeight
        hughesYoungReducedLocalizedStaticWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    exact continuousAt_const.congr_of_eventuallyEq heq
  · let y : ℝ := p.2 - (r : ℝ)
    by_cases hy : y < Y
    · have hycont : Continuous (fun z : ℝ × ℝ =>
          z.2 - (r : ℝ)) := continuous_snd.sub continuous_const
      have hmem : (fun z : ℝ × ℝ => z.2 - (r : ℝ)) ⁻¹'
          Set.Iio Y ∈ nhds p :=
        hycont.continuousAt (Iio_mem_nhds hy)
      have heq : (fun z : ℝ × ℝ =>
          hughesYoungReducedCleanedShiftWeight T c z.1 X Y h k r
            z.2 (z.2 - (r : ℝ))) =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [hmem] with z hz
        change z.2 - (r : ℝ) < Y at hz
        have hcut : hughesYoungDyadicCutoffAt Y (z.2 - (r : ℝ)) = 0 :=
          hughesYoungDyadicCutoff_eq_zero_of_le_one
            ((div_le_one hY).2 hz.le)
        unfold hughesYoungReducedCleanedShiftWeight
          hughesYoungReducedLocalizedStaticWeight
          hughesYoungLocalizedLogKernel
        simp [hcut]
      exact continuousAt_const.congr_of_eventuallyEq heq
    · have hx0 : 0 < p.2 := hX.trans_le (le_of_not_gt hx)
      have hy0 : 0 < y := hY.trans_le (le_of_not_gt hy)
      let a : ℕ := hughesYoungReducedLeft h k
      let b : ℕ := hughesYoungReducedRight h k
      have ha : 0 < a := hughesYoungReducedLeft_pos hh
      have hb : 0 < b := hughesYoungReducedRight_pos hh hk
      have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
      have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
      have hfirst : ContinuousAt (fun z : ℝ × ℝ =>
          hughesYoungLocalizedOneFactor X a
            ((1 / 2 : ℂ) + ((c : ℂ) + (z.1 : ℂ) * I)) z.2) p :=
        (continuous_uncurry_hughesYoungLocalizedOneFactor_ordinate
          (X := X) (h := (a : ℝ)) hX haR c).continuousAt
      have hsecond : ContinuousAt (fun z : ℝ × ℝ =>
          hughesYoungLocalizedOneFactor Y b
            ((1 / 2 : ℂ) + ((c : ℂ) + (z.1 : ℂ) * I))
            (z.2 - (r : ℝ))) p := by
        have hmapContinuous : Continuous (fun z : ℝ × ℝ =>
            (z.1, z.2 - (r : ℝ))) :=
          continuous_fst.prodMk (continuous_snd.sub continuous_const)
        have hcomp : Continuous (fun z : ℝ × ℝ =>
            hughesYoungLocalizedOneFactor Y (b : ℝ)
              ((1 / 2 : ℂ) + ((c : ℂ) + (z.1 : ℂ) * I))
              (z.2 - (r : ℝ))) := by
          simpa only [Function.comp_apply] using
          (continuous_uncurry_hughesYoungLocalizedOneFactor_ordinate
            (X := Y) (h := (b : ℝ)) hY hbR c).comp hmapContinuous
        exact hcomp.continuousAt
      have hratio0 : 0 < 1 + (r : ℝ) / y := by
        rw [one_add_div hy0.ne']
        change 0 < (y + (r : ℝ)) / y
        have hnum : y + (r : ℝ) = p.2 := by dsimp [y]; ring
        rw [hnum]
        positivity
      have hratio : ContinuousAt (fun z : ℝ × ℝ =>
          1 + (r : ℝ) / (z.2 - (r : ℝ))) p := by
        exact continuousAt_const.add
          (continuousAt_const.div
            (continuousAt_snd.sub continuousAt_const) hy0.ne')
      have hlog : ContinuousAt (fun z : ℝ × ℝ =>
          -Real.log (1 + (r : ℝ) / (z.2 - (r : ℝ)))) p :=
        (hratio.log hratio0.ne').neg
      have hheightMap : ContinuousAt (fun z : ℝ × ℝ =>
          (z.1, -Real.log (1 + (r : ℝ) /
            (z.2 - (r : ℝ))))) p :=
        continuousAt_fst.prodMk hlog
      have hheight : ContinuousAt (fun z : ℝ × ℝ =>
          hughesYoungHeightTransform T c z.1
            (-Real.log (1 + (r : ℝ) / (z.2 - (r : ℝ))))) p := by
        have hmapContinuous : ContinuousAt (fun z : ℝ × ℝ =>
            (z.1, -Real.log (1 + (r : ℝ) /
              (z.2 - (r : ℝ))))) p := hheightMap
        have hbase : ContinuousAt (fun w : ℝ × ℝ =>
            hughesYoungHeightTransform T c w.1 w.2)
            ((fun z : ℝ × ℝ =>
              (z.1, -Real.log (1 + (r : ℝ) /
                (z.2 - (r : ℝ))))) p) :=
          (continuous_uncurry_hughesYoungHeightTransform hT hc).continuousAt
        have hcomp := ContinuousAt.comp_of_eq
          (f := fun z : ℝ × ℝ =>
            (z.1, -Real.log (1 + (r : ℝ) /
              (z.2 - (r : ℝ))))) hbase hmapContinuous rfl
        simpa only [Function.comp_apply] using hcomp
      rw [show (fun z : ℝ × ℝ =>
          hughesYoungReducedCleanedShiftWeight T c z.1 X Y h k r
            z.2 (z.2 - (r : ℝ))) = fun z =>
          hughesYoungLocalizedStaticScalar T h k *
            (hughesYoungLocalizedOneFactor X a
                ((1 / 2 : ℂ) + ((c : ℂ) + (z.1 : ℂ) * I)) z.2 *
              (hughesYoungLocalizedOneFactor Y b
                  ((1 / 2 : ℂ) + ((c : ℂ) + (z.1 : ℂ) * I))
                  (z.2 - (r : ℝ)) *
                ((1 / (T : ℂ)) *
                  hughesYoungHeightTransform T c z.1
                    (-Real.log (1 + (r : ℝ) /
                      (z.2 - (r : ℝ))))))) by
        funext z
        rw [hughesYoungReducedCleanedShiftWeight_eq_staticScalar_mul_dfiCore]
        unfold hughesYoungDFICore
        rfl]
      exact continuousAt_const.mul
        (hfirst.mul (hsecond.mul (continuousAt_const.mul hheight)))

/-- Joint continuity of the literal DFI equation-(27) logarithmic kernel
for the reduced Hughes--Young source, restricted to its shifted line. -/
theorem continuous_uncurry_dfiEquation27C_reducedCleaned_on_line
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ)
    (qx qy : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      dfiEquation27C
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) qx qy
        (hughesYoungReducedCleanedShiftWeight T c p.1 X Y h k r)
        p.2 (p.2 - (r : ℝ))) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hx : p.2 < X
  · have hmem : Prod.snd ⁻¹' Set.Iio X ∈ nhds p :=
      continuous_snd.continuousAt (Iio_mem_nhds hx)
    have heq : (fun z : ℝ × ℝ =>
        dfiEquation27C
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) qx qy
          (hughesYoungReducedCleanedShiftWeight T c z.1 X Y h k r)
          z.2 (z.2 - (r : ℝ))) =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hmem] with z hz
      change z.2 < X at hz
      have hcut : hughesYoungDyadicCutoffAt X z.2 = 0 :=
        hughesYoungDyadicCutoff_eq_zero_of_le_one
          ((div_le_one hX).2 hz.le)
      unfold dfiEquation27C hughesYoungReducedCleanedShiftWeight
        hughesYoungReducedLocalizedStaticWeight hughesYoungLocalizedLogKernel
      simp [hcut]
    exact continuousAt_const.congr_of_eventuallyEq heq
  · let y : ℝ := p.2 - (r : ℝ)
    by_cases hy : y < Y
    · have hycont : Continuous (fun z : ℝ × ℝ =>
          z.2 - (r : ℝ)) := continuous_snd.sub continuous_const
      have hmem : (fun z : ℝ × ℝ => z.2 - (r : ℝ)) ⁻¹'
          Set.Iio Y ∈ nhds p :=
        hycont.continuousAt (Iio_mem_nhds hy)
      have heq : (fun z : ℝ × ℝ =>
          dfiEquation27C
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) qx qy
            (hughesYoungReducedCleanedShiftWeight T c z.1 X Y h k r)
            z.2 (z.2 - (r : ℝ))) =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [hmem] with z hz
        change z.2 - (r : ℝ) < Y at hz
        have hcut : hughesYoungDyadicCutoffAt Y (z.2 - (r : ℝ)) = 0 :=
          hughesYoungDyadicCutoff_eq_zero_of_le_one
            ((div_le_one hY).2 hz.le)
        unfold dfiEquation27C hughesYoungReducedCleanedShiftWeight
          hughesYoungReducedLocalizedStaticWeight hughesYoungLocalizedLogKernel
        simp [hcut]
      exact continuousAt_const.congr_of_eventuallyEq heq
    · have hx0 : 0 < p.2 := hX.trans_le (le_of_not_gt hx)
      have hy0 : 0 < y := hY.trans_le (le_of_not_gt hy)
      have hweight : ContinuousAt (fun z : ℝ × ℝ =>
          hughesYoungReducedCleanedShiftWeight T c z.1 X Y h k r
            z.2 (z.2 - (r : ℝ))) p :=
        (continuous_uncurry_hughesYoungReducedCleanedShiftWeight_on_line
          hT hc hX hY hh hk r).continuousAt
      have hlogx : ContinuousAt (fun z : ℝ × ℝ =>
          Real.log z.2) p := continuousAt_snd.log hx0.ne'
      have hlogy : ContinuousAt (fun z : ℝ × ℝ =>
          Real.log (z.2 - (r : ℝ))) p :=
        (continuousAt_snd.sub continuousAt_const).log hy0.ne'
      have hfactorx : ContinuousAt (fun z : ℝ × ℝ =>
          (Real.log z.2 : ℂ) -
            Complex.log (hughesYoungReducedLeft h k : ℂ) +
            2 * Real.eulerMascheroniConstant - 2 * Complex.log (qx : ℂ)) p := by
        fun_prop
      have hfactory : ContinuousAt (fun z : ℝ × ℝ =>
          (Real.log (z.2 - (r : ℝ)) : ℂ) -
            Complex.log (hughesYoungReducedRight h k : ℂ) +
            2 * Real.eulerMascheroniConstant - 2 * Complex.log (qy : ℂ)) p := by
        fun_prop
      unfold dfiEquation27C dfiEquation27LogFactor
      exact (hfactorx.mul hfactory).mul hweight

/-- Each DFI equation-(27) central integral for the reduced source varies
continuously in the Mellin ordinate.  Its physical integral is restricted
to the exact compact dyadic support before applying the parametric-integral
theorem. -/
theorem continuous_dfiEquation27CentralIntegral_reducedCleaned_ordinate
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ)
    (qx qy : ℕ) :
    Continuous (fun u : ℝ =>
      dfiEquation27CentralIntegral
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) qx qy
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) r) := by
  let F : (ℝ × ℝ) → ℂ := fun p =>
    dfiEquation27C
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) qx qy
      (hughesYoungReducedCleanedShiftWeight T c p.1 X Y h k r)
      p.2 (p.2 - (r : ℝ))
  have hF : Continuous F :=
    continuous_uncurry_dfiEquation27C_reducedCleaned_on_line
      hT hc hX hY hh hk r qx qy
  have hset : ∀ u : ℝ,
      (∫ x : ℝ, F (u, x)) = ∫ x in Set.Icc X (2 * X), F (u, x) := by
    intro u
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hweight :
        hughesYoungReducedCleanedShiftWeight T c u X Y h k r
          x (x - (r : ℝ)) = 0 := by
      have hcut : hughesYoungDyadicCutoffAt X x = 0 := by
        by_contra hn
        exact hx (support_hughesYoungDyadicCutoffAt_subset hX hn)
      unfold hughesYoungReducedCleanedShiftWeight
        hughesYoungReducedLocalizedStaticWeight hughesYoungLocalizedLogKernel
      simp [hcut]
    dsimp only [F]
    unfold dfiEquation27C
    simp [hweight]
  have hrepr : (fun u : ℝ =>
      dfiEquation27CentralIntegral
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) qx qy
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) r) =
      fun u => ∫ x in Set.Icc X (2 * X), F (u, x) := by
    funext u
    unfold dfiEquation27CentralIntegral
    exact hset u
  rw [hrepr]
  exact continuous_parametric_integral_of_continuous hF isCompact_Icc

/-- Negative source shifts are represented by DFI's exact coordinate swap.
For a positive natural `r`, the swapped central integral is jointly
continuous in the Mellin ordinate after the change of physical variable
`x ↦ x-r`. -/
theorem continuous_dfiEquation27CentralIntegral_swappedReducedCleaned_ordinate
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℕ)
    (qx qy : ℕ) :
    Continuous (fun u : ℝ =>
      dfiEquation27CentralIntegral
        (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k) qx qy
        (dfiSwapWeight
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k (-(r : ℤ)))) r) := by
  let F : (ℝ × ℝ) → ℂ := fun p =>
    dfiEquation27C
      (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k) qx qy
      (dfiSwapWeight
        (hughesYoungReducedCleanedShiftWeight T c p.1 X Y h k (-(r : ℤ))))
      p.2 (p.2 - (r : ℝ))
  have hbase : Continuous (fun p : ℝ × ℝ =>
      dfiEquation27C
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) qy qx
        (hughesYoungReducedCleanedShiftWeight T c p.1 X Y h k (-(r : ℤ)))
        p.2 (p.2 - ((-(r : ℤ) : ℤ) : ℝ))) :=
    continuous_uncurry_dfiEquation27C_reducedCleaned_on_line
      hT hc hX hY hh hk (-(r : ℤ)) qy qx
  have hmap : Continuous (fun p : ℝ × ℝ => (p.1, p.2 - (r : ℝ))) :=
    continuous_fst.prodMk (continuous_snd.sub continuous_const)
  have hF : Continuous F := by
    have hcomp := hbase.comp hmap
    rw [show F = fun p : ℝ × ℝ =>
        dfiEquation27C
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) qy qx
          (hughesYoungReducedCleanedShiftWeight T c p.1 X Y h k (-(r : ℤ)))
          (p.2 - (r : ℝ)) p.2 by
      funext p
      unfold F dfiEquation27C dfiEquation27LogFactor dfiSwapWeight
      ring]
    have heq :
        ((fun p : ℝ × ℝ =>
          dfiEquation27C
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) qy qx
            (hughesYoungReducedCleanedShiftWeight T c p.1 X Y h k (-(r : ℤ)))
            p.2 (p.2 - ((-(r : ℤ) : ℤ) : ℝ))) ∘
          fun p : ℝ × ℝ => (p.1, p.2 - (r : ℝ))) =
        fun p : ℝ × ℝ =>
          dfiEquation27C
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) qy qx
            (hughesYoungReducedCleanedShiftWeight T c p.1 X Y h k (-(r : ℤ)))
            (p.2 - (r : ℝ)) p.2 := by
      funext p
      simp only [Function.comp_apply, Int.cast_neg, Int.cast_natCast]
      congr 1
      ring
    rw [← heq]
    exact hcomp
  have hset : ∀ u : ℝ,
      (∫ x : ℝ, F (u, x)) = ∫ x in Set.Icc Y (2 * Y), F (u, x) := by
    intro u
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hweight :
        hughesYoungReducedCleanedShiftWeight T c u X Y h k (-(r : ℤ))
          (x - (r : ℝ)) x = 0 := by
      have hcut : hughesYoungDyadicCutoffAt Y x = 0 := by
        by_contra hn
        exact hx (support_hughesYoungDyadicCutoffAt_subset hY hn)
      unfold hughesYoungReducedCleanedShiftWeight
        hughesYoungReducedLocalizedStaticWeight hughesYoungLocalizedLogKernel
      simp [hcut]
    dsimp only [F]
    unfold dfiEquation27C dfiSwapWeight
    simp [hweight]
  have hrepr : (fun u : ℝ =>
      dfiEquation27CentralIntegral
        (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k) qx qy
        (dfiSwapWeight
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k (-(r : ℤ)))) r) =
      fun u => ∫ x in Set.Icc Y (2 * Y), F (u, x) := by
    funext u
    unfold dfiEquation27CentralIntegral
    exact hset u
  rw [hrepr]
  exact continuous_parametric_integral_of_continuous hF isCompact_Icc

/-- Every fixed modulus summand in the positive-shift DFI equation-(27)
central series is continuous in the Hughes--Young Mellin ordinate.  The
arithmetic coefficient and the external Jacobian are independent of the
ordinate; all analytic dependence is carried by the central integral. -/
theorem continuous_dfiEquation27CentralSummand_reducedCleaned_ordinate
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r q : ℕ) :
    Continuous (fun u : ℝ =>
      dfiEquation27CentralSummand
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ)) q) := by
  unfold dfiEquation27CentralSummand
  exact continuous_const.mul
    (continuous_dfiEquation27CentralIntegral_reducedCleaned_ordinate
      hT hc hX hY hh hk (r : ℤ)
      (dfiReducedDenominator (hughesYoungReducedLeft h k) q)
      (dfiReducedDenominator (hughesYoungReducedRight h k) q))

/-- Fixed-modulus continuity for the negative-shift branch of the signed
DFI central series. -/
theorem continuous_dfiEquation27CentralSummand_swappedReducedCleaned_ordinate
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r q : ℕ) :
    Continuous (fun u : ℝ =>
      dfiEquation27CentralSummand
        (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k) r
        (dfiSwapWeight
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k (-(r : ℤ)))) q) := by
  unfold dfiEquation27CentralSummand
  exact continuous_const.mul
    (continuous_dfiEquation27CentralIntegral_swappedReducedCleaned_ordinate
      hT hc hX hY hh hk r
      (dfiReducedDenominator (hughesYoungReducedRight h k) q)
      (dfiReducedDenominator (hughesYoungReducedLeft h k) q))

/-- A source-uniform Weierstrass majorant for one equation-(27) summand.
The `q⁻²` arithmetic decay is combined with the `q^(1/2)` cost of the two
logarithms.  Unlike the existential convergence theorem, the displayed
constant is fixed by the DFI derivative profiles and is therefore usable
uniformly in an external Mellin parameter. -/
theorem norm_dfiEquation27CentralSummand_le_profile_pseries
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (a b h q : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    ‖dfiEquation27CentralSummand a b h
        (dfiLocalizedWeight f φ h) q‖ ≤
      (‖(((a : ℂ) * b)⁻¹)‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) *
        dfiEquation27CentralProfileConstant Cf Cφ *
        (1 + Real.log (2 * X) + |Real.log a| +
          2 * |Real.eulerMascheroniConstant| + 8) *
        (1 + Real.log (2 * Y) + |Real.log b| +
          2 * |Real.eulerMascheroniConstant| + 8) * min X Y) *
        (((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ)) := by
  by_cases hq0 : q = 0
  · subst q
    simp [dfiEquation27CentralSummand,
      dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    have hcentral :=
      norm_dfiEquation27CentralIntegral_reduced_uniform_ab_le_rpow_of_profiles
        hf hfC hbox hφ hφC hscale (by norm_num : (0 : ℝ) < 1 / 2)
        a b h q hq
    have harith := norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
      a b h q ha hb hh
    rw [dfiEquation27CentralSummand, norm_mul, norm_mul]
    calc
      ‖((a : ℂ) * b)⁻¹‖ * ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
          ‖dfiEquation27CentralIntegral a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (dfiLocalizedWeight f φ h) h‖ ≤
        ‖((a : ℂ) * b)⁻¹‖ *
          ((((a * b * h ^ 2 : ℕ) : ℝ)) * ((q : ℝ) ^ 2)⁻¹) *
          (dfiEquation27CentralProfileConstant Cf Cφ *
            (1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 8) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 8) *
            min X Y * (q : ℝ) ^ (1 / 2 : ℝ)) := by
          gcongr
          simpa only [show 4 * (1 / 2 : ℝ)⁻¹ = 8 by norm_num] using hcentral
      _ = (‖(((a : ℂ) * b)⁻¹)‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) *
          dfiEquation27CentralProfileConstant Cf Cφ *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 8) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 8) * min X Y) *
          (((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ)) := by ring

/-- Termwise form of the redundant-cutoff identity.  On the central line
`x-y=h`, equation (21)'s cutoff is exactly one, so it can be inserted before
applying the profile-uniform majorant without changing any modulus term. -/
theorem dfiEquation27CentralSummand_localizedWeight_eq
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {U : ℝ}
    (hφ : DFIRedundantCutoff φ U) (a b h q : ℕ) :
    dfiEquation27CentralSummand a b h (dfiLocalizedWeight f φ h) q =
      dfiEquation27CentralSummand a b h f q := by
  unfold dfiEquation27CentralSummand
  congr 1
  unfold dfiEquation27CentralIntegral
  apply integral_congr_ae
  filter_upwards with x
  unfold dfiEquation27C
  rw [dfiLocalizedWeight_eq_of_sub_eq hφ]
  ring

/-- The positive-shift DFI equation-(27) central series for the exact
reduced Hughes--Young weight is continuous in the Mellin ordinate.  The
proof normalizes every ordinate to the same DFI derivative profile and uses
the explicit `q⁻² · q^(1/2)` majorant above on a compact neighborhood of
each ordinate. -/
theorem continuous_dfiEquation27CentralSeries_reducedCleaned_ordinate
    {T c X Y P U : ℝ} {h k r : ℕ}
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hh : 0 < h) (hk : 0 < k)
    (hr : 0 < r) (hrY : (r : ℝ) ≤ Y / 2)
    (hP : 1 ≤ P) (hTR : T * ((r : ℝ) / Y) ≤ P)
    (hU : 0 < U) (hscale : U ≤ P⁻¹ * min X Y) :
    Continuous (fun u : ℝ =>
      dfiEquation27CentralSeries
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ))) := by
  obtain ⟨Cγ, hCγ, hheight⟩ :=
    exists_norm_one_div_mul_iteratedDeriv_hughesYoungHeightTransform_le
  obtain ⟨Ccut, hCcut⟩ :=
    exists_uniform_hughesYoungDyadicCutoffAt_derivativeProfile
  obtain ⟨Cφ, hCφ⟩ := exists_dfiUniformRedundantCutoff_profile
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let A : ℝ → ℝ := hughesYoungSmallLineEnvelope Cγ T c
  let φ : ℝ → ℂ := dfiUniformRedundantCutoff U
  let hφ : DFIRedundantCutoff φ U := dfiUniformRedundantCutoff_spec U hU
  let Cf : ℕ → ℕ → ℝ := hughesYoungUniformDFIProfile Ccut
  let D : ℝ :=
    ‖(((a : ℂ) * b)⁻¹)‖ * (((a * b * r ^ 2 : ℕ) : ℝ)) *
      dfiEquation27CentralProfileConstant Cf Cφ *
      (1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 8) *
      (1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 8) * min X Y
  let pseries : ℕ → ℝ := fun q =>
    ((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ)
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hApos : ∀ u : ℝ, 0 < A u := fun u =>
    hughesYoungSmallLineEnvelope_pos
      (lt_of_lt_of_le zero_lt_one hT) hc u
  have hAcont : Continuous A :=
    continuous_hughesYoungSmallLineEnvelope Cγ T c
  have hφC : DFIRedundantCutoffProfile hφ Cφ := hCφ U hU
  have hD : 0 ≤ D := by
    dsimp only [D, Cf, a, b]
    have hlogX : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith)
    have hlogY : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith)
    have hprofile : 0 < dfiEquation27CentralProfileConstant
        (hughesYoungUniformDFIProfile Ccut) Cφ := by
      have hfC0 : DFIEquation2Profile
          (hughesYoungScaledNormalizedDFICore T c 0 X Y (A 0) a b (r : ℤ))
          P X Y (hughesYoungUniformDFIProfile Ccut) := by
        apply hughesYoungScaledNormalizedDFICore_equation2Profile_unrestricted
          Ccut hCcut hT hc hc1 hX hY ha hb
        · simpa using hrY
        · exact hP
        · simpa using hTR
        · exact hApos 0
        · intro n xi
          simpa only [A, hughesYoungSmallLineEnvelope] using
            hheight T 0 c hT hc hc1 n xi
      exact dfiEquation27CentralProfileConstant_pos hfC0 hφC
    positivity
  rw [continuous_iff_continuousAt]
  intro u₀
  let s : Set ℝ := Set.Icc (u₀ - 1) (u₀ + 1)
  let z : ℝ → ℂ := fun u =>
    hughesYoungLocalizedStaticScalar T h k *
      (hughesYoungScaledDFINormalization c u X Y (A u) a b : ℂ)
  have hzcont : Continuous z := by
    dsimp only [z]
    apply continuous_const.mul
    apply Complex.ofRealCLM.continuous.comp
    exact (((hAcont.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.pow 2)))).mul_const
        (((a : ℝ) / X) ^ ((1 / 2 : ℝ) + c))).mul_const
          (((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)))
  let zMap : C(ℝ, ℂ) := ⟨z, hzcont⟩
  let K : TopologicalSpace.Compacts ℝ := ⟨s, isCompact_Icc⟩
  let B : ℝ := ‖zMap.restrict K‖
  have hB : 0 ≤ B := norm_nonneg _
  have hmajor : Summable (fun q : ℕ => (B * D) * pseries q) := by
    exact summable_natCast_inv_sq_mul_rpow_half.mul_left (B * D)
  have htermContinuous : ∀ q : ℕ, Continuous (fun u : ℝ =>
      dfiEquation27CentralSummand a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ)) q) := by
    intro q
    simpa only [a, b] using
      continuous_dfiEquation27CentralSummand_reducedCleaned_ordinate
        (lt_of_lt_of_le zero_lt_one hT) hc hX0 hY0 hh hk r q
  have htermBound : ∀ q : ℕ, ∀ u ∈ s,
      ‖dfiEquation27CentralSummand a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ)) q‖ ≤
        (B * D) * pseries q := by
    intro q u hu
    let f : ℝ → ℝ → ℂ :=
      hughesYoungScaledNormalizedDFICore T c u X Y (A u) a b (r : ℤ)
    have hderiv : ∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A u) := by
      intro n xi
      simpa only [A, hughesYoungSmallLineEnvelope] using
        hheight T u c hT hc hc1 n xi
    have hf : DFIEquation2 f P X Y := by
      dsimp only [f]
      apply hughesYoungScaledNormalizedDFICore_equation2_unrestricted Ccut hCcut
        hT hc hc1 hX hY ha hb
      · simpa using hrY
      · exact hP
      · simpa using hTR
      · exact hApos u
      · exact hderiv
    have hfC : DFIEquation2Profile f P X Y Cf := by
      dsimp only [f, Cf]
      apply hughesYoungScaledNormalizedDFICore_equation2Profile_unrestricted
        Ccut hCcut hT hc hc1 hX hY ha hb
      · simpa using hrY
      · exact hP
      · simpa using hTR
      · exact hApos u
      · exact hderiv
    have hbox : DFILocalizedBox f X Y := by
      dsimp only [f]
      exact hughesYoungScaledNormalizedDFICore_localizedBox
        hX0 hY0 a b (r : ℤ)
    have hnormalized :
        ‖dfiEquation27CentralSummand a b r f q‖ ≤ D * pseries q := by
      rw [← dfiEquation27CentralSummand_localizedWeight_eq hφ a b r q]
      simpa only [D, pseries] using
        norm_dfiEquation27CentralSummand_le_profile_pseries
          hf hfC hbox hφ hφC hscale a b r q ha hb hr
    have hweight :
        hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ) =
          dfiComplexScaleWeight (z u) f := by
      funext x y
      rw [hughesYoungReducedCleanedShiftWeight_eq_staticScalar_mul_dfiCore]
      rw [hughesYoungDFICore_eq_scaledNormalization_mul_normalized
        hX0 hY0 (hApos u) ha hb T u (r : ℤ)]
      unfold dfiComplexScaleWeight
      dsimp only [z, f]
      ring
    have hzBound : ‖z u‖ ≤ B := by
      have hraw := ContinuousMap.norm_coe_le_norm (zMap.restrict K) ⟨u, hu⟩
      simpa only [B, zMap, K, ContinuousMap.restrict_apply] using hraw
    rw [hweight, dfiEquation27CentralSummand_scale, norm_mul]
    calc
      ‖z u‖ * ‖dfiEquation27CentralSummand a b r f q‖ ≤
          ‖z u‖ * (D * pseries q) :=
        mul_le_mul_of_nonneg_left hnormalized (norm_nonneg _)
      _ ≤ B * (D * pseries q) := by
        exact mul_le_mul_of_nonneg_right hzBound
          (mul_nonneg hD (by
            dsimp only [pseries]
            positivity))
      _ = (B * D) * pseries q := by ring
  have hcontinuousOn : ContinuousOn (fun u : ℝ =>
      ∑' q : ℕ, dfiEquation27CentralSummand a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ)) q) s := by
    exact continuousOn_tsum
      (fun q => (htermContinuous q).continuousOn) hmajor htermBound
  have hu₀s : u₀ ∈ s := by
    dsimp only [s]
    constructor <;> linarith
  have hsNhd : s ∈ 𝓝 u₀ := by
    dsimp only [s]
    exact Icc_mem_nhds (by linarith) (by linarith)
  unfold dfiEquation27CentralSeries
  simpa only [a, b] using (hcontinuousOn u₀ hu₀s).continuousAt hsNhd

/-- Continuity of the negative-shift branch after DFI's exact coordinate
swap.  The normalized source has one universal profile; the swapped profile
is its transpose, and the same summable modulus majorant applies. -/
theorem continuous_dfiEquation27CentralSeries_swappedReducedCleaned_ordinate
    {T c X Y P U : ℝ} {h k r : ℕ}
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hh : 0 < h) (hk : 0 < k)
    (hr : 0 < r) (hrY : (r : ℝ) ≤ Y / 2)
    (hP : 1 ≤ P) (hTR : T * ((r : ℝ) / Y) ≤ P)
    (hU : 0 < U) (hscale : U ≤ P⁻¹ * min X Y) :
    Continuous (fun u : ℝ =>
      dfiEquation27CentralSeries
        (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k) r
        (dfiSwapWeight
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k (-(r : ℤ))))) := by
  obtain ⟨Cγ, hCγ, hheight⟩ :=
    exists_norm_one_div_mul_iteratedDeriv_hughesYoungHeightTransform_le
  obtain ⟨Ccut, hCcut⟩ :=
    exists_uniform_hughesYoungDyadicCutoffAt_derivativeProfile
  obtain ⟨Cφ, hCφ⟩ := exists_dfiUniformRedundantCutoff_profile
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let A : ℝ → ℝ := hughesYoungSmallLineEnvelope Cγ T c
  let φ : ℝ → ℂ := dfiUniformRedundantCutoff U
  let hφ : DFIRedundantCutoff φ U := dfiUniformRedundantCutoff_spec U hU
  let Cf : ℕ → ℕ → ℝ := hughesYoungUniformDFIProfile Ccut
  let CfSwap : ℕ → ℕ → ℝ := fun i j => Cf j i
  let D : ℝ :=
    ‖(((b : ℂ) * a)⁻¹)‖ * (((b * a * r ^ 2 : ℕ) : ℝ)) *
      dfiEquation27CentralProfileConstant CfSwap Cφ *
      (1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 8) *
      (1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 8) * min Y X
  let pseries : ℕ → ℝ := fun q =>
    ((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ)
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hApos : ∀ u : ℝ, 0 < A u := fun u =>
    hughesYoungSmallLineEnvelope_pos
      (lt_of_lt_of_le zero_lt_one hT) hc u
  have hAcont : Continuous A :=
    continuous_hughesYoungSmallLineEnvelope Cγ T c
  have hφC : DFIRedundantCutoffProfile hφ Cφ := hCφ U hU
  have hscaleSwap : U ≤ P⁻¹ * min Y X := by
    simpa [min_comm] using hscale
  have hD : 0 ≤ D := by
    dsimp only [D, CfSwap, Cf, a, b]
    have hlogX : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith)
    have hlogY : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith)
    let f0 : ℝ → ℝ → ℂ :=
      hughesYoungScaledNormalizedDFICore T c 0 X Y (A 0) a b (-(r : ℤ))
    have hf0 : DFIEquation2 f0 P X Y := by
      dsimp only [f0]
      apply hughesYoungScaledNormalizedDFICore_equation2_unrestricted Ccut hCcut
        hT hc hc1 hX hY ha hb
      · simpa using hrY
      · exact hP
      · simpa [abs_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) by positivity)] using hTR
      · exact hApos 0
      · intro n xi
        simpa only [A, hughesYoungSmallLineEnvelope] using
          hheight T 0 c hT hc hc1 n xi
    have hfC0 : DFIEquation2Profile f0 P X Y
        (hughesYoungUniformDFIProfile Ccut) := by
      dsimp only [f0]
      apply hughesYoungScaledNormalizedDFICore_equation2Profile_unrestricted
        Ccut hCcut hT hc hc1 hX hY ha hb
      · simpa using hrY
      · exact hP
      · simpa [abs_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) by positivity)] using hTR
      · exact hApos 0
      · intro n xi
        simpa only [A, hughesYoungSmallLineEnvelope] using
          hheight T 0 c hT hc hc1 n xi
    have hprofile : 0 < dfiEquation27CentralProfileConstant
        (fun i j => hughesYoungUniformDFIProfile Ccut j i) Cφ :=
      dfiEquation27CentralProfileConstant_pos (hfC0.swap hf0) hφC
    positivity
  rw [continuous_iff_continuousAt]
  intro u₀
  let s : Set ℝ := Set.Icc (u₀ - 1) (u₀ + 1)
  let z : ℝ → ℂ := fun u =>
    hughesYoungLocalizedStaticScalar T h k *
      (hughesYoungScaledDFINormalization c u X Y (A u) a b : ℂ)
  have hzcont : Continuous z := by
    dsimp only [z]
    apply continuous_const.mul
    apply Complex.ofRealCLM.continuous.comp
    exact (((hAcont.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.pow 2)))).mul_const
        (((a : ℝ) / X) ^ ((1 / 2 : ℝ) + c))).mul_const
          (((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)))
  let zMap : C(ℝ, ℂ) := ⟨z, hzcont⟩
  let K : TopologicalSpace.Compacts ℝ := ⟨s, isCompact_Icc⟩
  let B : ℝ := ‖zMap.restrict K‖
  have hmajor : Summable (fun q : ℕ => (B * D) * pseries q) :=
    summable_natCast_inv_sq_mul_rpow_half.mul_left (B * D)
  have htermContinuous : ∀ q : ℕ, Continuous (fun u : ℝ =>
      dfiEquation27CentralSummand b a r
        (dfiSwapWeight
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k (-(r : ℤ)))) q) := by
    intro q
    simpa only [a, b] using
      continuous_dfiEquation27CentralSummand_swappedReducedCleaned_ordinate
        (lt_of_lt_of_le zero_lt_one hT) hc hX0 hY0 hh hk r q
  have htermBound : ∀ q : ℕ, ∀ u ∈ s,
      ‖dfiEquation27CentralSummand b a r
        (dfiSwapWeight
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k (-(r : ℤ)))) q‖ ≤
        (B * D) * pseries q := by
    intro q u hu
    let f : ℝ → ℝ → ℂ :=
      hughesYoungScaledNormalizedDFICore T c u X Y (A u) a b (-(r : ℤ))
    let g : ℝ → ℝ → ℂ := dfiSwapWeight f
    have hderiv : ∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A u) := by
      intro n xi
      simpa only [A, hughesYoungSmallLineEnvelope] using
        hheight T u c hT hc hc1 n xi
    have hf : DFIEquation2 f P X Y := by
      dsimp only [f]
      apply hughesYoungScaledNormalizedDFICore_equation2_unrestricted Ccut hCcut
        hT hc hc1 hX hY ha hb
      · simpa using hrY
      · exact hP
      · simpa [abs_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) by positivity)] using hTR
      · exact hApos u
      · exact hderiv
    have hfC : DFIEquation2Profile f P X Y Cf := by
      dsimp only [f, Cf]
      apply hughesYoungScaledNormalizedDFICore_equation2Profile_unrestricted
        Ccut hCcut hT hc hc1 hX hY ha hb
      · simpa using hrY
      · exact hP
      · simpa [abs_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) by positivity)] using hTR
      · exact hApos u
      · exact hderiv
    have hg : DFIEquation2 g P Y X := by
      dsimp only [g]
      exact hf.swap
    have hgC : DFIEquation2Profile g P Y X CfSwap := by
      dsimp only [g, CfSwap]
      exact hfC.swap hf
    have hgbox : DFILocalizedBox g Y X := by
      dsimp only [g]
      exact (hughesYoungScaledNormalizedDFICore_localizedBox
        hX0 hY0 a b (-(r : ℤ))).swap
    have hnormalized :
        ‖dfiEquation27CentralSummand b a r g q‖ ≤ D * pseries q := by
      rw [← dfiEquation27CentralSummand_localizedWeight_eq hφ b a r q]
      simpa only [D, pseries] using
        norm_dfiEquation27CentralSummand_le_profile_pseries
          hg hgC hgbox hφ hφC hscaleSwap b a r q hb ha hr
    have hweight :
        hughesYoungReducedCleanedShiftWeight T c u X Y h k (-(r : ℤ)) =
          dfiComplexScaleWeight (z u) f := by
      funext x y
      rw [hughesYoungReducedCleanedShiftWeight_eq_staticScalar_mul_dfiCore]
      rw [hughesYoungDFICore_eq_scaledNormalization_mul_normalized
        hX0 hY0 (hApos u) ha hb T u (-(r : ℤ))]
      unfold dfiComplexScaleWeight
      dsimp only [z, f]
      ring
    have hzBound : ‖z u‖ ≤ B := by
      have hraw := ContinuousMap.norm_coe_le_norm (zMap.restrict K) ⟨u, hu⟩
      simpa only [B, zMap, K, ContinuousMap.restrict_apply] using hraw
    rw [hweight, dfiSwapWeight_scale,
      dfiEquation27CentralSummand_scale, norm_mul]
    calc
      ‖z u‖ * ‖dfiEquation27CentralSummand b a r g q‖ ≤
          ‖z u‖ * (D * pseries q) :=
        mul_le_mul_of_nonneg_left hnormalized (norm_nonneg _)
      _ ≤ B * (D * pseries q) := by
        exact mul_le_mul_of_nonneg_right hzBound
          (mul_nonneg hD (by
            dsimp only [pseries]
            positivity))
      _ = (B * D) * pseries q := by ring
  have hcontinuousOn : ContinuousOn (fun u : ℝ =>
      ∑' q : ℕ, dfiEquation27CentralSummand b a r
        (dfiSwapWeight
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k (-(r : ℤ)))) q) s := by
    exact continuousOn_tsum
      (fun q => (htermContinuous q).continuousOn) hmajor htermBound
  have hu₀s : u₀ ∈ s := by
    dsimp only [s]
    constructor <;> linarith
  have hsNhd : s ∈ 𝓝 u₀ := by
    dsimp only [s]
    exact Icc_mem_nhds (by linarith) (by linarith)
  unfold dfiEquation27CentralSeries
  simpa only [a, b] using (hcontinuousOn u₀ hu₀s).continuousAt hsNhd

/-- The complete signed DFI equation-(27) central series for one nonzero
Hughes--Young shift is continuous in the Mellin ordinate.  Both sign
branches are discharged by the corresponding source-order theorem above;
no absolute value is taken across the signed main term. -/
theorem continuous_dfiSignedCentralSeries_reducedCleaned_ordinate
    {T c X Y P U : ℝ} {h k : ℕ} {r : ℤ}
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hh : 0 < h) (hk : 0 < k)
    (hr0 : r ≠ 0) (hrY : |(r : ℝ)| ≤ Y / 2)
    (hP : 1 ≤ P) (hTR : T * (|(r : ℝ)| / Y) ≤ P)
    (hU : 0 < U) (hscale : U ≤ P⁻¹ * min X Y) :
    Continuous (fun u : ℝ =>
      dfiSignedCentralSeries
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)) := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        by_contra hn0
        have : n = 0 := Nat.eq_zero_of_not_pos hn0
        subst n
        exact hr0 rfl
      have hnY : (n : ℝ) ≤ Y / 2 := by
        change |(n : ℝ)| ≤ Y / 2 at hrY
        simpa only [abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)] using hrY
      have hnTR : T * ((n : ℝ) / Y) ≤ P := by
        change T * (|(n : ℝ)| / Y) ≤ P at hTR
        simpa only [abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)] using hTR
      simpa only [dfiSignedCentralSeries_ofNat] using
        continuous_dfiEquation27CentralSeries_reducedCleaned_ordinate
          hT hc hc1 hX hY hh hk hn hnY hP hnTR hU hscale
  | negSucc n =>
      let q : ℕ := n + 1
      have hq : 0 < q := by dsimp only [q]; omega
      have hrEq : Int.negSucc n = -((q : ℕ) : ℤ) := by
        dsimp only [q]
        omega
      have hqY : (q : ℝ) ≤ Y / 2 := by
        rw [hrEq] at hrY
        simp only [Int.cast_neg, Int.cast_natCast] at hrY
        simpa only [abs_neg,
          abs_of_nonneg (show (0 : ℝ) ≤ (q : ℝ) by positivity)] using hrY
      have hqTR : T * ((q : ℝ) / Y) ≤ P := by
        rw [hrEq] at hTR
        simp only [Int.cast_neg, Int.cast_natCast] at hTR
        simpa only [abs_neg,
          abs_of_nonneg (show (0 : ℝ) ≤ (q : ℝ) by positivity)] using hTR
      rw [hrEq]
      simpa only [dfiSignedCentralSeries_neg_ofNat
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) q hq] using
        continuous_dfiEquation27CentralSeries_swappedReducedCleaned_ordinate
          hT hc hc1 hX hY hh hk hq hqY hP hqTR hU hscale

/-- A finite signed shift family retains continuity before the compact
Mellin integral is taken.  This is the analytic regularity required by the
cancellation-preserving Hughes--Young central term. -/
theorem continuous_sum_dfiSignedCentralSeries_reducedCleaned_ordinate
    {T c X Y P U : ℝ} {h k : ℕ} {s : Finset ℤ}
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hh : 0 < h) (hk : 0 < k)
    (hP : 1 ≤ P) (hU : 0 < U) (hscale : U ≤ P⁻¹ * min X Y)
    (hs : ∀ r ∈ s,
      r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧ T * (|(r : ℝ)| / Y) ≤ P) :
    Continuous (fun u : ℝ =>
      ∑ r ∈ s,
        dfiSignedCentralSeries
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)) := by
  exact continuous_finsetSum s fun r hr =>
    continuous_dfiSignedCentralSeries_reducedCleaned_ordinate
      hT hc hc1 hX hY hh hk
      (hs r hr).1 (hs r hr).2.1 hP (hs r hr).2.2 hU hscale

end RiemannZeta.GuthMaynard
