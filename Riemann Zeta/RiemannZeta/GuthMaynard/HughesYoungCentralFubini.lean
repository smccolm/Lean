import RiemannZeta.GuthMaynard.HughesYoungCentralBetaBridge
import RiemannZeta.GuthMaynard.HughesYoungCentralContinuity

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

set_option maxHeartbeats 4000000

namespace RiemannZeta.GuthMaynard

/-!
# Fubini for the Hughes--Young DFI central term

This is the missing analytic interchange between the height integral in
Hughes--Young (70) and the physical central integral in DFI (27).  The
interchange is proved from joint continuity and the two literal compact
supports; it is not an invocation of formal linearity for a possibly
non-integrable Bochner integral.
-/

/-- A localized logarithmic-power factor is jointly continuous when its
complex exponent varies continuously.  The cutoff kills the logarithmic
singularity uniformly in the parameter. -/
theorem continuous_uncurry_hughesYoungLocalizedOneFactor_parameter
    {α : Type*} [TopologicalSpace α] {X h : ℝ}
    (hX : 0 < X) (hh : 0 < h) {s : α → ℂ} (hs : Continuous s) :
    Continuous (fun p : α × ℝ =>
      hughesYoungLocalizedOneFactor X h (s p.1) p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hx : p.2 < X
  · have hmem : Prod.snd ⁻¹' Set.Iio X ∈ nhds p :=
      continuous_snd.continuousAt (Iio_mem_nhds hx)
    have heq : (fun z : α × ℝ =>
        hughesYoungLocalizedOneFactor X h (s z.1) z.2) =ᶠ[nhds p]
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
    have hlog : ContinuousAt (fun z : α × ℝ => Real.log (z.2 / h)) p :=
      (continuousAt_snd.div_const h).log hdiv0
    have hsAt : ContinuousAt (fun z : α × ℝ => s z.1) p :=
      hs.continuousAt.comp continuousAt_fst
    have hpow : ContinuousAt (fun z : α × ℝ =>
        hughesYoungLogPower (s z.1) (z.2 / h)) p := by
      unfold hughesYoungLogPower
      exact Complex.continuous_exp.continuousAt.comp
        (hsAt.neg.mul (Complex.ofRealCLM.continuous.continuousAt.comp hlog))
    unfold hughesYoungLocalizedOneFactor
    exact (Complex.ofRealCLM.continuous.continuousAt.comp
      ((contDiff_hughesYoungDyadicCutoffAt X).continuous.continuousAt.comp
        continuousAt_snd)).mul hpow

/-- The scalar independent of the physical divisor variables is continuous
in the height parameter. -/
theorem continuous_hughesYoungMellinScalar_height
    (T : ℝ) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Continuous (fun t : ℝ => hughesYoungMellinScalar T t c u h k) := by
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsH : Continuous (fun t : ℝ => (h : ℂ) ^ (-afeCriticalPoint t)) := by
    have he : Continuous (fun t : ℝ => -afeCriticalPoint t) := by
      unfold afeCriticalPoint
      fun_prop
    exact he.const_cpow (Or.inl hh0)
  have hsK : Continuous (fun t : ℝ => (k : ℂ) ^ (-afeCriticalPoint (-t))) := by
    have he : Continuous (fun t : ℝ => -afeCriticalPoint (-t)) := by
      unfold afeCriticalPoint
      fun_prop
    exact he.const_cpow (Or.inl hk0)
  unfold hughesYoungMellinScalar
  exact (((((continuous_const.mul hsH).mul continuous_const).mul hsK).mul
    continuous_const).mul
      (continuous_hughesYoungRightContourWeight_height hc u))

/-- Joint continuity in physical position and height of the exact reduced
Mellin weight on the positive shifted line. -/
theorem continuous_uncurry_hughesYoungReducedLocalizedMellinWeight_on_line_height
    (T : ℝ) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ) :
    Continuous (fun p : ℝ × ℝ =>
      hughesYoungReducedLocalizedMellinWeight T p.2 c u X Y h k
        p.1 (p.1 - (r : ℝ))) := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let a : ℝ := hughesYoungReducedLeft h k
  let b : ℝ := hughesYoungReducedRight h k
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast hughesYoungReducedLeft_pos hh
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast hughesYoungReducedRight_pos hh hk
  have hs1 : Continuous (fun t : ℝ => afeCriticalPoint t + w) := by
    unfold afeCriticalPoint
    fun_prop
  have hs2 : Continuous (fun t : ℝ => afeCriticalPoint (-t) + w) := by
    unfold afeCriticalPoint
    fun_prop
  have hfirst : Continuous (fun p : ℝ × ℝ =>
      hughesYoungLocalizedOneFactor X a (afeCriticalPoint p.2 + w) p.1) := by
    have hbase := continuous_uncurry_hughesYoungLocalizedOneFactor_parameter
      (α := ℝ) hX ha hs1
    simpa only [Prod.swap_prod_mk] using hbase.comp
      (continuous_snd.prodMk continuous_fst)
  have hsecond0 : Continuous (fun p : ℝ × ℝ =>
      hughesYoungLocalizedOneFactor Y b (afeCriticalPoint (-p.2) + w) p.1) := by
    have hbase := continuous_uncurry_hughesYoungLocalizedOneFactor_parameter
      (α := ℝ) hY hb hs2
    simpa only [Prod.swap_prod_mk] using hbase.comp
      (continuous_snd.prodMk continuous_fst)
  have hsecond : Continuous (fun p : ℝ × ℝ =>
      hughesYoungLocalizedOneFactor Y b (afeCriticalPoint (-p.2) + w)
        (p.1 - (r : ℝ))) := by
    simpa only [Function.comp_apply] using hsecond0.comp
      ((continuous_fst.sub continuous_const).prodMk continuous_snd)
  have hscalar : Continuous (fun p : ℝ × ℝ =>
      hughesYoungMellinScalar T p.2 c u h k) :=
    (continuous_hughesYoungMellinScalar_height T hc u hh hk).comp continuous_snd
  rw [show (fun p : ℝ × ℝ =>
      hughesYoungReducedLocalizedMellinWeight T p.2 c u X Y h k
        p.1 (p.1 - (r : ℝ))) = fun p =>
      hughesYoungMellinScalar T p.2 c u h k *
        (hughesYoungLocalizedOneFactor X a (afeCriticalPoint p.2 + w) p.1 *
          hughesYoungLocalizedOneFactor Y b (afeCriticalPoint (-p.2) + w)
            (p.1 - (r : ℝ))) by
    funext p
    unfold hughesYoungReducedLocalizedMellinWeight
      hughesYoungLocalizedLogKernel
    dsimp only [w, a, b]
    unfold hughesYoungLocalizedOneFactor
    ring]
  exact hscalar.mul (hfirst.mul hsecond)

/-- The joint physical/height integrand for one DFI equation-(27) central
integral. -/
noncomputable def hughesYoungCentralHeightIntegrand
    (T c u X Y : ℝ) (h k : ℕ) (r : ℤ)
    (a b qx qy : ℕ) (x t : ℝ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    dfiEquation27C a b qx qy
      (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)
      x (x - (r : ℝ))

/-- Joint continuity of the central height integrand. -/
theorem continuous_uncurry_hughesYoungCentralHeightIntegrand
    (T : ℝ) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ)
    (a b qx qy : ℕ) :
    Continuous (Function.uncurry
      (hughesYoungCentralHeightIntegrand T c u X Y h k r a b qx qy)) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hx : p.1 < X
  · have hmem : Prod.fst ⁻¹' Set.Iio X ∈ nhds p :=
      continuous_fst.continuousAt (Iio_mem_nhds hx)
    have heq : Function.uncurry
        (hughesYoungCentralHeightIntegrand T c u X Y h k r a b qx qy)
        =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hmem] with z hz
      change z.1 < X at hz
      have hcut : hughesYoungDyadicCutoffAt X z.1 = 0 :=
        hughesYoungDyadicCutoff_eq_zero_of_le_one ((div_le_one hX).2 hz.le)
      change hughesYoungCentralHeightIntegrand
        T c u X Y h k r a b qx qy z.1 z.2 = 0
      unfold hughesYoungCentralHeightIntegrand dfiEquation27C
        hughesYoungReducedLocalizedMellinWeight hughesYoungLocalizedLogKernel
      simp [hcut]
    exact continuousAt_const.congr_of_eventuallyEq heq
  · let y : ℝ := p.1 - (r : ℝ)
    by_cases hy : y < Y
    · have hymap : Continuous (fun z : ℝ × ℝ => z.1 - (r : ℝ)) :=
        continuous_fst.sub continuous_const
      have hmem : (fun z : ℝ × ℝ => z.1 - (r : ℝ)) ⁻¹' Set.Iio Y ∈ nhds p :=
        hymap.continuousAt (Iio_mem_nhds hy)
      have heq : Function.uncurry
          (hughesYoungCentralHeightIntegrand T c u X Y h k r a b qx qy)
          =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [hmem] with z hz
        change z.1 - (r : ℝ) < Y at hz
        have hcut : hughesYoungDyadicCutoffAt Y (z.1 - (r : ℝ)) = 0 :=
          hughesYoungDyadicCutoff_eq_zero_of_le_one ((div_le_one hY).2 hz.le)
        change hughesYoungCentralHeightIntegrand
          T c u X Y h k r a b qx qy z.1 z.2 = 0
        unfold hughesYoungCentralHeightIntegrand dfiEquation27C
          hughesYoungReducedLocalizedMellinWeight hughesYoungLocalizedLogKernel
        simp [hcut]
      exact continuousAt_const.congr_of_eventuallyEq heq
    · have hx0 : 0 < p.1 := hX.trans_le (le_of_not_gt hx)
      have hy0 : 0 < y := hY.trans_le (le_of_not_gt hy)
      have hweight : ContinuousAt (fun z : ℝ × ℝ =>
          hughesYoungReducedLocalizedMellinWeight T z.2 c u X Y h k
            z.1 (z.1 - (r : ℝ))) p :=
        (continuous_uncurry_hughesYoungReducedLocalizedMellinWeight_on_line_height
          T hc u hX hY hh hk r).continuousAt
      have hlogx : ContinuousAt (fun z : ℝ × ℝ => Real.log z.1) p :=
        continuousAt_fst.log hx0.ne'
      have hlogy : ContinuousAt (fun z : ℝ × ℝ =>
          Real.log (z.1 - (r : ℝ))) p :=
        (continuousAt_fst.sub continuousAt_const).log hy0.ne'
      have hfactorx : ContinuousAt (fun z : ℝ × ℝ =>
          (Real.log z.1 : ℂ) - Complex.log (a : ℂ) +
            2 * Real.eulerMascheroniConstant - 2 * Complex.log (qx : ℂ)) p := by
        fun_prop
      have hfactory : ContinuousAt (fun z : ℝ × ℝ =>
          (Real.log (z.1 - (r : ℝ)) : ℂ) - Complex.log (b : ℂ) +
            2 * Real.eulerMascheroniConstant - 2 * Complex.log (qy : ℂ)) p := by
        fun_prop
      have hheight : ContinuousAt (fun z : ℝ × ℝ =>
          (hughesYoungHeightWeight T z.2 : ℂ)) p :=
        Complex.ofRealCLM.continuous.continuousAt.comp
          ((contDiff_hughesYoungHeightWeight T).continuous.continuousAt.comp
            continuousAt_snd)
      unfold Function.uncurry hughesYoungCentralHeightIntegrand
        dfiEquation27C dfiEquation27LogFactor
      exact hheight.mul ((hfactorx.mul hfactory).mul hweight)

/-- The joint central height integrand is supported in the literal product
of the physical dyadic box and the physical height cutoff. -/
theorem support_uncurry_hughesYoungCentralHeightIntegrand_subset
    {T : ℝ} (hT : 0 < T) (c u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (r : ℤ) (a b qx qy : ℕ) :
    Function.support (Function.uncurry
      (hughesYoungCentralHeightIntegrand T c u X Y h k r a b qx qy)) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc (T / 4) (4 * T) := by
  intro p hp
  have hweight : hughesYoungReducedLocalizedMellinWeight T p.2 c u X Y h k
      p.1 (p.1 - (r : ℝ)) ≠ 0 := by
    intro hz
    apply hp
    unfold Function.uncurry hughesYoungCentralHeightIntegrand dfiEquation27C
    simp [hz]
  have hpair : (p.1, p.1 - (r : ℝ)) ∈
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
    support_uncurry_hughesYoungReducedLocalizedMellinWeight_subset
      T p.2 c u hX hY h k hweight
  have hheight : hughesYoungHeightWeight T p.2 ≠ 0 := by
    intro hz
    apply hp
    unfold Function.uncurry hughesYoungCentralHeightIntegrand
    simp [hz]
  exact ⟨hpair.1, hughesYoungHeightWeight_support hT hheight⟩

/-- The joint central height integrand is Bochner integrable on the product
measure, by joint continuity and its exact compact rectangle support. -/
theorem integrable_uncurry_hughesYoungCentralHeightIntegrand
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ)
    (a b qx qy : ℕ) :
    Integrable (Function.uncurry
      (hughesYoungCentralHeightIntegrand T c u X Y h k r a b qx qy)) := by
  exact (continuous_uncurry_hughesYoungCentralHeightIntegrand
    T hc u hX hY hh hk r a b qx qy).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc)
        (support_uncurry_hughesYoungCentralHeightIntegrand_subset
          hT c u hX hY h k r a b qx qy))

/-- Exact Fubini bridge for the positive-shift central integral.  The factor
`T⁻¹` is the normalization in Hughes--Young equation (70). -/
theorem dfiEquation27CentralIntegral_reducedCleaned_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℕ)
    (a b qx qy : ℕ) :
    dfiEquation27CentralIntegral a b qx qy
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ)) r =
      (1 / (T : ℂ)) * ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralIntegral a b qx qy
          (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) r := by
  let J : ℝ → ℝ → ℂ :=
    hughesYoungCentralHeightIntegrand T c u X Y h k (r : ℤ) a b qx qy
  have hJ : Integrable (Function.uncurry J) :=
    integrable_uncurry_hughesYoungCentralHeightIntegrand
      hT hc u hX hY hh hk (r : ℤ) a b qx qy
  have hpoint : ∀ x : ℝ,
      dfiEquation27C a b qx qy
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ))
          x (x - (r : ℝ)) =
        (1 / (T : ℂ)) * ∫ t : ℝ, J x t := by
    intro x
    by_cases hx : 0 < x
    · by_cases hy : 0 < x - (r : ℝ)
      · unfold dfiEquation27C
        rw [hughesYoungReducedCleanedShiftWeight_eq_heightIntegral
          T c u X Y hh hk hx hy (r := (r : ℤ)) (by norm_num)]
        let L : ℂ := dfiEquation27LogFactor a qx x *
          dfiEquation27LogFactor b qy (x - (r : ℝ))
        let F : ℝ → ℂ := fun t =>
          (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
              x (x - (r : ℝ))
        calc
          dfiEquation27LogFactor a qx x *
                dfiEquation27LogFactor b qy (x - (r : ℝ)) *
                ((1 / (T : ℂ)) * ∫ t : ℝ, F t) =
              (1 / (T : ℂ)) * (L * ∫ t : ℝ, F t) := by
            dsimp only [L]
            ring
          _ = (1 / (T : ℂ)) * ∫ t : ℝ, L * F t := by
            rw [MeasureTheory.integral_const_mul]
          _ = (1 / (T : ℂ)) * ∫ t : ℝ, J x t := by
            apply congrArg ((1 / (T : ℂ)) * ·)
            apply integral_congr_ae
            filter_upwards with t
            unfold J hughesYoungCentralHeightIntegrand F L dfiEquation27C
            simp only [Int.cast_natCast]
            ring
      · have hyLe : x - (r : ℝ) ≤ 0 := le_of_not_gt hy
        have hcut : hughesYoungDyadicCutoffAt Y (x - (r : ℝ)) = 0 := by
          apply hughesYoungDyadicCutoff_eq_zero_of_le_one
          exact (div_le_one hY).2 (hyLe.trans (le_of_lt hY))
        have hJx : (fun t : ℝ => J x t) = fun _ => 0 := by
          funext t
          unfold J hughesYoungCentralHeightIntegrand dfiEquation27C
            hughesYoungReducedLocalizedMellinWeight hughesYoungLocalizedLogKernel
          simp [hcut]
        have hleft : dfiEquation27C a b qx qy
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ))
            x (x - (r : ℝ)) = 0 := by
          unfold dfiEquation27C hughesYoungReducedCleanedShiftWeight
            hughesYoungReducedLocalizedStaticWeight hughesYoungLocalizedLogKernel
          simp [hcut]
        rw [hleft, hJx]
        simp
    · have hxLe : x ≤ 0 := le_of_not_gt hx
      have hcut : hughesYoungDyadicCutoffAt X x = 0 := by
        apply hughesYoungDyadicCutoff_eq_zero_of_le_one
        exact (div_le_one hX).2 (hxLe.trans (le_of_lt hX))
      have hJx : (fun t : ℝ => J x t) = fun _ => 0 := by
        funext t
        unfold J hughesYoungCentralHeightIntegrand dfiEquation27C
          hughesYoungReducedLocalizedMellinWeight hughesYoungLocalizedLogKernel
        simp [hcut]
      have hleft : dfiEquation27C a b qx qy
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ))
          x (x - (r : ℝ)) = 0 := by
        unfold dfiEquation27C hughesYoungReducedCleanedShiftWeight
          hughesYoungReducedLocalizedStaticWeight hughesYoungLocalizedLogKernel
        simp [hcut]
      rw [hleft, hJx]
      simp
  unfold dfiEquation27CentralIntegral
  rw [integral_congr_ae (Eventually.of_forall hpoint)]
  calc
    (∫ x : ℝ, (1 / (T : ℂ)) * ∫ t : ℝ, J x t) =
        (1 / (T : ℂ)) * ∫ x : ℝ, ∫ t : ℝ, J x t :=
      MeasureTheory.integral_const_mul _ _
    _ = (1 / (T : ℂ)) * ∫ t : ℝ, ∫ x : ℝ, J x t := by
      rw [MeasureTheory.integral_integral_swap hJ]
    _ = (1 / (T : ℂ)) * ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
          ∫ x : ℝ, dfiEquation27C a b qx qy
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)
            x (x - (r : ℝ)) := by
      apply congrArg ((1 / (T : ℂ)) * ·)
      apply integral_congr_ae
      filter_upwards with t
      unfold J hughesYoungCentralHeightIntegrand
      rw [MeasureTheory.integral_const_mul]
      simp only [Int.cast_natCast]

/-- Exact height-integral formula for one modulus of DFI equation (27).
The arithmetic factor is independent of height and is therefore moved
inside the integral without changing its cancellation. -/
theorem dfiEquation27CentralSummand_reducedCleaned_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r q : ℕ)
    (a b : ℕ) :
    dfiEquation27CentralSummand a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ)) q =
      (1 / (T : ℂ)) * ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralSummand a b r
          (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) q := by
  let A : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  unfold dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_reducedCleaned_eq_heightIntegral
    hT hc u hX hY hh hk r a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)]
  calc
    A * ((1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralIntegral a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) r) =
      (1 / (T : ℂ)) * (A * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralIntegral a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) r) := by
        ring
    _ = (1 / (T : ℂ)) * ∫ t : ℝ, A *
        ((hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralIntegral a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) r) := by
      rw [MeasureTheory.integral_const_mul]
    _ = (1 / (T : ℂ)) * ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        (A * dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) r) := by
      apply congrArg ((1 / (T : ℂ)) * ·)
      apply integral_congr_ae
      filter_upwards with t
      ring

end RiemannZeta.GuthMaynard
