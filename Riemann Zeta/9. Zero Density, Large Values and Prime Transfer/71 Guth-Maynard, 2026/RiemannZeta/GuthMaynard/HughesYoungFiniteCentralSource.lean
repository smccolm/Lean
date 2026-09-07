import RiemannZeta.GuthMaynard.HughesYoungCentralReassembly

open Complex MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Finite Hughes--Young central source

This module reassembles the complete finite dyadic rectangle before any
absolute value is taken.  Both endpoint corrections therefore remain in
the source weight that enters the Hughes--Young beta calculation.
-/

/-- The exact finite-depth signed central source at one Mellin and physical
height, with one common shift interval for the complete dyadic rectangle. -/
noncomputable def hughesYoungFiniteReassembledSignedCentralAtHeight
    (T t c u : ℝ) (h k a b K : ℕ) : ℂ :=
  let B := hughesYoungFullDyadicBound (K + 1)
  ∑ r ∈ hughesYoungShiftInterval a b B B,
    if r = 0 then 0 else
      dfiSignedCentralSeries a b r
        (hughesYoungFiniteReassembledReducedMellinWeight
          T t c u h k K)

/-- The signed central source for one positive dyadic box at one physical
height.  It is the literal finite shift interval from DFI equation (2), with
the zero shift omitted exactly as in the off-diagonal source. -/
noncomputable def hughesYoungFiniteBoxSignedCentralAtHeight
    (T t c u X Y : ℝ) (h k a b M N : ℕ) : ℂ :=
  ∑ r ∈ hughesYoungShiftInterval a b M N,
    if r = 0 then 0 else
      dfiSignedCentralSeries a b r
        (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)

/-- On a compact Mellin-ordinate interval, the base of every positive-scale
central kernel has one bound independent of the ordinate and of the two
integration variables.  This is the endpoint-safe replacement for the
large-box profile: it uses only positivity of the dyadic scales. -/
theorem exists_uniform_norm_hughesYoungCentralHeightBase_le_on_ordinateInterval
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Set.Icc (-H) H, ∀ t x : ℝ,
      ‖hughesYoungCentralHeightBase T t c u X Y h k r x‖ ≤ B := by
  let W : C(ℝ × ℝ, ℂ) :=
    ⟨fun p => hughesYoungRightContourWeight p.1 c p.2,
      continuous_uncurry_hughesYoungRightContourWeight hc⟩
  let K : TopologicalSpace.Compacts (ℝ × ℝ) :=
    ⟨Set.Icc (T / 4) (4 * T) ×ˢ Set.Icc (-H) H,
      isCompact_Icc.prod isCompact_Icc⟩
  let A : ℝ := ‖W.restrict K‖
  let B : ℝ := hughesYoungReducedStaticScale T c X Y h k * A
  have hA : 0 ≤ A := norm_nonneg _
  have hscale : 0 ≤ hughesYoungReducedStaticScale T c X Y h k :=
    hughesYoungReducedStaticScale_nonneg T c hX.le hY.le h k
  refine ⟨B, mul_nonneg hscale hA, ?_⟩
  intro u hu t x
  by_cases hz : hughesYoungCentralHeightBase T t c u X Y h k r x = 0
  · simp [hz, B, mul_nonneg hscale hA]
  · have hs := hughesYoungCentralHeightBase_mem_support_box
      hT c u hX hY h k r hz
    have hright : ‖hughesYoungRightContourWeight t c u‖ ≤ A := by
      have hmem : (t, u) ∈ (K : Set (ℝ × ℝ)) := ⟨hs.1, hu⟩
      have hraw := ContinuousMap.norm_coe_le_norm (W.restrict K) ⟨(t, u), hmem⟩
      simpa only [W, K, A, ContinuousMap.restrict_apply] using hraw
    have hstatic :
        ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k
            x (x - (r : ℝ))‖ ≤
          hughesYoungReducedStaticScale T c X Y h k :=
      norm_hughesYoungReducedLocalizedStaticWeight_le_scale
        hX hY hs.2.1.1 hs.2.2.1 hh hk hc
    have hheight :
        ‖hughesYoungHeightFourierInput T c u t‖ ≤ A := by
      rw [hughesYoungHeightFourierInput, norm_mul, norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg (hughesYoungHeightWeight_nonneg T t)]
      calc
        hughesYoungHeightWeight T t *
              ‖hughesYoungRightContourWeight t c u‖ ≤ 1 * A :=
          mul_le_mul (hughesYoungHeightWeight_le_one T t) hright
            (norm_nonneg _) (by norm_num)
        _ = A := one_mul A
    have hid :=
      heightWeight_mul_hughesYoungReducedLocalizedMellinWeight_eq_static_mul_phase
        T t c u X Y hh hk
          (hX.trans_le hs.2.1.1) (hY.trans_le hs.2.2.1)
    unfold hughesYoungCentralHeightBase
    rw [hid, norm_mul, norm_mul, Complex.norm_exp]
    have hphase :
        Real.exp
            ((((t * Real.log ((x - (r : ℝ)) / x) : ℝ) : ℂ) * I).re) = 1 := by
      simp
    rw [hphase, mul_one]
    simpa only [B] using
      (mul_le_mul hstatic hheight (norm_nonneg _) hscale)

/-- The complete positive equation-(27) height summands have one summable
modulus majorant uniformly on a compact Mellin-ordinate interval. -/
theorem exists_uniform_ordinate_norm_hughesYoungCentralSeriesHeightTerm_le
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u ∈ Set.Icc (-H) H, ∀ q t,
      ‖hughesYoungCentralSeriesHeightTerm
          T t c u X Y h k a b r q‖ ≤
        D * hughesYoungPositiveScaleCentralModulusProfile X Y a b q := by
  obtain ⟨B, hB, hbase⟩ :=
    exists_uniform_norm_hughesYoungCentralHeightBase_le_on_ordinateInterval
      hT hc H hX hY hh hk (r : ℤ)
  let D : ℝ := ‖(((a : ℂ) * b)⁻¹)‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * X * B
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro u hu q t
  by_cases hq₀ : q = 0
  · subst q
    simp [hughesYoungCentralSeriesHeightTerm,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient,
      hughesYoungPositiveScaleCentralModulusProfile]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq₀
    letI : NeZero q := ⟨hq₀⟩
    have hCoeff := norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
      a b r q ha hb hr
    have hIntegral :=
      norm_integral_hughesYoungCentralHeightKernel_le_positiveScale
        hT c u hX hY h k (a := a) (b := b) (r := r) (q := q)
          hq hB (hbase u hu) t
    rw [hughesYoungCentralSeriesHeightTerm_eq_integral_heightKernel]
    simp only [norm_mul]
    calc
      ‖(((a : ℂ) * b)⁻¹)‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ‖∫ x : ℝ,
            hughesYoungCentralHeightKernel T t c u X Y h k a b r q x‖ ≤
        ‖(((a : ℂ) * b)⁻¹)‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          (X * ((1 + |Real.log X| + Real.log 2 + |Real.log (a : ℝ)| +
            2 * |Real.eulerMascheroniConstant| + |Real.log Y| + Real.log 2 +
            |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
            2 * Real.log (q : ℝ)) ^ 2 * B)) := by
          gcongr
      _ = D * hughesYoungPositiveScaleCentralModulusProfile X Y a b q := by
        dsimp only [D, hughesYoungPositiveScaleCentralModulusProfile]
        ring

/-- Joint continuity in the Mellin ordinate and the physical variable of
the localized reduced source on a fixed positive-shift line. -/
theorem continuous_uncurry_hughesYoungReducedLocalizedMellinWeight_on_line_ordinate
    (T t : ℝ) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ) :
    Continuous (fun p : ℝ × ℝ =>
      hughesYoungReducedLocalizedMellinWeight T t c p.1 X Y h k
        p.2 (p.2 - (r : ℝ))) := by
  let a : ℝ := hughesYoungReducedLeft h k
  let b : ℝ := hughesYoungReducedRight h k
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast hughesYoungReducedLeft_pos hh
  have hb : 0 < b := by
    dsimp only [b]
    exact_mod_cast hughesYoungReducedRight_pos hh hk
  let s₁ : ℝ → ℂ := fun u =>
    afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)
  let s₂ : ℝ → ℂ := fun u =>
    afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)
  have hs₁ : Continuous s₁ := by
    dsimp only [s₁]
    fun_prop
  have hs₂ : Continuous s₂ := by
    dsimp only [s₂]
    fun_prop
  have hfirst : Continuous (fun p : ℝ × ℝ =>
      hughesYoungLocalizedOneFactor X a (s₁ p.1) p.2) :=
    continuous_uncurry_hughesYoungLocalizedOneFactor_parameter hX ha hs₁
  have hsecond₀ : Continuous (fun p : ℝ × ℝ =>
      hughesYoungLocalizedOneFactor Y b (s₂ p.1) p.2) :=
    continuous_uncurry_hughesYoungLocalizedOneFactor_parameter hY hb hs₂
  have hsecond : Continuous (fun p : ℝ × ℝ =>
      hughesYoungLocalizedOneFactor Y b (s₂ p.1)
        (p.2 - (r : ℝ))) := by
    simpa only [Function.comp_apply] using hsecond₀.comp
      (continuous_fst.prodMk (continuous_snd.sub continuous_const))
  have hright : Continuous (fun u : ℝ =>
      hughesYoungRightContourWeight t c u) := by
    simpa only [Function.uncurry_apply_pair] using
      (continuous_uncurry_hughesYoungRightContourWeight hc).comp
        ((continuous_const : Continuous (fun _u : ℝ => t)).prodMk
          continuous_id)
  have hscalar : Continuous (fun u : ℝ =>
      hughesYoungMellinScalar T t c u h k) := by
    unfold hughesYoungMellinScalar
    exact (((((continuous_const.mul continuous_const).mul
      continuous_const).mul continuous_const).mul continuous_const).mul hright)
  rw [show (fun p : ℝ × ℝ =>
      hughesYoungReducedLocalizedMellinWeight T t c p.1 X Y h k
        p.2 (p.2 - (r : ℝ))) = fun p =>
      hughesYoungMellinScalar T t c p.1 h k *
        (hughesYoungLocalizedOneFactor X a (s₁ p.1) p.2 *
          hughesYoungLocalizedOneFactor Y b (s₂ p.1)
            (p.2 - (r : ℝ))) by
      funext p
      unfold hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel hughesYoungLocalizedOneFactor
      dsimp only [a, b, s₁, s₂]
      ring]
  exact (hscalar.comp continuous_fst).mul (hfirst.mul hsecond)

/-- Joint continuity in ordinate and physical position of one fixed-modulus
positive central height kernel. -/
theorem continuous_uncurry_hughesYoungCentralHeightKernel_ordinate
    (T t : ℝ) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b r q : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      hughesYoungCentralHeightKernel T t c p.1 X Y h k a b r q p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hx : p.2 < X
  · have hmem : Prod.snd ⁻¹' Set.Iio X ∈ nhds p :=
      continuous_snd.continuousAt (Iio_mem_nhds hx)
    have heq : (fun z : ℝ × ℝ =>
        hughesYoungCentralHeightKernel T t c z.1 X Y h k a b r q z.2)
        =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hmem] with z hz
      have hcut : hughesYoungDyadicCutoffAt X z.2 = 0 :=
        hughesYoungDyadicCutoff_eq_zero_of_le_one
          ((div_le_one hX).2 hz.le)
      unfold hughesYoungCentralHeightKernel hughesYoungCentralHeightBase
        hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    exact continuousAt_const.congr_of_eventuallyEq heq
  · let y : ℝ := p.2 - (r : ℝ)
    by_cases hy : y < Y
    · have hymap : Continuous (fun z : ℝ × ℝ =>
          z.2 - (r : ℝ)) := continuous_snd.sub continuous_const
      have hmem : (fun z : ℝ × ℝ => z.2 - (r : ℝ)) ⁻¹'
          Set.Iio Y ∈ nhds p := hymap.continuousAt (Iio_mem_nhds hy)
      have heq : (fun z : ℝ × ℝ =>
          hughesYoungCentralHeightKernel T t c z.1 X Y h k a b r q z.2)
          =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [hmem] with z hz
        have hcut : hughesYoungDyadicCutoffAt Y (z.2 - (r : ℝ)) = 0 :=
          hughesYoungDyadicCutoff_eq_zero_of_le_one
            ((div_le_one hY).2 hz.le)
        unfold hughesYoungCentralHeightKernel hughesYoungCentralHeightBase
          hughesYoungReducedLocalizedMellinWeight
          hughesYoungLocalizedLogKernel
        simp [hcut]
      exact continuousAt_const.congr_of_eventuallyEq heq
    · have hx₀ : 0 < p.2 := hX.trans_le (le_of_not_gt hx)
      have hy₀ : 0 < y := hY.trans_le (le_of_not_gt hy)
      have hweight : ContinuousAt (fun z : ℝ × ℝ =>
          hughesYoungReducedLocalizedMellinWeight T t c z.1 X Y h k
            z.2 (z.2 - (r : ℝ))) p :=
        (continuous_uncurry_hughesYoungReducedLocalizedMellinWeight_on_line_ordinate
          T t hc hX hY hh hk (r : ℤ)).continuousAt
      have hlogx : ContinuousAt (fun z : ℝ × ℝ => Real.log z.2) p :=
        continuousAt_snd.log hx₀.ne'
      have hlogy : ContinuousAt (fun z : ℝ × ℝ =>
          Real.log (z.2 - (r : ℝ))) p :=
        (continuousAt_snd.sub continuousAt_const).log hy₀.ne'
      have hfactorx : ContinuousAt (fun z : ℝ × ℝ =>
          (Real.log z.2 : ℂ) - Complex.log (a : ℂ) +
            2 * Real.eulerMascheroniConstant -
              2 * Complex.log (dfiReducedDenominator a q : ℂ)) p := by
        fun_prop
      have hfactory : ContinuousAt (fun z : ℝ × ℝ =>
          (Real.log (z.2 - (r : ℝ)) : ℂ) - Complex.log (b : ℂ) +
            2 * Real.eulerMascheroniConstant -
              2 * Complex.log (dfiReducedDenominator b q : ℂ)) p := by
        fun_prop
      unfold hughesYoungCentralHeightKernel hughesYoungCentralHeightBase
        dfiEquation27LogFactor
      exact (hfactorx.mul hfactory).mul
        (continuousAt_const.mul hweight)

/-- Each fixed modulus contribution to the positive central height series
is continuous in the Mellin ordinate, including at the initial dyadic
scale. -/
theorem continuous_hughesYoungCentralSeriesHeightTerm_ordinate
    (T t : ℝ) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b r q : ℕ) :
    Continuous (fun u : ℝ =>
      hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q) := by
  let F : ℝ × ℝ → ℂ := fun p =>
    hughesYoungCentralHeightKernel T t c p.1 X Y h k a b r q p.2
  have hF : Continuous F := by
    simpa only [F] using
      continuous_uncurry_hughesYoungCentralHeightKernel_ordinate
        T t hc hX hY hh hk a b r q
  have hset : ∀ u : ℝ,
      (∫ x : ℝ, F (u, x)) = ∫ x in Set.Icc X (2 * X), F (u, x) := by
    intro u
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hweight : hughesYoungReducedLocalizedMellinWeight
        T t c u X Y h k x (x - (r : ℝ)) = 0 := by
      have hcut : hughesYoungDyadicCutoffAt X x = 0 := by
        by_contra hn
        exact hx (support_hughesYoungDyadicCutoffAt_subset hX hn)
      unfold hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    dsimp only [F]
    unfold hughesYoungCentralHeightKernel hughesYoungCentralHeightBase
    simp [hweight]
  rw [show (fun u : ℝ =>
      hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q) =
      fun u => (((a : ℂ) * b)⁻¹ *
          dfiEquation27ArithmeticCoefficient a b r q) *
        ∫ x in Set.Icc X (2 * X), F (u, x) by
      funext u
      rw [hughesYoungCentralSeriesHeightTerm_eq_integral_heightKernel]
      congr 1
      simpa only [F] using hset u]
  exact continuous_const.mul
    (continuous_parametric_integral_of_continuous hF isCompact_Icc)

/-- The positive central series at a fixed physical height is integrable in
the Mellin ordinate on every compact symmetric interval, with no large-box
hypothesis. -/
theorem intervalIntegrable_heightWeight_mul_dfiEquation27CentralSeries_ordinate
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) {H : ℝ} (hH : 0 ≤ H)
    (t : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    IntervalIntegrable (fun u : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralSeries a b r
          (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k))
      volume (-H) H := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_uniform_ordinate_norm_hughesYoungCentralSeriesHeightTerm_le
      hT hc H hX hY hh hk ha hb hr
  let g : ℕ → ℝ := fun q =>
    D * hughesYoungPositiveScaleCentralModulusProfile X Y a b q
  have hg : Summable g :=
    (summable_hughesYoungPositiveScaleCentralModulusProfile X Y a b).mul_left D
  have hcont : ContinuousOn (fun u : ℝ =>
      ∑' q : ℕ,
        hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q)
      (Set.Icc (-H) H) := by
    exact continuousOn_tsum
      (fun q => (continuous_hughesYoungCentralSeriesHeightTerm_ordinate
        T t hc hX hY hh hk a b r q).continuousOn)
      hg (fun q u hu => by
        simpa only [g] using hbound u hu q t)
  have hint : IntervalIntegrable (fun u : ℝ =>
      ∑' q : ℕ,
        hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q)
      volume (-H) H :=
    hcont.intervalIntegrable_of_Icc (by linarith [hH])
  simpa only [hughesYoungCentralSeriesHeightTerm,
    dfiEquation27CentralSeries, tsum_mul_left] using hint

/-- Coordinate-swapped compact-ordinate base bound for a negative signed
shift. -/
theorem exists_uniform_norm_hughesYoungNegativeCentralHeightBase_le_on_ordinateInterval
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Set.Icc (-H) H, ∀ t x : ℝ,
      ‖hughesYoungNegativeCentralHeightBase T t c u X Y h k r x‖ ≤ B := by
  let W : C(ℝ × ℝ, ℂ) :=
    ⟨fun p => hughesYoungRightContourWeight p.1 c p.2,
      continuous_uncurry_hughesYoungRightContourWeight hc⟩
  let K : TopologicalSpace.Compacts (ℝ × ℝ) :=
    ⟨Set.Icc (T / 4) (4 * T) ×ˢ Set.Icc (-H) H,
      isCompact_Icc.prod isCompact_Icc⟩
  let A : ℝ := ‖W.restrict K‖
  let B : ℝ := hughesYoungReducedStaticScale T c X Y h k * A
  have hA : 0 ≤ A := norm_nonneg _
  have hscale : 0 ≤ hughesYoungReducedStaticScale T c X Y h k :=
    hughesYoungReducedStaticScale_nonneg T c hX.le hY.le h k
  refine ⟨B, mul_nonneg hscale hA, ?_⟩
  intro u hu t x
  by_cases hz :
      hughesYoungNegativeCentralHeightBase T t c u X Y h k r x = 0
  · simp [hz, B, mul_nonneg hscale hA]
  · have hs := hughesYoungNegativeCentralHeightBase_mem_support_box
      hT c u hX hY h k r hz
    have hright : ‖hughesYoungRightContourWeight t c u‖ ≤ A := by
      have hmem : (t, u) ∈ (K : Set (ℝ × ℝ)) := ⟨hs.1, hu⟩
      have hraw := ContinuousMap.norm_coe_le_norm (W.restrict K) ⟨(t, u), hmem⟩
      simpa only [W, K, A, ContinuousMap.restrict_apply] using hraw
    have hstatic :
        ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k
            (x - (r : ℝ)) x‖ ≤
          hughesYoungReducedStaticScale T c X Y h k :=
      norm_hughesYoungReducedLocalizedStaticWeight_le_scale
        hX hY hs.2.1.1 hs.2.2.1 hh hk hc
    have hheight :
        ‖hughesYoungHeightFourierInput T c u t‖ ≤ A := by
      rw [hughesYoungHeightFourierInput, norm_mul, norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg (hughesYoungHeightWeight_nonneg T t)]
      calc
        hughesYoungHeightWeight T t *
              ‖hughesYoungRightContourWeight t c u‖ ≤ 1 * A :=
          mul_le_mul (hughesYoungHeightWeight_le_one T t) hright
            (norm_nonneg _) (by norm_num)
        _ = A := one_mul A
    have hid :=
      heightWeight_mul_hughesYoungReducedLocalizedMellinWeight_eq_static_mul_phase
        T t c u X Y hh hk
          (hX.trans_le hs.2.1.1) (hY.trans_le hs.2.2.1)
    unfold hughesYoungNegativeCentralHeightBase
    rw [hid, norm_mul, norm_mul, Complex.norm_exp]
    have hphase :
        Real.exp
            ((((t * Real.log (x / (x - (r : ℝ))) : ℝ) : ℂ) * I).re) = 1 := by
      simp
    rw [hphase, mul_one]
    simpa only [B] using
      (mul_le_mul hstatic hheight (norm_nonneg _) hscale)

/-- Uniform summable modulus profile for the negative central height
series on a compact ordinate interval. -/
theorem exists_uniform_ordinate_norm_hughesYoungNegativeCentralSeriesHeightTerm_le
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u ∈ Set.Icc (-H) H, ∀ q t,
      ‖hughesYoungNegativeCentralSeriesHeightTerm
          T t c u X Y h k a b r q‖ ≤
        D * hughesYoungPositiveScaleCentralModulusProfile Y X b a q := by
  obtain ⟨B, hB, hbase⟩ :=
    exists_uniform_norm_hughesYoungNegativeCentralHeightBase_le_on_ordinateInterval
      hT hc H hX hY hh hk (r : ℤ)
  let D : ℝ := ‖(((b : ℂ) * a)⁻¹)‖ *
    ((b * a * r ^ 2 : ℕ) : ℝ) * Y * B
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro u hu q t
  by_cases hq₀ : q = 0
  · subst q
    simp [hughesYoungNegativeCentralSeriesHeightTerm,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient,
      hughesYoungPositiveScaleCentralModulusProfile]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq₀
    letI : NeZero q := ⟨hq₀⟩
    have hCoeff := norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
      b a r q hb ha hr
    have hIntegral :=
      norm_integral_hughesYoungNegativeCentralHeightKernel_le_positiveScale
        hT c u hX hY h k (a := a) (b := b) (r := r) (q := q)
          hq hB (hbase u hu) t
    rw [hughesYoungNegativeCentralSeriesHeightTerm_eq_integral_heightKernel]
    simp only [norm_mul]
    calc
      ‖(((b : ℂ) * a)⁻¹)‖ *
          ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
          ‖∫ x : ℝ,
            hughesYoungNegativeCentralHeightKernel
              T t c u X Y h k a b r q x‖ ≤
        ‖(((b : ℂ) * a)⁻¹)‖ *
          (((b * a * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          (Y * ((1 + |Real.log Y| + Real.log 2 + |Real.log (b : ℝ)| +
            2 * |Real.eulerMascheroniConstant| + |Real.log X| + Real.log 2 +
            |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
            2 * Real.log (q : ℝ)) ^ 2 * B)) := by
          gcongr
      _ = D * hughesYoungPositiveScaleCentralModulusProfile Y X b a q := by
        dsimp only [D, hughesYoungPositiveScaleCentralModulusProfile]
        ring

/-- Joint ordinate/physical continuity of the coordinate-swapped localized
source used for a negative signed shift. -/
theorem continuous_uncurry_hughesYoungReducedLocalizedMellinWeight_negativeLine_ordinate
    (T t : ℝ) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      hughesYoungReducedLocalizedMellinWeight T t c p.1 X Y h k
        (p.2 - (r : ℝ)) p.2) := by
  have hbase :=
    continuous_uncurry_hughesYoungReducedLocalizedMellinWeight_on_line_ordinate
      T t hc hX hY hh hk (-(r : ℤ))
  have hmap : Continuous (fun p : ℝ × ℝ =>
      (p.1, p.2 - (r : ℝ))) :=
    continuous_fst.prodMk (continuous_snd.sub continuous_const)
  convert hbase.comp hmap using 1
  funext p
  simp only [Function.comp_apply, Int.cast_neg, Int.cast_natCast]
  congr 2
  ring

/-- Joint continuity in ordinate and physical position of one fixed-modulus
negative central height kernel. -/
theorem continuous_uncurry_hughesYoungNegativeCentralHeightKernel_ordinate
    (T t : ℝ) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b r q : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      hughesYoungNegativeCentralHeightKernel
        T t c p.1 X Y h k a b r q p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hx : p.2 < Y
  · have hmem : Prod.snd ⁻¹' Set.Iio Y ∈ nhds p :=
      continuous_snd.continuousAt (Iio_mem_nhds hx)
    have heq : (fun z : ℝ × ℝ =>
        hughesYoungNegativeCentralHeightKernel
          T t c z.1 X Y h k a b r q z.2) =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hmem] with z hz
      have hcut : hughesYoungDyadicCutoffAt Y z.2 = 0 :=
        hughesYoungDyadicCutoff_eq_zero_of_le_one
          ((div_le_one hY).2 hz.le)
      unfold hughesYoungNegativeCentralHeightKernel
        hughesYoungNegativeCentralHeightBase
        hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    exact continuousAt_const.congr_of_eventuallyEq heq
  · let y : ℝ := p.2 - (r : ℝ)
    by_cases hy : y < X
    · have hymap : Continuous (fun z : ℝ × ℝ =>
          z.2 - (r : ℝ)) := continuous_snd.sub continuous_const
      have hmem : (fun z : ℝ × ℝ => z.2 - (r : ℝ)) ⁻¹'
          Set.Iio X ∈ nhds p := hymap.continuousAt (Iio_mem_nhds hy)
      have heq : (fun z : ℝ × ℝ =>
          hughesYoungNegativeCentralHeightKernel
            T t c z.1 X Y h k a b r q z.2) =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [hmem] with z hz
        have hcut : hughesYoungDyadicCutoffAt X (z.2 - (r : ℝ)) = 0 :=
          hughesYoungDyadicCutoff_eq_zero_of_le_one
            ((div_le_one hX).2 hz.le)
        unfold hughesYoungNegativeCentralHeightKernel
          hughesYoungNegativeCentralHeightBase
          hughesYoungReducedLocalizedMellinWeight
          hughesYoungLocalizedLogKernel
        simp [hcut]
      exact continuousAt_const.congr_of_eventuallyEq heq
    · have hx₀ : 0 < p.2 := hY.trans_le (le_of_not_gt hx)
      have hy₀ : 0 < y := hX.trans_le (le_of_not_gt hy)
      have hweight : ContinuousAt (fun z : ℝ × ℝ =>
          hughesYoungReducedLocalizedMellinWeight T t c z.1 X Y h k
            (z.2 - (r : ℝ)) z.2) p :=
        (continuous_uncurry_hughesYoungReducedLocalizedMellinWeight_negativeLine_ordinate
          T t hc hX hY hh hk r).continuousAt
      have hlogx : ContinuousAt (fun z : ℝ × ℝ => Real.log z.2) p :=
        continuousAt_snd.log hx₀.ne'
      have hlogy : ContinuousAt (fun z : ℝ × ℝ =>
          Real.log (z.2 - (r : ℝ))) p :=
        (continuousAt_snd.sub continuousAt_const).log hy₀.ne'
      have hfactorx : ContinuousAt (fun z : ℝ × ℝ =>
          (Real.log z.2 : ℂ) - Complex.log (b : ℂ) +
            2 * Real.eulerMascheroniConstant -
              2 * Complex.log (dfiReducedDenominator b q : ℂ)) p := by
        fun_prop
      have hfactory : ContinuousAt (fun z : ℝ × ℝ =>
          (Real.log (z.2 - (r : ℝ)) : ℂ) - Complex.log (a : ℂ) +
            2 * Real.eulerMascheroniConstant -
              2 * Complex.log (dfiReducedDenominator a q : ℂ)) p := by
        fun_prop
      unfold hughesYoungNegativeCentralHeightKernel
        hughesYoungNegativeCentralHeightBase dfiEquation27LogFactor
      exact (hfactorx.mul hfactory).mul
        (continuousAt_const.mul hweight)

/-- Fixed-modulus continuity in the ordinate for the negative central
height series. -/
theorem continuous_hughesYoungNegativeCentralSeriesHeightTerm_ordinate
    (T t : ℝ) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b r q : ℕ) :
    Continuous (fun u : ℝ =>
      hughesYoungNegativeCentralSeriesHeightTerm
        T t c u X Y h k a b r q) := by
  let F : ℝ × ℝ → ℂ := fun p =>
    hughesYoungNegativeCentralHeightKernel
      T t c p.1 X Y h k a b r q p.2
  have hF : Continuous F := by
    simpa only [F] using
      continuous_uncurry_hughesYoungNegativeCentralHeightKernel_ordinate
        T t hc hX hY hh hk a b r q
  have hset : ∀ u : ℝ,
      (∫ x : ℝ, F (u, x)) = ∫ x in Set.Icc Y (2 * Y), F (u, x) := by
    intro u
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hweight : hughesYoungReducedLocalizedMellinWeight
        T t c u X Y h k (x - (r : ℝ)) x = 0 := by
      have hcut : hughesYoungDyadicCutoffAt Y x = 0 := by
        by_contra hn
        exact hx (support_hughesYoungDyadicCutoffAt_subset hY hn)
      unfold hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    dsimp only [F]
    unfold hughesYoungNegativeCentralHeightKernel
      hughesYoungNegativeCentralHeightBase
    simp [hweight]
  rw [show (fun u : ℝ =>
      hughesYoungNegativeCentralSeriesHeightTerm
        T t c u X Y h k a b r q) =
      fun u => (((b : ℂ) * a)⁻¹ *
          dfiEquation27ArithmeticCoefficient b a r q) *
        ∫ x in Set.Icc Y (2 * Y), F (u, x) by
      funext u
      rw [hughesYoungNegativeCentralSeriesHeightTerm_eq_integral_heightKernel]
      congr 1
      simpa only [F] using hset u]
  exact continuous_const.mul
    (continuous_parametric_integral_of_continuous hF isCompact_Icc)

/-- Compact-ordinate integrability of the complete negative central series
at a fixed physical height. -/
theorem intervalIntegrable_heightWeight_mul_dfiEquation27CentralSeries_swapped_ordinate
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) {H : ℝ} (hH : 0 ≤ H)
    (t : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    IntervalIntegrable (fun u : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralSeries b a r
          (dfiSwapWeight
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)))
      volume (-H) H := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_uniform_ordinate_norm_hughesYoungNegativeCentralSeriesHeightTerm_le
      hT hc H hX hY hh hk ha hb hr
  let g : ℕ → ℝ := fun q =>
    D * hughesYoungPositiveScaleCentralModulusProfile Y X b a q
  have hg : Summable g :=
    (summable_hughesYoungPositiveScaleCentralModulusProfile Y X b a).mul_left D
  have hcont : ContinuousOn (fun u : ℝ =>
      ∑' q : ℕ,
        hughesYoungNegativeCentralSeriesHeightTerm
          T t c u X Y h k a b r q) (Set.Icc (-H) H) := by
    exact continuousOn_tsum
      (fun q => (continuous_hughesYoungNegativeCentralSeriesHeightTerm_ordinate
        T t hc hX hY hh hk a b r q).continuousOn)
      hg (fun q u hu => by
        simpa only [g] using hbound u hu q t)
  have hint : IntervalIntegrable (fun u : ℝ =>
      ∑' q : ℕ,
        hughesYoungNegativeCentralSeriesHeightTerm
          T t c u X Y h k a b r q) volume (-H) H :=
    hcont.intervalIntegrable_of_Icc (by linarith [hH])
  simpa only [hughesYoungNegativeCentralSeriesHeightTerm,
    dfiEquation27CentralSeries, tsum_mul_left] using hint

/-- Compact-ordinate integrability for either sign of a nonzero central
shift at a fixed physical height. -/
theorem intervalIntegrable_heightWeight_mul_dfiSignedCentralSeries_ordinate
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) {H : ℝ} (hH : 0 ≤ H)
    (t : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) :
    IntervalIntegrable (fun u : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k))
      volume (-H) H := by
  by_cases hr₀ : 0 ≤ r
  · have hrNat : 0 < r.toNat := by omega
    simp only [dfiSignedCentralSeries, if_pos hr₀]
    exact intervalIntegrable_heightWeight_mul_dfiEquation27CentralSeries_ordinate
      hT hc hH t hX hY hh hk ha hb hrNat
  · have hrNat : 0 < (-r).toNat := by omega
    simp only [dfiSignedCentralSeries, if_neg hr₀]
    exact
      intervalIntegrable_heightWeight_mul_dfiEquation27CentralSeries_swapped_ordinate
        hT hc hH t hX hY hh hk ha hb hrNat

/-- The fully reassembled finite dyadic weight retains compact-ordinate
integrability before summing over shifts. -/
theorem intervalIntegrable_heightWeight_mul_dfiSignedCentralSeries_finiteReassembled
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) {H : ℝ} (hH : 0 ≤ H)
    (t : ℝ) {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) (K : ℕ) :
    IntervalIntegrable (fun u : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungFiniteReassembledReducedMellinWeight
            T t c u h k K)) volume (-H) H := by
  let S := hughesYoungCompleteDyadicRectangle K
  have hsum : IntervalIntegrable (fun u : ℝ =>
      ∑ ij ∈ S, (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungFullDyadicReducedMellinWeight
            T t c u h k ij.1 ij.2)) volume (-H) H := by
    have hraw := IntervalIntegrable.sum S fun ij _hij =>
        intervalIntegrable_heightWeight_mul_dfiSignedCentralSeries_ordinate
          hT hc hH t
            (hughesYoungFullDyadicScale_pos ij.1)
            (hughesYoungFullDyadicScale_pos ij.2)
            hh hk ha hb hr
    refine hraw.congr ?_
    intro u _hu
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro ij _hij
    rfl
  refine hsum.congr ?_
  intro u _hu
  change (∑ ij ∈ S, (hughesYoungHeightWeight T t : ℂ) *
      dfiSignedCentralSeries a b r
        (hughesYoungFullDyadicReducedMellinWeight
          T t c u h k ij.1 ij.2)) = _
  have hreassemble :=
    heightWeight_mul_dfiSignedCentralSeries_fullDyadic_finsetSum
      hT hc u t hh hk ha hb hr S
  rw [← hreassemble]
  congr 2
  funext x y
  simp only [S, hughesYoungCompleteDyadicRectangle,
    hughesYoungFiniteReassembledReducedMellinWeight]
  exact Finset.sum_product (Finset.range (K + 2))
    (Finset.range (K + 2))
    (fun ij => hughesYoungFullDyadicReducedMellinWeight
      T t c u h k ij.1 ij.2 x y)

/-- The complete finite signed shift family at a fixed height is integrable
in the Mellin ordinate. -/
theorem intervalIntegrable_heightWeight_mul_hughesYoungFiniteReassembledSignedCentralAtHeight
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) {H : ℝ} (hH : 0 ≤ H)
    (t : ℝ) {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    IntervalIntegrable (fun u : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteReassembledSignedCentralAtHeight
          T t c u h k a b K) volume (-H) H := by
  let B := hughesYoungFullDyadicBound (K + 1)
  let f : ℤ → ℝ → ℂ := fun r u =>
    if r = 0 then 0 else
      (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungFiniteReassembledReducedMellinWeight
            T t c u h k K)
  have hsum : IntervalIntegrable (fun u : ℝ =>
      ∑ r ∈ hughesYoungShiftInterval a b B B,
        if r = 0 then 0 else
          (hughesYoungHeightWeight T t : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungFiniteReassembledReducedMellinWeight
                T t c u h k K)) volume (-H) H := by
    have hraw : IntervalIntegrable
        (∑ r ∈ hughesYoungShiftInterval a b B B, f r)
        volume (-H) H :=
      IntervalIntegrable.sum (hughesYoungShiftInterval a b B B)
        fun r _hr => by
          by_cases hr₀ : r = 0
          · subst r
            simpa only [f, if_pos] using
              ((continuous_const : Continuous (fun _u : ℝ => (0 : ℂ))).intervalIntegrable
                (-H) H)
          · simpa only [f, hr₀, if_false] using
              intervalIntegrable_heightWeight_mul_dfiSignedCentralSeries_finiteReassembled
                hT hc hH t hh hk ha hb hr₀ K
    refine hraw.congr ?_
    intro u _hu
    simp only [Finset.sum_apply, f]
  refine hsum.congr ?_
  intro u _hu
  change (∑ r ∈ hughesYoungShiftInterval a b B B,
      if r = 0 then 0 else
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungFiniteReassembledReducedMellinWeight
              T t c u h k K)) =
    (hughesYoungHeightWeight T t : ℂ) *
      ∑ r ∈ hughesYoungShiftInterval a b B B,
        if r = 0 then 0 else
          dfiSignedCentralSeries a b r
            (hughesYoungFiniteReassembledReducedMellinWeight
              T t c u h k K)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hr₀ : r = 0 <;> simp [hr₀]

/-- Joint continuity in Mellin ordinate, physical height, and physical
position of the positive-line reduced source.  The parameter ordering is
`((u,t),x)`, matching the product measure used below. -/
theorem continuous_hughesYoungReducedLocalizedMellinWeight_ordinate_height_position
    (T : ℝ) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ) :
    Continuous (fun p : (ℝ × ℝ) × ℝ =>
      hughesYoungReducedLocalizedMellinWeight T p.1.2 c p.1.1 X Y h k
        p.2 (p.2 - (r : ℝ))) := by
  let a : ℝ := hughesYoungReducedLeft h k
  let b : ℝ := hughesYoungReducedRight h k
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast hughesYoungReducedLeft_pos hh
  have hb : 0 < b := by
    dsimp only [b]
    exact_mod_cast hughesYoungReducedRight_pos hh hk
  let s₁ : ℝ × ℝ → ℂ := fun p =>
    afeCriticalPoint p.2 + ((c : ℂ) + (p.1 : ℂ) * I)
  let s₂ : ℝ × ℝ → ℂ := fun p =>
    afeCriticalPoint (-p.2) + ((c : ℂ) + (p.1 : ℂ) * I)
  have hs₁ : Continuous s₁ := by
    unfold s₁ afeCriticalPoint
    fun_prop
  have hs₂ : Continuous s₂ := by
    unfold s₂ afeCriticalPoint
    fun_prop
  have hfirst : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      hughesYoungLocalizedOneFactor X a (s₁ p.1) p.2) :=
    continuous_uncurry_hughesYoungLocalizedOneFactor_parameter hX ha hs₁
  have hsecond₀ : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      hughesYoungLocalizedOneFactor Y b (s₂ p.1) p.2) :=
    continuous_uncurry_hughesYoungLocalizedOneFactor_parameter hY hb hs₂
  have hsecond : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      hughesYoungLocalizedOneFactor Y b (s₂ p.1)
        (p.2 - (r : ℝ))) := by
    simpa only [Function.comp_apply] using hsecond₀.comp
      (continuous_fst.prodMk (continuous_snd.sub continuous_const))
  have hh₀ : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hk₀ : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpowH : Continuous (fun p : ℝ × ℝ =>
      (h : ℂ) ^ (-afeCriticalPoint p.2)) := by
    have he : Continuous (fun p : ℝ × ℝ =>
        -afeCriticalPoint p.2) := by unfold afeCriticalPoint; fun_prop
    exact he.const_cpow (Or.inl hh₀)
  have hpowK : Continuous (fun p : ℝ × ℝ =>
      (k : ℂ) ^ (-afeCriticalPoint (-p.2))) := by
    have he : Continuous (fun p : ℝ × ℝ =>
        -afeCriticalPoint (-p.2)) := by unfold afeCriticalPoint; fun_prop
    exact he.const_cpow (Or.inl hk₀)
  have hright : Continuous (fun p : ℝ × ℝ =>
      hughesYoungRightContourWeight p.2 c p.1) := by
    simpa only [Function.uncurry_apply_pair] using
      (continuous_uncurry_hughesYoungRightContourWeight hc).comp
        (continuous_snd.prodMk continuous_fst)
  have hscalar : Continuous (fun p : ℝ × ℝ =>
      hughesYoungMellinScalar T p.2 c p.1 h k) := by
    unfold hughesYoungMellinScalar
    exact (((((continuous_const.mul hpowH).mul continuous_const).mul
      hpowK).mul continuous_const).mul hright)
  rw [show (fun p : (ℝ × ℝ) × ℝ =>
      hughesYoungReducedLocalizedMellinWeight T p.1.2 c p.1.1 X Y h k
        p.2 (p.2 - (r : ℝ))) = fun p =>
      hughesYoungMellinScalar T p.1.2 c p.1.1 h k *
        (hughesYoungLocalizedOneFactor X a (s₁ p.1) p.2 *
          hughesYoungLocalizedOneFactor Y b (s₂ p.1)
            (p.2 - (r : ℝ))) by
      funext p
      unfold hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel hughesYoungLocalizedOneFactor
      dsimp only [a, b, s₁, s₂]
      ring]
  exact (hscalar.comp continuous_fst).mul (hfirst.mul hsecond)

/-- Joint continuity of a positive fixed-modulus central height kernel in
`((u,t),x)`. -/
theorem continuous_hughesYoungCentralHeightKernel_ordinate_height_position
    (T : ℝ) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b r q : ℕ) :
    Continuous (fun p : (ℝ × ℝ) × ℝ =>
      hughesYoungCentralHeightKernel
        T p.1.2 c p.1.1 X Y h k a b r q p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hx : p.2 < X
  · have hmem : Prod.snd ⁻¹' Set.Iio X ∈ nhds p :=
      continuous_snd.continuousAt (Iio_mem_nhds hx)
    have heq : (fun z : (ℝ × ℝ) × ℝ =>
        hughesYoungCentralHeightKernel
          T z.1.2 c z.1.1 X Y h k a b r q z.2) =ᶠ[nhds p]
          fun _ => 0 := by
      filter_upwards [hmem] with z hz
      have hcut : hughesYoungDyadicCutoffAt X z.2 = 0 :=
        hughesYoungDyadicCutoff_eq_zero_of_le_one
          ((div_le_one hX).2 hz.le)
      unfold hughesYoungCentralHeightKernel hughesYoungCentralHeightBase
        hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    exact continuousAt_const.congr_of_eventuallyEq heq
  · let y : ℝ := p.2 - (r : ℝ)
    by_cases hy : y < Y
    · have hymap : Continuous (fun z : (ℝ × ℝ) × ℝ =>
          z.2 - (r : ℝ)) := continuous_snd.sub continuous_const
      have hmem : (fun z : (ℝ × ℝ) × ℝ =>
          z.2 - (r : ℝ)) ⁻¹' Set.Iio Y ∈ nhds p :=
        hymap.continuousAt (Iio_mem_nhds hy)
      have heq : (fun z : (ℝ × ℝ) × ℝ =>
          hughesYoungCentralHeightKernel
            T z.1.2 c z.1.1 X Y h k a b r q z.2) =ᶠ[nhds p]
            fun _ => 0 := by
        filter_upwards [hmem] with z hz
        have hcut : hughesYoungDyadicCutoffAt Y (z.2 - (r : ℝ)) = 0 :=
          hughesYoungDyadicCutoff_eq_zero_of_le_one
            ((div_le_one hY).2 hz.le)
        unfold hughesYoungCentralHeightKernel hughesYoungCentralHeightBase
          hughesYoungReducedLocalizedMellinWeight
          hughesYoungLocalizedLogKernel
        simp [hcut]
      exact continuousAt_const.congr_of_eventuallyEq heq
    · have hx₀ : 0 < p.2 := hX.trans_le (le_of_not_gt hx)
      have hy₀ : 0 < y := hY.trans_le (le_of_not_gt hy)
      have hweight : ContinuousAt
          (fun z : (ℝ × ℝ) × ℝ =>
            hughesYoungReducedLocalizedMellinWeight
              T z.1.2 c z.1.1 X Y h k z.2 (z.2 - (r : ℝ))) p :=
        (continuous_hughesYoungReducedLocalizedMellinWeight_ordinate_height_position
          T hc hX hY hh hk (r : ℤ)).continuousAt
      have hfactorx : ContinuousAt
          (fun z : (ℝ × ℝ) × ℝ =>
            (Real.log z.2 : ℂ) - Complex.log (a : ℂ) +
              2 * Real.eulerMascheroniConstant -
                2 * Complex.log (dfiReducedDenominator a q : ℂ)) p := by
        have hlog := continuousAt_snd.log hx₀.ne'
        fun_prop
      have hfactory : ContinuousAt
          (fun z : (ℝ × ℝ) × ℝ =>
            (Real.log (z.2 - (r : ℝ)) : ℂ) - Complex.log (b : ℂ) +
              2 * Real.eulerMascheroniConstant -
                2 * Complex.log (dfiReducedDenominator b q : ℂ)) p := by
        have hlog :=
          (continuousAt_snd.sub continuousAt_const).log hy₀.ne'
        fun_prop
      have hheight : ContinuousAt
          (fun z : (ℝ × ℝ) × ℝ =>
            (hughesYoungHeightWeight T z.1.2 : ℂ)) p := by
        exact Complex.ofRealCLM.continuous.continuousAt.comp
          ((contDiff_hughesYoungHeightWeight T).continuous.continuousAt.comp
            (continuousAt_snd.comp continuousAt_fst))
      unfold hughesYoungCentralHeightKernel hughesYoungCentralHeightBase
        dfiEquation27LogFactor
      exact (hfactorx.mul hfactory).mul (hheight.mul hweight)

/-- Joint continuity of one positive fixed-modulus central-series height
term in `(u,t)`. -/
theorem continuous_hughesYoungCentralSeriesHeightTerm_ordinate_height
    (T : ℝ) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b r q : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      hughesYoungCentralSeriesHeightTerm
        T p.2 c p.1 X Y h k a b r q) := by
  let F : (ℝ × ℝ) × ℝ → ℂ := fun p =>
    hughesYoungCentralHeightKernel
      T p.1.2 c p.1.1 X Y h k a b r q p.2
  have hF : Continuous F := by
    simpa only [F] using
      continuous_hughesYoungCentralHeightKernel_ordinate_height_position
        T hc hX hY hh hk a b r q
  have hset : ∀ p : ℝ × ℝ,
      (∫ x : ℝ, F (p, x)) = ∫ x in Set.Icc X (2 * X), F (p, x) := by
    intro p
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hweight : hughesYoungReducedLocalizedMellinWeight
        T p.2 c p.1 X Y h k x (x - (r : ℝ)) = 0 := by
      have hcut : hughesYoungDyadicCutoffAt X x = 0 := by
        by_contra hn
        exact hx (support_hughesYoungDyadicCutoffAt_subset hX hn)
      unfold hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    dsimp only [F]
    unfold hughesYoungCentralHeightKernel hughesYoungCentralHeightBase
    simp [hweight]
  rw [show (fun p : ℝ × ℝ =>
      hughesYoungCentralSeriesHeightTerm
        T p.2 c p.1 X Y h k a b r q) =
      fun p => (((a : ℂ) * b)⁻¹ *
          dfiEquation27ArithmeticCoefficient a b r q) *
        ∫ x in Set.Icc X (2 * X), F (p, x) by
      funext p
      rw [hughesYoungCentralSeriesHeightTerm_eq_integral_heightKernel]
      congr 1
      simpa only [F] using hset p]
  exact continuous_const.mul
    (continuous_parametric_integral_of_continuous hF isCompact_Icc)

/-- Uniform convergence makes the complete positive central series jointly
continuous on the compact ordinate-height rectangle. -/
theorem continuousOn_heightWeight_mul_dfiEquation27CentralSeries_ordinate_height
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        dfiEquation27CentralSeries a b r
          (hughesYoungReducedLocalizedMellinWeight
            T p.2 c p.1 X Y h k))
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_uniform_ordinate_norm_hughesYoungCentralSeriesHeightTerm_le
      hT hc H hX hY hh hk ha hb hr
  let g : ℕ → ℝ := fun q =>
    D * hughesYoungPositiveScaleCentralModulusProfile X Y a b q
  have hg : Summable g :=
    (summable_hughesYoungPositiveScaleCentralModulusProfile X Y a b).mul_left D
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      ∑' q : ℕ,
        hughesYoungCentralSeriesHeightTerm
          T p.2 c p.1 X Y h k a b r q)
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
    exact continuousOn_tsum
      (fun q => (continuous_hughesYoungCentralSeriesHeightTerm_ordinate_height
        T hc hX hY hh hk a b r q).continuousOn)
      hg (fun q p hp => by
        simpa only [g] using hbound p.1 hp.1 q p.2)
  simpa only [hughesYoungCentralSeriesHeightTerm,
    dfiEquation27CentralSeries, tsum_mul_left] using hcont

/-- Joint `(u,t,x)` continuity for the coordinate-swapped negative line. -/
theorem continuous_hughesYoungReducedLocalizedMellinWeight_negativeLine_ordinate_height_position
    (T : ℝ) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℕ) :
    Continuous (fun p : (ℝ × ℝ) × ℝ =>
      hughesYoungReducedLocalizedMellinWeight T p.1.2 c p.1.1 X Y h k
        (p.2 - (r : ℝ)) p.2) := by
  have hbase :=
    continuous_hughesYoungReducedLocalizedMellinWeight_ordinate_height_position
      T hc hX hY hh hk (-(r : ℤ))
  have hmap : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      (p.1, p.2 - (r : ℝ))) :=
    continuous_fst.prodMk (continuous_snd.sub continuous_const)
  convert hbase.comp hmap using 1
  funext p
  simp only [Function.comp_apply, Int.cast_neg, Int.cast_natCast]
  congr 2
  ring

/-- Joint continuity of a negative fixed-modulus central height kernel in
`((u,t),x)`. -/
theorem continuous_hughesYoungNegativeCentralHeightKernel_ordinate_height_position
    (T : ℝ) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b r q : ℕ) :
    Continuous (fun p : (ℝ × ℝ) × ℝ =>
      hughesYoungNegativeCentralHeightKernel
        T p.1.2 c p.1.1 X Y h k a b r q p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hx : p.2 < Y
  · have hmem : Prod.snd ⁻¹' Set.Iio Y ∈ nhds p :=
      continuous_snd.continuousAt (Iio_mem_nhds hx)
    have heq : (fun z : (ℝ × ℝ) × ℝ =>
        hughesYoungNegativeCentralHeightKernel
          T z.1.2 c z.1.1 X Y h k a b r q z.2) =ᶠ[nhds p]
          fun _ => 0 := by
      filter_upwards [hmem] with z hz
      have hcut : hughesYoungDyadicCutoffAt Y z.2 = 0 :=
        hughesYoungDyadicCutoff_eq_zero_of_le_one
          ((div_le_one hY).2 hz.le)
      unfold hughesYoungNegativeCentralHeightKernel
        hughesYoungNegativeCentralHeightBase
        hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    exact continuousAt_const.congr_of_eventuallyEq heq
  · let y : ℝ := p.2 - (r : ℝ)
    by_cases hy : y < X
    · have hymap : Continuous (fun z : (ℝ × ℝ) × ℝ =>
          z.2 - (r : ℝ)) := continuous_snd.sub continuous_const
      have hmem : (fun z : (ℝ × ℝ) × ℝ =>
          z.2 - (r : ℝ)) ⁻¹' Set.Iio X ∈ nhds p :=
        hymap.continuousAt (Iio_mem_nhds hy)
      have heq : (fun z : (ℝ × ℝ) × ℝ =>
          hughesYoungNegativeCentralHeightKernel
            T z.1.2 c z.1.1 X Y h k a b r q z.2) =ᶠ[nhds p]
            fun _ => 0 := by
        filter_upwards [hmem] with z hz
        have hcut : hughesYoungDyadicCutoffAt X (z.2 - (r : ℝ)) = 0 :=
          hughesYoungDyadicCutoff_eq_zero_of_le_one
            ((div_le_one hX).2 hz.le)
        unfold hughesYoungNegativeCentralHeightKernel
          hughesYoungNegativeCentralHeightBase
          hughesYoungReducedLocalizedMellinWeight
          hughesYoungLocalizedLogKernel
        simp [hcut]
      exact continuousAt_const.congr_of_eventuallyEq heq
    · have hx₀ : 0 < p.2 := hY.trans_le (le_of_not_gt hx)
      have hy₀ : 0 < y := hX.trans_le (le_of_not_gt hy)
      have hweight : ContinuousAt
          (fun z : (ℝ × ℝ) × ℝ =>
            hughesYoungReducedLocalizedMellinWeight T z.1.2 c z.1.1 X Y h k
              (z.2 - (r : ℝ)) z.2) p :=
        (continuous_hughesYoungReducedLocalizedMellinWeight_negativeLine_ordinate_height_position
          T hc hX hY hh hk r).continuousAt
      have hfactorx : ContinuousAt
          (fun z : (ℝ × ℝ) × ℝ =>
            (Real.log z.2 : ℂ) - Complex.log (b : ℂ) +
              2 * Real.eulerMascheroniConstant -
                2 * Complex.log (dfiReducedDenominator b q : ℂ)) p := by
        have hlog := continuousAt_snd.log hx₀.ne'
        fun_prop
      have hfactory : ContinuousAt
          (fun z : (ℝ × ℝ) × ℝ =>
            (Real.log (z.2 - (r : ℝ)) : ℂ) - Complex.log (a : ℂ) +
              2 * Real.eulerMascheroniConstant -
                2 * Complex.log (dfiReducedDenominator a q : ℂ)) p := by
        have hlog :=
          (continuousAt_snd.sub continuousAt_const).log hy₀.ne'
        fun_prop
      have hheight : ContinuousAt
          (fun z : (ℝ × ℝ) × ℝ =>
            (hughesYoungHeightWeight T z.1.2 : ℂ)) p :=
        Complex.ofRealCLM.continuous.continuousAt.comp
          ((contDiff_hughesYoungHeightWeight T).continuous.continuousAt.comp
            (continuousAt_snd.comp continuousAt_fst))
      unfold hughesYoungNegativeCentralHeightKernel
        hughesYoungNegativeCentralHeightBase dfiEquation27LogFactor
      exact (hfactorx.mul hfactory).mul (hheight.mul hweight)

/-- Joint continuity of one negative fixed-modulus central-series height
term in `(u,t)`. -/
theorem continuous_hughesYoungNegativeCentralSeriesHeightTerm_ordinate_height
    (T : ℝ) {c : ℝ} (hc : 0 < c)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b r q : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      hughesYoungNegativeCentralSeriesHeightTerm
        T p.2 c p.1 X Y h k a b r q) := by
  let F : (ℝ × ℝ) × ℝ → ℂ := fun p =>
    hughesYoungNegativeCentralHeightKernel
      T p.1.2 c p.1.1 X Y h k a b r q p.2
  have hF : Continuous F := by
    simpa only [F] using
      continuous_hughesYoungNegativeCentralHeightKernel_ordinate_height_position
        T hc hX hY hh hk a b r q
  have hset : ∀ p : ℝ × ℝ,
      (∫ x : ℝ, F (p, x)) = ∫ x in Set.Icc Y (2 * Y), F (p, x) := by
    intro p
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hweight : hughesYoungReducedLocalizedMellinWeight
        T p.2 c p.1 X Y h k (x - (r : ℝ)) x = 0 := by
      have hcut : hughesYoungDyadicCutoffAt Y x = 0 := by
        by_contra hn
        exact hx (support_hughesYoungDyadicCutoffAt_subset hY hn)
      unfold hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    dsimp only [F]
    unfold hughesYoungNegativeCentralHeightKernel
      hughesYoungNegativeCentralHeightBase
    simp [hweight]
  rw [show (fun p : ℝ × ℝ =>
      hughesYoungNegativeCentralSeriesHeightTerm
        T p.2 c p.1 X Y h k a b r q) =
      fun p => (((b : ℂ) * a)⁻¹ *
          dfiEquation27ArithmeticCoefficient b a r q) *
        ∫ x in Set.Icc Y (2 * Y), F (p, x) by
      funext p
      rw [hughesYoungNegativeCentralSeriesHeightTerm_eq_integral_heightKernel]
      congr 1
      simpa only [F] using hset p]
  exact continuous_const.mul
    (continuous_parametric_integral_of_continuous hF isCompact_Icc)

/-- Uniform convergence makes the complete negative central series jointly
continuous on the compact ordinate-height rectangle. -/
theorem continuousOn_heightWeight_mul_dfiEquation27CentralSeries_swapped_ordinate_height
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        dfiEquation27CentralSeries b a r
          (dfiSwapWeight
            (hughesYoungReducedLocalizedMellinWeight
              T p.2 c p.1 X Y h k)))
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_uniform_ordinate_norm_hughesYoungNegativeCentralSeriesHeightTerm_le
      hT hc H hX hY hh hk ha hb hr
  let g : ℕ → ℝ := fun q =>
    D * hughesYoungPositiveScaleCentralModulusProfile Y X b a q
  have hg : Summable g :=
    (summable_hughesYoungPositiveScaleCentralModulusProfile Y X b a).mul_left D
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      ∑' q : ℕ,
        hughesYoungNegativeCentralSeriesHeightTerm
          T p.2 c p.1 X Y h k a b r q)
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
    exact continuousOn_tsum
      (fun q =>
        (continuous_hughesYoungNegativeCentralSeriesHeightTerm_ordinate_height
          T hc hX hY hh hk a b r q).continuousOn)
      hg (fun q p hp => by
        simpa only [g] using hbound p.1 hp.1 q p.2)
  simpa only [hughesYoungNegativeCentralSeriesHeightTerm,
    dfiEquation27CentralSeries, tsum_mul_left] using hcont

/-- Joint continuity on the compact source rectangle for either sign of a
nonzero central shift. -/
theorem continuousOn_heightWeight_mul_dfiSignedCentralSeries_ordinate_height
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungReducedLocalizedMellinWeight
            T p.2 c p.1 X Y h k))
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
  by_cases hr₀ : 0 ≤ r
  · have hrNat : 0 < r.toNat := by omega
    simp only [dfiSignedCentralSeries, if_pos hr₀]
    exact
      continuousOn_heightWeight_mul_dfiEquation27CentralSeries_ordinate_height
        hT hc H hX hY hh hk ha hb hrNat
  · have hrNat : 0 < (-r).toNat := by omega
    simp only [dfiSignedCentralSeries, if_neg hr₀]
    exact
      continuousOn_heightWeight_mul_dfiEquation27CentralSeries_swapped_ordinate_height
        hT hc H hX hY hh hk ha hb hrNat

/-- Joint continuity of one nonzero shift after finite dyadic reassembly. -/
theorem continuousOn_heightWeight_mul_dfiSignedCentralSeries_finiteReassembled
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) (K : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungFiniteReassembledReducedMellinWeight
            T p.2 c p.1 h k K))
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
  let S := hughesYoungCompleteDyadicRectangle K
  have hsum : ContinuousOn (fun p : ℝ × ℝ =>
      ∑ ij ∈ S, (hughesYoungHeightWeight T p.2 : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungFullDyadicReducedMellinWeight
            T p.2 c p.1 h k ij.1 ij.2))
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
    exact continuousOn_finsetSum S fun ij _hij =>
      continuousOn_heightWeight_mul_dfiSignedCentralSeries_ordinate_height
        hT hc H
          (hughesYoungFullDyadicScale_pos ij.1)
          (hughesYoungFullDyadicScale_pos ij.2)
          hh hk ha hb hr
  refine hsum.congr ?_
  intro p hp
  change (hughesYoungHeightWeight T p.2 : ℂ) *
      dfiSignedCentralSeries a b r
        (hughesYoungFiniteReassembledReducedMellinWeight
          T p.2 c p.1 h k K) =
    ∑ ij ∈ S, (hughesYoungHeightWeight T p.2 : ℂ) *
      dfiSignedCentralSeries a b r
        (hughesYoungFullDyadicReducedMellinWeight
          T p.2 c p.1 h k ij.1 ij.2)
  have hreassemble :=
    heightWeight_mul_dfiSignedCentralSeries_fullDyadic_finsetSum
      hT hc p.1 p.2 hh hk ha hb hr S
  rw [show hughesYoungFiniteReassembledReducedMellinWeight
      T p.2 c p.1 h k K = fun x y => ∑ ij ∈ S,
        hughesYoungFullDyadicReducedMellinWeight
          T p.2 c p.1 h k ij.1 ij.2 x y by
      funext x y
      simp only [S, hughesYoungCompleteDyadicRectangle,
        hughesYoungFiniteReassembledReducedMellinWeight]
      exact (Finset.sum_product (Finset.range (K + 2))
        (Finset.range (K + 2))
        (fun ij => hughesYoungFullDyadicReducedMellinWeight
          T p.2 c p.1 h k ij.1 ij.2 x y)).symm]
  exact hreassemble

/-- Joint continuity of the complete finite signed central source on its
compact ordinate-height rectangle. -/
theorem continuousOn_heightWeight_mul_hughesYoungFiniteReassembledSignedCentralAtHeight
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        hughesYoungFiniteReassembledSignedCentralAtHeight
          T p.2 c p.1 h k a b K)
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
  let B := hughesYoungFullDyadicBound (K + 1)
  have hsum : ContinuousOn (fun p : ℝ × ℝ =>
      ∑ r ∈ hughesYoungShiftInterval a b B B,
        if r = 0 then 0 else
          (hughesYoungHeightWeight T p.2 : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungFiniteReassembledReducedMellinWeight
                T p.2 c p.1 h k K))
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
    apply continuousOn_finsetSum (hughesYoungShiftInterval a b B B)
    intro r _hr
    by_cases hr₀ : r = 0
    · subst r
      simp only [if_pos]
      exact continuousOn_const
    · simp only [hr₀, if_false]
      exact
        continuousOn_heightWeight_mul_dfiSignedCentralSeries_finiteReassembled
          hT hc H hh hk ha hb hr₀ K
  refine hsum.congr ?_
  intro p hp
  change (hughesYoungHeightWeight T p.2 : ℂ) *
      (∑ r ∈ hughesYoungShiftInterval a b B B,
        if r = 0 then 0 else
          dfiSignedCentralSeries a b r
            (hughesYoungFiniteReassembledReducedMellinWeight
              T p.2 c p.1 h k K)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hr₀ : r = 0 <;> simp [hr₀]

/-- At a fixed nonzero shift, the full finite dyadic family of cleaned
central series is exactly the physical-height integral of the reassembled
finite endpoint weight. -/
theorem sum_completeDyadicRectangle_signedCentral_cleaned_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) (K : ℕ) :
    (∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
      dfiSignedCentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k r)) =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungFiniteReassembledReducedMellinWeight
              T t c u h k K) := by
  let S := hughesYoungCompleteDyadicRectangle K
  calc
    (∑ ij ∈ S,
        dfiSignedCentralSeries a b r
          (hughesYoungReducedCleanedShiftWeight T c u
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k r)) =
        ∑ ij ∈ S, (1 / (T : ℂ)) * ∫ t : ℝ,
          (hughesYoungHeightWeight T t : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungFullDyadicReducedMellinWeight
                T t c u h k ij.1 ij.2) := by
      apply Finset.sum_congr rfl
      intro ij _hij
      exact dfiSignedCentralSeries_reducedCleaned_eq_heightIntegral_positiveScale
        hT hc u (hughesYoungFullDyadicScale_pos ij.1)
          (hughesYoungFullDyadicScale_pos ij.2) hh hk ha hb hr
    _ = (1 / (T : ℂ)) * ∑ ij ∈ S, ∫ t : ℝ,
          (hughesYoungHeightWeight T t : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungFullDyadicReducedMellinWeight
                T t c u h k ij.1 ij.2) := by
      rw [Finset.mul_sum]
    _ = (1 / (T : ℂ)) * ∫ t : ℝ, ∑ ij ∈ S,
          (hughesYoungHeightWeight T t : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungFullDyadicReducedMellinWeight
                T t c u h k ij.1 ij.2) := by
      congr 1
      symm
      apply MeasureTheory.integral_finsetSum
      intro ij _hij
      exact integrable_heightWeight_mul_dfiSignedCentralSeries_positiveScale
        hT hc u (hughesYoungFullDyadicScale_pos ij.1)
          (hughesYoungFullDyadicScale_pos ij.2) hh hk ha hb hr
    _ = (1 / (T : ℂ)) * ∫ t : ℝ,
          (hughesYoungHeightWeight T t : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungFiniteReassembledReducedMellinWeight
                T t c u h k K) := by
      apply congrArg ((1 / (T : ℂ)) * ·)
      apply integral_congr_ae
      filter_upwards with t
      have hreassemble :=
        heightWeight_mul_dfiSignedCentralSeries_fullDyadic_finsetSum
          hT hc u t hh hk ha hb hr S
      rw [← hreassemble]
      congr 2
      funext x y
      simp only [S, hughesYoungCompleteDyadicRectangle,
        hughesYoungFiniteReassembledReducedMellinWeight]
      exact Finset.sum_product (Finset.range (K + 2))
        (Finset.range (K + 2))
        (fun ij => hughesYoungFullDyadicReducedMellinWeight
          T t c u h k ij.1 ij.2 x y)

/-- After every localized box is enlarged to the one common shift interval,
the complete finite dyadic rectangle is exactly the height integral of the
reassembled signed source.  This is the cancellation-preserving finite
counterpart of the passage from Hughes--Young (83) to (85). -/
theorem sum_completeDyadicRectangle_finiteCompleteBox_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (K : ℕ) :
    (∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
      hughesYoungFiniteCompleteSignedCentralBox T c u
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2)) =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteReassembledSignedCentralAtHeight
            T t c u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) K := by
  classical
  let S := hughesYoungCompleteDyadicRectangle K
  let B := hughesYoungFullDyadicBound (K + 1)
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hbox (ij : ℕ × ℕ) (hij : ij ∈ S) :
      hughesYoungFiniteCompleteSignedCentralBox T c u
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k a b
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2) =
        ∑ r ∈ hughesYoungShiftInterval a b B B,
          if r = 0 then 0 else
            dfiSignedCentralSeries a b r
              (hughesYoungReducedCleanedShiftWeight T c u
                (hughesYoungFullDyadicScale ij.1)
                (hughesYoungFullDyadicScale ij.2) h k r) := by
    have hij' : ij ∈ (Finset.range (K + 2)).product
        (Finset.range (K + 2)) := by
      simpa only [S, hughesYoungCompleteDyadicRectangle] using hij
    have hi : ij.1 < K + 2 :=
      Finset.mem_range.mp (Finset.mem_product.mp hij').1
    have hj : ij.2 < K + 2 :=
      Finset.mem_range.mp (Finset.mem_product.mp hij').2
    exact hughesYoungFiniteCompleteSignedCentralBox_eq_enlarged
      T c u (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k a b
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2) B
        (hughesYoungFullDyadicScale_pos ij.1)
        (hughesYoungFullDyadicScale_pos ij.2) ha hb
        (two_mul_hughesYoungFullDyadicScale_le_bound ij.1)
        (two_mul_hughesYoungFullDyadicScale_le_bound ij.2)
        (hughesYoungFullDyadicBound_le_terminal hi)
        (hughesYoungFullDyadicBound_le_terminal hj)
  have hIntReassembled (r : ℤ) (hr : r ≠ 0) :
      Integrable (fun t : ℝ =>
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungFiniteReassembledReducedMellinWeight
              T t c u h k K)) := by
    have hsum : Integrable (fun t : ℝ => ∑ ij ∈ S,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungFullDyadicReducedMellinWeight
              T t c u h k ij.1 ij.2)) := by
      exact integrable_finsetSum S (fun ij _hij =>
        integrable_heightWeight_mul_dfiSignedCentralSeries_positiveScale
          hT hc u (hughesYoungFullDyadicScale_pos ij.1)
            (hughesYoungFullDyadicScale_pos ij.2) hh hk ha hb hr)
    refine hsum.congr ?_
    filter_upwards with t
    have hreassemble :=
      heightWeight_mul_dfiSignedCentralSeries_fullDyadic_finsetSum
        hT hc u t hh hk ha hb hr S
    rw [← hreassemble]
    congr 2
    funext x y
    simp only [S, hughesYoungCompleteDyadicRectangle,
      hughesYoungFiniteReassembledReducedMellinWeight]
    exact Finset.sum_product (Finset.range (K + 2))
      (Finset.range (K + 2))
      (fun ij => hughesYoungFullDyadicReducedMellinWeight
        T t c u h k ij.1 ij.2 x y)
  calc
    (∑ ij ∈ S,
        hughesYoungFiniteCompleteSignedCentralBox T c u
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k a b
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)) =
        ∑ ij ∈ S, ∑ r ∈ hughesYoungShiftInterval a b B B,
          if r = 0 then 0 else
            dfiSignedCentralSeries a b r
              (hughesYoungReducedCleanedShiftWeight T c u
                (hughesYoungFullDyadicScale ij.1)
                (hughesYoungFullDyadicScale ij.2) h k r) := by
      apply Finset.sum_congr rfl
      intro ij hij
      exact hbox ij hij
    _ = ∑ r ∈ hughesYoungShiftInterval a b B B, ∑ ij ∈ S,
          if r = 0 then 0 else
            dfiSignedCentralSeries a b r
              (hughesYoungReducedCleanedShiftWeight T c u
                (hughesYoungFullDyadicScale ij.1)
                (hughesYoungFullDyadicScale ij.2) h k r) := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ hughesYoungShiftInterval a b B B,
          if r = 0 then 0 else
            (1 / (T : ℂ)) * ∫ t : ℝ,
              (hughesYoungHeightWeight T t : ℂ) *
                dfiSignedCentralSeries a b r
                  (hughesYoungFiniteReassembledReducedMellinWeight
                    T t c u h k K) := by
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hr0 : r = 0
      · simp [hr0]
      · simp only [hr0, if_false]
        exact sum_completeDyadicRectangle_signedCentral_cleaned_eq_heightIntegral
          hT hc u hh hk ha hb hr0 K
    _ = (1 / (T : ℂ)) * ∑ r ∈ hughesYoungShiftInterval a b B B,
          if r = 0 then 0 else ∫ t : ℝ,
            (hughesYoungHeightWeight T t : ℂ) *
              dfiSignedCentralSeries a b r
                (hughesYoungFiniteReassembledReducedMellinWeight
                  T t c u h k K) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hr0 : r = 0 <;> simp [hr0]
    _ = (1 / (T : ℂ)) * ∫ t : ℝ,
          ∑ r ∈ hughesYoungShiftInterval a b B B,
            if r = 0 then 0 else
              (hughesYoungHeightWeight T t : ℂ) *
                dfiSignedCentralSeries a b r
                  (hughesYoungFiniteReassembledReducedMellinWeight
                    T t c u h k K) := by
      congr 1
      rw [MeasureTheory.integral_finsetSum
        (hughesYoungShiftInterval a b B B)]
      · apply Finset.sum_congr rfl
        intro r _hr
        by_cases hr0 : r = 0
        · simp [hr0]
        · simp only [hr0, if_false]
      · intro r _hr
        by_cases hr0 : r = 0
        · simp [hr0]
        · simpa only [hr0, if_false] using hIntReassembled r hr0
    _ = (1 / (T : ℂ)) * ∫ t : ℝ,
          (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungFiniteReassembledSignedCentralAtHeight
              T t c u h k a b K := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      unfold hughesYoungFiniteReassembledSignedCentralAtHeight
      simp only [B, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hr0 : r = 0 <;> simp [hr0]

/-- The cancellation-preserving finite central source is jointly integrable
on a bounded Mellin-ordinate interval and the full physical-height line.
The latter is harmless because the Hughes--Young height weight is compactly
supported in `[T / 4, 4 * T]`. -/
theorem integrable_uncurry_heightWeight_mul_hughesYoungFiniteReassembledSignedCentralAtHeight
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) {H : ℝ} (hH : 0 ≤ H)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (K : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        hughesYoungFiniteReassembledSignedCentralAtHeight
          T p.2 c p.1 h k
            (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) K)
      ((volume.restrict (Set.uIoc (-H) H)).prod volume) := by
  let f : ℝ × ℝ → ℂ := fun p =>
    (hughesYoungHeightWeight T p.2 : ℂ) *
      hughesYoungFiniteReassembledSignedCentralAtHeight
        T p.2 c p.1 h k
          (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) K
  let C : Set (ℝ × ℝ) :=
    Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)
  have hcontinuous : ContinuousOn f C := by
    dsimp only [f, C]
    exact
      continuousOn_heightWeight_mul_hughesYoungFiniteReassembledSignedCentralAtHeight
        hT hc H hh hk (hughesYoungReducedLeft_pos hh)
          (hughesYoungReducedRight_pos hh hk) K
  have hcompact : IsCompact C := isCompact_Icc.prod isCompact_Icc
  have hsmall : IntegrableOn f C (volume.prod volume) :=
    hcontinuous.integrableOn_compact hcompact
  have hbig : IntegrableOn f
      (Set.uIoc (-H) H ×ˢ Set.univ) (volume.prod volume) := by
    apply hsmall.of_forall_diff_eq_zero
      (measurableSet_uIoc.prod MeasurableSet.univ)
    intro p hp
    have ht : p.2 ∉ Set.Icc (T / 4) (4 * T) := by
      intro hp2
      apply hp.2
      have hp1 : p.1 ∈ Set.Icc (-H) H := by
        have hu := Set.uIoc_subset_uIcc hp.1.1
        simpa only [Set.uIcc_of_le (by linarith : -H ≤ H)] using hu
      exact ⟨hp1, hp2⟩
    have hzero : hughesYoungHeightWeight T p.2 = 0 := by
      by_contra hne
      exact ht (hughesYoungHeightWeight_support hT hne)
    dsimp only [f]
    simp [hzero]
  rw [IntegrableOn, ← Measure.prod_restrict] at hbig
  simpa [f] using hbig

/-- Fubini's theorem for the fully reassembled finite central source.  This
keeps all shifts and both dyadic endpoints inside the integral until after
the cancellation has occurred. -/
theorem intervalIntegral_integral_hughesYoungFiniteReassembledSignedCentralAtHeight_swap
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) {H : ℝ} (hH : 0 ≤ H)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (K : ℕ) :
    (∫ u in -H..H, ∫ t : ℝ,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteReassembledSignedCentralAtHeight
          T t c u h k
            (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) K) =
      ∫ t : ℝ, ∫ u in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteReassembledSignedCentralAtHeight
            T t c u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) K := by
  exact intervalIntegral_integral_swap
    (integrable_uncurry_heightWeight_mul_hughesYoungFiniteReassembledSignedCentralAtHeight
      hT hc hH hh hk K)

/-- The complete finite dyadic central contribution, integrated over the
small Mellin line, is exactly the height integral of the interval-integrated
reassembled signed source.  This is the finite, endpoint-faithful form in
which the DFI source-line calculation must be entered. -/
theorem intervalIntegral_sum_completeDyadicRectangle_finiteCompleteBox_eq
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) {H : ℝ} (hH : 0 ≤ H)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (K : ℕ) :
    (∫ u in -H..H,
      ∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
        hughesYoungFiniteCompleteSignedCentralBox T c u
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)) =
      (1 / (T : ℂ)) * ∫ t : ℝ, ∫ u in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteReassembledSignedCentralAtHeight
            T t c u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) K := by
  let F : ℝ → ℂ := fun u =>
    ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungFiniteReassembledSignedCentralAtHeight
        T t c u h k
          (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) K
  calc
    (∫ u in -H..H,
        ∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
          hughesYoungFiniteCompleteSignedCentralBox T c u
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2)) =
        ∫ u in -H..H, (1 / (T : ℂ)) * F u := by
      apply intervalIntegral.integral_congr
      intro u _hu
      exact sum_completeDyadicRectangle_finiteCompleteBox_eq_heightIntegral
        hT hc u hh hk K
    _ = (1 / (T : ℂ)) * ∫ u in -H..H, F u := by
      rw [intervalIntegral.integral_const_mul]
    _ = (1 / (T : ℂ)) * ∫ t : ℝ, ∫ u in -H..H,
          (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungFiniteReassembledSignedCentralAtHeight
              T t c u h k
                (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) K := by
      apply congrArg ((1 / (T : ℂ)) * ·)
      exact
        intervalIntegral_integral_hughesYoungFiniteReassembledSignedCentralAtHeight_swap
          hT hc hH hh hk K

/-! ## Boxwise integrability without large-DFI hypotheses -/

/-- On every positive scale, the literal finite complete central box is the
physical-height integral of its signed source.  This version deliberately has
no near/far cutoff and therefore needs none of the large-DFI scale hypotheses. -/
theorem hughesYoungFiniteCompleteSignedCentralBox_eq_heightIntegral_positiveScale
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b M N : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) :
    hughesYoungFiniteCompleteSignedCentralBox T c u X Y h k a b M N =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteBoxSignedCentralAtHeight
            T t c u X Y h k a b M N := by
  classical
  let S := hughesYoungShiftInterval a b M N
  have hterm (r : ℤ) (hr : r ≠ 0) :
      dfiSignedCentralSeries a b r
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) =
        (1 / (T : ℂ)) * ∫ t : ℝ,
          (hughesYoungHeightWeight T t : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) :=
    dfiSignedCentralSeries_reducedCleaned_eq_heightIntegral_positiveScale
      hT hc u hX hY hh hk ha hb hr
  have hint (r : ℤ) (hr : r ≠ 0) :
      Integrable (fun t : ℝ =>
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) :=
    integrable_heightWeight_mul_dfiSignedCentralSeries_positiveScale
      hT hc u hX hY hh hk ha hb hr
  unfold hughesYoungFiniteCompleteSignedCentralBox
  calc
    (∑ r ∈ S, if r = 0 then 0 else
        dfiSignedCentralSeries a b r
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)) =
        ∑ r ∈ S, if r = 0 then 0 else
          (1 / (T : ℂ)) * ∫ t : ℝ,
            (hughesYoungHeightWeight T t : ℂ) *
              dfiSignedCentralSeries a b r
                (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) := by
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hr0 : r = 0
      · simp [hr0]
      · simp only [hr0, if_false]
        exact hterm r hr0
    _ = (1 / (T : ℂ)) * ∑ r ∈ S, if r = 0 then 0 else
          ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hr0 : r = 0 <;> simp [hr0]
    _ = (1 / (T : ℂ)) * ∫ t : ℝ,
          ∑ r ∈ S, if r = 0 then 0 else
            (hughesYoungHeightWeight T t : ℂ) *
              dfiSignedCentralSeries a b r
                (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) := by
      congr 1
      rw [MeasureTheory.integral_finsetSum S]
      · apply Finset.sum_congr rfl
        intro r _hr
        by_cases hr0 : r = 0 <;> simp [hr0]
      · intro r _hr
        by_cases hr0 : r = 0
        · simp [hr0]
        · simpa only [hr0, if_false] using hint r hr0
    _ = (1 / (T : ℂ)) * ∫ t : ℝ,
          (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungFiniteBoxSignedCentralAtHeight
              T t c u X Y h k a b M N := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      unfold hughesYoungFiniteBoxSignedCentralAtHeight
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hr0 : r = 0 <;> simp [hr0]

/-- Joint continuity of one finite complete-box signed source on the compact
Mellin-ordinate/height rectangle. -/
theorem continuousOn_heightWeight_mul_hughesYoungFiniteBoxSignedCentralAtHeight
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b M N : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        hughesYoungFiniteBoxSignedCentralAtHeight
          T p.2 c p.1 X Y h k a b M N)
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
  classical
  unfold hughesYoungFiniteBoxSignedCentralAtHeight
  have hdistrib : (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        ∑ r ∈ hughesYoungShiftInterval a b M N,
          if r = 0 then 0 else
            dfiSignedCentralSeries a b r
              (hughesYoungReducedLocalizedMellinWeight
                T p.2 c p.1 X Y h k)) =
      fun p => ∑ r ∈ hughesYoungShiftInterval a b M N,
        if r = 0 then 0 else
          (hughesYoungHeightWeight T p.2 : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungReducedLocalizedMellinWeight
                T p.2 c p.1 X Y h k) := by
    funext p
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    by_cases hr0 : r = 0 <;> simp [hr0]
  rw [hdistrib]
  apply continuousOn_finsetSum (hughesYoungShiftInterval a b M N)
  intro r _hr
  by_cases hr0 : r = 0
  · subst r
    simp only [if_pos]
    exact continuousOn_const
  · simp only [hr0, if_false]
    exact continuousOn_heightWeight_mul_dfiSignedCentralSeries_ordinate_height
      hT hc H hX hY hh hk ha hb hr0

/-- The one-box source is integrable on the compact ordinate interval and
the full physical-height line; compact support of the height cutoff supplies
the extension from the source rectangle. -/
theorem integrable_uncurry_heightWeight_mul_hughesYoungFiniteBoxSignedCentralAtHeight
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) {H : ℝ} (hH : 0 ≤ H)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b M N : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        hughesYoungFiniteBoxSignedCentralAtHeight
          T p.2 c p.1 X Y h k a b M N)
      ((volume.restrict (Set.uIoc (-H) H)).prod volume) := by
  let f : ℝ × ℝ → ℂ := fun p =>
    (hughesYoungHeightWeight T p.2 : ℂ) *
      hughesYoungFiniteBoxSignedCentralAtHeight
        T p.2 c p.1 X Y h k a b M N
  let C : Set (ℝ × ℝ) :=
    Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)
  have hcontinuous : ContinuousOn f C := by
    dsimp only [f, C]
    exact
      continuousOn_heightWeight_mul_hughesYoungFiniteBoxSignedCentralAtHeight
        hT hc H hX hY hh hk ha hb
  have hsmall : IntegrableOn f C (volume.prod volume) :=
    hcontinuous.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hbig : IntegrableOn f
      (Set.uIoc (-H) H ×ˢ Set.univ) (volume.prod volume) := by
    apply hsmall.of_forall_diff_eq_zero
      (measurableSet_uIoc.prod MeasurableSet.univ)
    intro p hp
    have ht : p.2 ∉ Set.Icc (T / 4) (4 * T) := by
      intro hp2
      apply hp.2
      have hp1 : p.1 ∈ Set.Icc (-H) H := by
        have hu := Set.uIoc_subset_uIcc hp.1.1
        simpa only [Set.uIcc_of_le (by linarith : -H ≤ H)] using hu
      exact ⟨hp1, hp2⟩
    have hzero : hughesYoungHeightWeight T p.2 = 0 := by
      by_contra hne
      exact ht (hughesYoungHeightWeight_support hT hne)
    dsimp only [f]
    simp [hzero]
  rw [IntegrableOn, ← Measure.prod_restrict] at hbig
  simpa [f] using hbig

/-- Every literal finite complete central box is integrable on the compact
Mellin segment.  This closes the linearity gap needed to pass from the sum of
box integrals to the integral of the cancellation-preserving dyadic sum. -/
theorem intervalIntegrable_mul_hughesYoungFiniteCompleteSignedCentralBox_positiveScale
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) {H : ℝ} (hH : 0 ≤ H)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b M N : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u : ℝ => (T : ℂ) *
      hughesYoungFiniteCompleteSignedCentralBox T c u X Y h k a b M N)
      volume (-H) H := by
  have hprod :=
    integrable_uncurry_heightWeight_mul_hughesYoungFiniteBoxSignedCentralAtHeight
      hT hc hH hX hY hh hk ha hb (M := M) (N := N)
  have houter := hprod.integral_prod_left
  rw [intervalIntegrable_iff]
  apply houter.congr
  filter_upwards with u
  have hsource :=
    hughesYoungFiniteCompleteSignedCentralBox_eq_heightIntegral_positiveScale
      hT hc u hX hY hh hk ha hb (M := M) (N := N)
  dsimp only at houter ⊢
  rw [hsource]
  have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp

/-- The complete rectangular central definition is the interval integral of
the entire finite dyadic source.  No absolute value is taken and no endpoint
box is discarded. -/
theorem hughesYoungRectangularIntegratedCompleteCentral_eq_intervalIntegral_sum
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) {H : ℝ} (hH : 0 ≤ H)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (K : ℕ) :
    (∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
      hughesYoungIntegratedFiniteCompleteSignedCentralBox T c H
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2)) =
      ∫ u in -H..H,
        ∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
          (T : ℂ) * hughesYoungFiniteCompleteSignedCentralBox T c u
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2) := by
  classical
  unfold hughesYoungIntegratedFiniteCompleteSignedCentralBox
  symm
  rw [intervalIntegral.integral_finsetSum]
  intro ij _hij
  exact
    intervalIntegrable_mul_hughesYoungFiniteCompleteSignedCentralBox_positiveScale
      hT hc hH
        (hughesYoungFullDyadicScale_pos ij.1)
        (hughesYoungFullDyadicScale_pos ij.2)
        hh hk (hughesYoungReducedLeft_pos hh)
          (hughesYoungReducedRight_pos hh hk)

/-- Pairwise finite Hughes--Young equation (85): after summing the complete
dyadic rectangle and integrating the Mellin ordinate, the prefactor `T`
exactly cancels the `1/T` from the height transform.  The result keeps the
whole signed source inside both integrals. -/
theorem sum_completeDyadicRectangle_integratedFiniteCompleteBox_eq_source
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) {H : ℝ} (hH : 0 ≤ H)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (K : ℕ) :
    (∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
      hughesYoungIntegratedFiniteCompleteSignedCentralBox T c H
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2)) =
      ∫ t : ℝ, ∫ u in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteReassembledSignedCentralAtHeight
            T t c u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) K := by
  rw [hughesYoungRectangularIntegratedCompleteCentral_eq_intervalIntegral_sum
    hT hc hH hh hk K]
  have hreassembled :=
    intervalIntegral_sum_completeDyadicRectangle_finiteCompleteBox_eq
      hT hc hH hh hk K
  calc
    (∫ u in -H..H,
        ∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
          (T : ℂ) * hughesYoungFiniteCompleteSignedCentralBox T c u
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2)) =
        ∫ u in -H..H, (T : ℂ) *
          (∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
            hughesYoungFiniteCompleteSignedCentralBox T c u
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      change (∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
          (T : ℂ) * hughesYoungFiniteCompleteSignedCentralBox T c u
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2)) =
        (T : ℂ) * ∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
          hughesYoungFiniteCompleteSignedCentralBox T c u
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2)
      exact (Finset.mul_sum _ _ _).symm
    _ = (T : ℂ) * (∫ u in -H..H,
          ∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
            hughesYoungFiniteCompleteSignedCentralBox T c u
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (T : ℂ) * ((1 / (T : ℂ)) * ∫ t : ℝ, ∫ u in -H..H,
          (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungFiniteReassembledSignedCentralAtHeight
              T t c u h k
                (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) K) := by
      rw [hreassembled]
    _ = _ := by
      have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
      field_simp

/-- Finite Hughes--Young equation (85) for the actual mollifier family.
The complete rectangular central term is exactly the sum over `h,k` of the
single cancellation-preserving height/Mellin source.  In particular, the
dyadic endpoint boxes remain present and no triangle inequality has been
applied before the positive and negative shifts are paired. -/
theorem hughesYoungRectangularIntegratedCompleteCentral_eq_finiteSource
    {T : ℝ} (hT : Real.exp 1 ≤ T) (K : ℕ) :
    hughesYoungRectangularIntegratedCompleteCentral T K =
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∫ t : ℝ, ∫ u in -(T / 8)..T / 8,
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungFiniteReassembledSignedCentralAtHeight
                T t (hughesYoungSmallContour T) u h k
                  (hughesYoungReducedLeft h k)
                  (hughesYoungReducedRight h k) K := by
  classical
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hH : 0 ≤ T / 8 := div_nonneg hTpos.le (by norm_num)
  have hc : 0 < hughesYoungSmallContour T :=
    (hughesYoungSmallContour_spec hT).1
  unfold hughesYoungRectangularIntegratedCompleteCentral
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  have hhpos : 0 < h := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hh).1
  have hkpos : 0 < k := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hk).1
  exact
    sum_completeDyadicRectangle_integratedFiniteCompleteBox_eq_source
      hTpos hc hH hhpos hkpos K

end RiemannZeta.GuthMaynard
