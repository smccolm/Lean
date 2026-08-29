import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import RiemannZeta.GuthMaynard.DFIDelta
import RiemannZeta.GuthMaynard.DFIHighOrderEuler

open Set Filter Function MeasureTheory
open scoped BigOperators ContDiff Interval Topology

namespace RiemannZeta.GuthMaynard

/-!
# DFI equation (12)

This file formalizes Lemma 1 of Duke--Friedlander--Iwaniec.  The first
stage below upgrades the finite high-order Euler--Maclaurin theorem to the
endpoint-flat form used by the two source sums.  Subsequent declarations
specialize it to the scaled cutoff and the bilateral sampled test function.
-/

/-- Local vanishing at an endpoint kills every iterated derivative there. -/
theorem iteratedDeriv_eq_zero_of_eventuallyEq_zero
    (g : ℝ → ℝ) (x : ℝ) (hzero : g =ᶠ[𝓝 x] 0) (k : ℕ) :
    iteratedDeriv k g x = 0 := by
  have h := hzero.iteratedDeriv_eq k
  simpa using h

/-- Euler--Maclaurin with endpoint flatness expressed in the local form
that follows directly from compact support or an annular cutoff. -/
theorem dfi_high_order_euler_maclaurin_of_eventually_zero
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (R j : ℕ) (hj : 1 ≤ j)
    (hzero : g =ᶠ[𝓝 (0 : ℝ)] 0)
    (hR : g =ᶠ[𝓝 (R : ℝ)] 0) :
    (∑ r ∈ Finset.Ioc 0 R, g r) =
      (∫ x in (0 : ℝ)..R, g x) +
        (-1 : ℝ) ^ (j + 1) *
          ∫ x in (0 : ℝ)..R, dfiPsi j x * iteratedDeriv j g x := by
  apply dfi_high_order_euler_maclaurin g hg R j hj
  intro k
  exact ⟨iteratedDeriv_eq_zero_of_eventuallyEq_zero g 0 hzero k,
    iteratedDeriv_eq_zero_of_eventuallyEq_zero g R hR k⟩

/-- The first summand in the proof of DFI (12), extended smoothly across
the removable point at zero because the annular cutoff vanishes there. -/
noncomputable def dfiScaledWeightQuotient {Q : ℝ} (w : DFIDeltaWeight Q)
    (q : ℕ) (x : ℝ) : ℝ := w ((q : ℝ) * x) / ((q : ℝ) * x)

/-- The unscaled smooth quotient `(w(r)/r)` occurring literally in DFI
equation (12), with its removable value at zero supplied by the annular
support of `w`. -/
noncomputable def dfiWeightQuotient {Q : ℝ} (w : DFIDeltaWeight Q)
    (r : ℝ) : ℝ := w r / r

theorem dfiScaledWeightQuotient_eq_comp
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) :
    dfiScaledWeightQuotient w q =
      fun x : ℝ => dfiWeightQuotient w ((q : ℝ) * x) := by
  rfl

/-- The scaled quotient is identically zero near the removable point. -/
theorem dfiScaledWeightQuotient_eventuallyEq_zero_at_zero
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) :
    dfiScaledWeightQuotient w q =ᶠ[𝓝 (0 : ℝ)] 0 := by
  by_cases hq : q = 0
  · subst q
    filter_upwards [] with x
    simp [dfiScaledWeightQuotient]
  · have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    have hrad : 0 < Q / (q : ℝ) := div_pos w.Q_pos hqpos
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hrad] with x hx
    unfold dfiScaledWeightQuotient
    have hx' : |x| < Q / (q : ℝ) := by simpa [Real.dist_eq] using hx
    have hxabs : |(q : ℝ) * x| < Q := by
      rw [abs_mul, abs_of_nonneg hqpos.le]
      simpa [mul_comm] using (lt_div_iff₀ hqpos).mp hx'
    rw [w.eq_zero_of_abs_lt hxabs, zero_div]
    rfl

/-- The removable extension is smooth on the entire real line. -/
theorem contDiff_dfiScaledWeightQuotient
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) :
    ContDiff ℝ ∞ (dfiScaledWeightQuotient w q) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hq : q = 0
  · subst q
    have heq : dfiScaledWeightQuotient w 0 = (0 : ℝ → ℝ) := by
      funext y
      simp [dfiScaledWeightQuotient]
    rw [heq]
    exact contDiffAt_const
  by_cases hx : x = 0
  · subst x
    exact (contDiffAt_const (𝕜 := ℝ) (x := (0 : ℝ)) (c := (0 : ℝ))
      (n := (∞ : WithTop ℕ∞))).congr_of_eventuallyEq
        (dfiScaledWeightQuotient_eventuallyEq_zero_at_zero w q)
  · have hlin : ContDiff ℝ ∞ (fun y : ℝ => (q : ℝ) * y) := by fun_prop
    have hden : (q : ℝ) * x ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hq) hx
    exact (w.smooth.comp hlin).contDiffAt.div hlin.contDiffAt hden

/-- The unscaled quotient is smooth globally, including at zero. -/
theorem contDiff_dfiWeightQuotient
    {Q : ℝ} (w : DFIDeltaWeight Q) :
    ContDiff ℝ ∞ (dfiWeightQuotient w) := by
  have h := contDiff_dfiScaledWeightQuotient w 1
  have heq : dfiScaledWeightQuotient w 1 = dfiWeightQuotient w := by
    funext x
    simp [dfiScaledWeightQuotient, dfiWeightQuotient]
  rwa [heq] at h

/-- Exact chain rule for the scaled quotient.  This exposes the `q^j`
factor which, after the change of variables, becomes DFI's `q^(j-1)`. -/
theorem iteratedDeriv_dfiScaledWeightQuotient
    {Q : ℝ} (w : DFIDeltaWeight Q) (q j : ℕ) :
    iteratedDeriv j (dfiScaledWeightQuotient w q) =
      fun x : ℝ => (q : ℝ) ^ j *
        iteratedDeriv j (dfiWeightQuotient w) ((q : ℝ) * x) := by
  rw [dfiScaledWeightQuotient_eq_comp]
  exact iteratedDeriv_comp_const_mul
    ((contDiff_dfiWeightQuotient w).of_le
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))) (q : ℝ)

/-- The explicit delta radius lies strictly beyond the positive support of
every scaled quotient with positive integer scale. -/
theorem dfiScaledWeightQuotient_eventuallyEq_zero_at_radius
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) :
    dfiScaledWeightQuotient w q =ᶠ[𝓝 (dfiDeltaRadius Q 0 : ℝ)] 0 := by
  by_cases hq : q = 0
  · subst q
    filter_upwards [] with x
    simp [dfiScaledWeightQuotient]
  · have hq1 : (1 : ℝ) ≤ q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
    have hR : 2 * Q < (dfiDeltaRadius Q 0 : ℝ) := by
      have := dfiDeltaRadius_spec (Q := Q) (u := (0 : ℝ))
      simpa using this
    have hRnonneg : (0 : ℝ) ≤ (dfiDeltaRadius Q 0 : ℝ) :=
      Nat.cast_nonneg _
    have hRscale : (dfiDeltaRadius Q 0 : ℝ) ≤
        (q : ℝ) * (dfiDeltaRadius Q 0 : ℝ) := by
      nlinarith
    have hcenter : 2 * Q < (q : ℝ) * (dfiDeltaRadius Q 0 : ℝ) :=
      hR.trans_le hRscale
    have hopen : IsOpen {x : ℝ | 2 * Q < (q : ℝ) * x} :=
      isOpen_lt continuous_const (continuous_const.mul continuous_id)
    filter_upwards [hopen.mem_nhds hcenter] with x hx
    unfold dfiScaledWeightQuotient
    have hxpos : 0 < (q : ℝ) * x := lt_trans (mul_pos two_pos w.Q_pos) hx
    have hxabs : 2 * Q < |(q : ℝ) * x| := by simpa [abs_of_pos hxpos] using hx
    rw [w.eq_zero_of_two_mul_lt_abs hxabs, zero_div]
    rfl

/-- The first Euler--Maclaurin expansion in the proof of DFI (12), before
the source changes variables from the lattice parameter to the cutoff
variable. -/
theorem dfiScaledWeightQuotient_euler_maclaurin
    {Q : ℝ} (w : DFIDeltaWeight Q) (q j : ℕ) (hj : 1 ≤ j) :
    (∑ r ∈ Finset.Ioc 0 (dfiDeltaRadius Q 0),
        dfiScaledWeightQuotient w q r) =
      (∫ x in (0 : ℝ)..(dfiDeltaRadius Q 0),
        dfiScaledWeightQuotient w q x) +
      (-1 : ℝ) ^ (j + 1) *
        ∫ x in (0 : ℝ)..(dfiDeltaRadius Q 0),
          dfiPsi j x *
            iteratedDeriv j (dfiScaledWeightQuotient w q) x := by
  exact dfi_high_order_euler_maclaurin_of_eventually_zero
    (dfiScaledWeightQuotient w q)
    (contDiff_dfiScaledWeightQuotient w q)
    (dfiDeltaRadius Q 0) j hj
    (dfiScaledWeightQuotient_eventuallyEq_zero_at_zero w q)
    (dfiScaledWeightQuotient_eventuallyEq_zero_at_radius w q)

/-- Translation by an integer radius, used to turn a bilateral sampled sum
into the natural interval accepted by the finite Euler--Maclaurin theorem. -/
noncomputable def dfiTranslateByRadius (R : ℕ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  g (x - R)

theorem contDiff_dfiTranslateByRadius (g : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (R : ℕ) :
    ContDiff ℝ ∞ (dfiTranslateByRadius R g) := by
  exact hg.comp (by fun_prop)

theorem dfiTranslateByRadius_eventuallyEq_zero_at_zero
    (g : ℝ → ℝ) (R : ℕ) (hneg : g =ᶠ[𝓝 (-(R : ℝ))] 0) :
    dfiTranslateByRadius R g =ᶠ[𝓝 (0 : ℝ)] 0 := by
  have htend0 : Tendsto (fun x : ℝ => x - R) (𝓝 (0 : ℝ))
      (𝓝 ((0 : ℝ) - R)) := continuousAt_id.sub_const (R : ℝ)
  have htend : Tendsto (fun x : ℝ => x - R) (𝓝 0) (𝓝 (-(R : ℝ))) := by
    simpa using htend0
  have hcomp := hneg.comp_tendsto htend
  filter_upwards [hcomp] with x hx
  simpa [dfiTranslateByRadius] using hx

theorem dfiTranslateByRadius_eventuallyEq_zero_at_two_mul
    (g : ℝ → ℝ) (R : ℕ) (hpos : g =ᶠ[𝓝 (R : ℝ)] 0) :
    dfiTranslateByRadius R g =ᶠ[𝓝 ((2 * R : ℕ) : ℝ)] 0 := by
  have htend0 : Tendsto (fun x : ℝ => x - R)
      (𝓝 (((2 * R : ℕ) : ℝ)))
      (𝓝 ((((2 * R : ℕ) : ℝ)) - R)) :=
    continuousAt_id.sub_const (R : ℝ)
  have htend : Tendsto (fun x : ℝ => x - R)
      (𝓝 (((2 * R : ℕ) : ℝ))) (𝓝 (R : ℝ)) := by
    convert htend0 using 1
    push_cast
    ring_nf
  have hcomp := hpos.comp_tendsto htend
  filter_upwards [hcomp] with x hx
  simpa [dfiTranslateByRadius] using hx

/-- Bilateral Euler--Maclaurin on a symmetric finite window, written first
in the exact translated indexing used by the proof. -/
theorem dfi_bilateral_euler_maclaurin_translated
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (R j : ℕ) (hj : 1 ≤ j)
    (hneg : g =ᶠ[𝓝 (-(R : ℝ))] 0)
    (hpos : g =ᶠ[𝓝 (R : ℝ)] 0) :
    (∑ r ∈ Finset.Ioc 0 (2 * R), dfiTranslateByRadius R g r) =
      (∫ x in (0 : ℝ)..(2 * R : ℕ), dfiTranslateByRadius R g x) +
        (-1 : ℝ) ^ (j + 1) *
          ∫ x in (0 : ℝ)..(2 * R : ℕ),
            dfiPsi j x *
              iteratedDeriv j (dfiTranslateByRadius R g) x := by
  exact dfi_high_order_euler_maclaurin_of_eventually_zero
    (dfiTranslateByRadius R g) (contDiff_dfiTranslateByRadius g hg R)
    (2 * R) j hj
    (dfiTranslateByRadius_eventuallyEq_zero_at_zero g R hneg)
    (dfiTranslateByRadius_eventuallyEq_zero_at_two_mul g R hpos)

/-- The finite integer window `(-R,R]`, represented as an injective image
of the natural interval used by Euler--Maclaurin. -/
noncomputable def dfiBilateralWindow (R : ℕ) : Finset ℤ :=
  (Finset.Ioc 0 (2 * R)).map
    ⟨fun r : ℕ => (r : ℤ) - R, fun a b h => by
      have hab : (a : ℤ) = (b : ℤ) := by linarith
      exact_mod_cast hab⟩

theorem sum_dfiBilateralWindow (g : ℝ → ℝ) (R : ℕ) :
    (∑ z ∈ dfiBilateralWindow R, g z) =
      ∑ r ∈ Finset.Ioc 0 (2 * R), dfiTranslateByRadius R g r := by
  unfold dfiBilateralWindow
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro r _hr
  unfold dfiTranslateByRadius
  congr 1
  change (((r : ℤ) - (R : ℤ) : ℤ) : ℝ) = (r : ℝ) - (R : ℝ)
  norm_cast

/-- Translation converts the leading integral exactly to the symmetric
source interval. -/
theorem integral_dfiTranslateByRadius (g : ℝ → ℝ) (R : ℕ) :
    (∫ x in (0 : ℝ)..(2 * R : ℕ), dfiTranslateByRadius R g x) =
      ∫ x in (-(R : ℝ))..R, g x := by
  unfold dfiTranslateByRadius
  rw [intervalIntegral.integral_comp_sub_right]
  congr 1
  · ring
  · rw [Nat.cast_mul, Nat.cast_ofNat]
    ring

/-- Integer translation leaves the periodic Bernoulli factor unchanged and
translates the iterated derivative without a Jacobian. -/
theorem integral_dfiPsi_mul_iteratedDeriv_dfiTranslateByRadius
    (g : ℝ → ℝ) (j R : ℕ) :
    (∫ x in (0 : ℝ)..(2 * R : ℕ),
        dfiPsi j x * iteratedDeriv j (dfiTranslateByRadius R g) x) =
      ∫ x in (-(R : ℝ))..R,
        dfiPsi j x * iteratedDeriv j g x := by
  let F : ℝ → ℝ := fun x =>
    dfiPsi j x * iteratedDeriv j (dfiTranslateByRadius R g) x
  have hshift := intervalIntegral.integral_comp_add_right
    (a := (-(R : ℝ))) (b := (R : ℝ)) F (R : ℝ)
  have hbounds : (-(R : ℝ)) + R = 0 ∧ (R : ℝ) + R = (2 * R : ℕ) := by
    constructor
    · ring
    · push_cast
      ring
  rw [hbounds.1, hbounds.2] at hshift
  rw [← hshift]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold F dfiTranslateByRadius
  rw [iteratedDeriv_comp_sub_const]
  have hperiod : dfiPsi j (x + (R : ℝ)) = dfiPsi j x := by
    simpa using dfiPsi_add_intCast j x (R : ℤ)
  change dfiPsi j (x + (R : ℝ)) *
      iteratedDeriv j g (x + (R : ℝ) - (R : ℝ)) =
    dfiPsi j x * iteratedDeriv j g x
  rw [hperiod]
  congr 2
  ring

/-- DFI's bilateral Euler--Maclaurin formula on the exact symmetric integer
window. -/
theorem dfi_bilateral_euler_maclaurin
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (R j : ℕ) (hj : 1 ≤ j)
    (hneg : g =ᶠ[𝓝 (-(R : ℝ))] 0)
    (hpos : g =ᶠ[𝓝 (R : ℝ)] 0) :
    (∑ z ∈ dfiBilateralWindow R, g z) =
      (∫ x in (-(R : ℝ))..R, g x) +
        (-1 : ℝ) ^ (j + 1) *
          ∫ x in (-(R : ℝ))..R,
            dfiPsi j x * iteratedDeriv j g x := by
  rw [sum_dfiBilateralWindow]
  rw [dfi_bilateral_euler_maclaurin_translated g hg R j hj hneg hpos]
  rw [integral_dfiTranslateByRadius,
    integral_dfiPsi_mul_iteratedDeriv_dfiTranslateByRadius]

/-- Every compact support on the line lies strictly inside a symmetric
integer window.  Strict containment is what supplies endpoint flatness for
all derivative orders. -/
theorem exists_nat_tsupport_subset_Ioo {g : ℝ → ℝ}
    (hg : HasCompactSupport g) :
    ∃ R : ℕ, tsupport g ⊆ Set.Ioo (-(R : ℝ)) (R : ℝ) := by
  obtain ⟨r, hr⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hg.isBounded
  let R : ℕ := ⌈max r 0⌉₊ + 1
  refine ⟨R, fun x hx => ?_⟩
  have hxball := hr hx
  have hxabs : |x| ≤ r := by
    simpa [Real.dist_eq] using hxball
  have hrceil : max r 0 ≤ (⌈max r 0⌉₊ : ℝ) := Nat.le_ceil _
  have hrR : r < (R : ℝ) := by
    dsimp [R]
    push_cast
    linarith [le_max_left r 0]
  constructor <;> linarith [le_abs_self x, neg_le_abs x]

/-- The mapped finite window is exactly the integer interval `(-R,R]`. -/
theorem dfiBilateralWindow_eq_Ioc (R : ℕ) :
    dfiBilateralWindow R = Finset.Ioc (-(R : ℤ)) (R : ℤ) := by
  ext z
  simp only [dfiBilateralWindow, Finset.mem_map, Finset.mem_Ioc]
  constructor
  · rintro ⟨r, ⟨hr0, hrR⟩, hrz⟩
    change (r : ℤ) - (R : ℤ) = z at hrz
    subst z
    constructor <;> omega
  · rintro ⟨hz0, hzR⟩
    let r : ℕ := (z + R).toNat
    have hnonneg : 0 ≤ z + (R : ℤ) := by omega
    have hrCast : (r : ℤ) = z + R := by
      simpa [r] using Int.toNat_of_nonneg hnonneg
    refine ⟨r, ?_, ?_⟩
    · constructor
      · omega
      · have hrBound : (r : ℤ) ≤ 2 * (R : ℤ) := by
          rw [hrCast]
          omega
        exact_mod_cast hrBound
    · change (r : ℤ) - (R : ℤ) = z
      rw [hrCast]
      ring

/-- Pointwise vanishing outside topological support. -/
theorem eq_zero_of_notMem_tsupport {g : ℝ → ℝ} {x : ℝ}
    (hx : x ∉ tsupport g) : g x = 0 := by
  have hlocal := (notMem_tsupport_iff_eventuallyEq.mp hx).self_of_nhds
  simpa using hlocal

/-- Every iterated ordinary derivative has topological support contained in
the support of the original function. -/
theorem tsupport_iteratedDeriv_subset (g : ℝ → ℝ) (k : ℕ) :
    tsupport (iteratedDeriv k g) ⊆ tsupport g := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

/-- Restricting a function supported in a strict symmetric window does not
change its whole-line integral. -/
theorem intervalIntegral_eq_integral_of_tsupport_subset_Ioo
    (g : ℝ → ℝ) (R : ℕ)
    (hsupp : tsupport g ⊆ Set.Ioo (-(R : ℝ)) (R : ℝ)) :
    (∫ x in (-(R : ℝ))..R, g x) = ∫ x, g x := by
  rw [intervalIntegral.integral_of_le (by
    have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith)]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Set.Ioc (-(R : ℝ)) (R : ℝ)
  · simp [Set.indicator_of_mem hx]
  · have hxt : x ∉ tsupport g := by
      intro hmem
      have hrange := hsupp hmem
      have hx' : ¬ (-(R : ℝ) < x ∧ x ≤ (R : ℝ)) := by
        simpa [Set.mem_Ioc] using hx
      have hout : x ≤ -(R : ℝ) ∨ (R : ℝ) < x := by
        by_cases hleft : x ≤ -(R : ℝ)
        · exact Or.inl hleft
        · exact Or.inr (lt_of_not_ge fun hright => hx' ⟨lt_of_not_ge hleft, hright⟩)
      rcases hout with hout | hout
      · exact (not_lt_of_ge hout) hrange.1
      · exact (not_lt_of_ge hrange.2.le) hout
    simp [hx, eq_zero_of_notMem_tsupport hxt]

/-- A compactly supported integer sample has an exact finite `tsum` over
any symmetric window containing its support. -/
theorem tsum_int_eq_sum_dfiBilateralWindow
    (g : ℝ → ℝ) (R : ℕ)
    (hsupp : tsupport g ⊆ Set.Ioo (-(R : ℝ)) (R : ℝ)) :
    (∑' z : ℤ, g z) = ∑ z ∈ dfiBilateralWindow R, g z := by
  symm
  rw [tsum_eq_sum (s := dfiBilateralWindow R)]
  intro z hz
  have hzIoc : z ∉ Finset.Ioc (-(R : ℤ)) (R : ℤ) := by
    simpa [dfiBilateralWindow_eq_Ioc] using hz
  have hz' : ¬ (-(R : ℤ) < z ∧ z ≤ (R : ℤ)) := by
    simpa [Finset.mem_Ioc] using hzIoc
  have hout : z ≤ -(R : ℤ) ∨ (R : ℤ) < z := by omega
  apply eq_zero_of_notMem_tsupport
  intro hmem
  have hrange := hsupp hmem
  rcases hout with hout | hout
  · have hout' : (z : ℝ) ≤ -(R : ℝ) := by exact_mod_cast hout
    exact (not_lt_of_ge hout') hrange.1
  · have hout' : (R : ℝ) < (z : ℝ) := by exact_mod_cast hout
    exact (not_lt_of_ge hrange.2.le) hout'

/-- Integer samples of a function supported in a bounded symmetric window
form a summable family. -/
theorem summable_int_of_tsupport_subset_Ioo
    (g : ℝ → ℝ) (R : ℕ)
    (hsupp : tsupport g ⊆ Set.Ioo (-(R : ℝ)) (R : ℝ)) :
    Summable (fun z : ℤ => g z) := by
  apply summable_of_ne_finset_zero (s := dfiBilateralWindow R)
  intro z hz
  apply eq_zero_of_notMem_tsupport
  intro hmem
  have hrange := hsupp hmem
  have hzIoc : z ∉ Finset.Ioc (-(R : ℤ)) (R : ℤ) := by
    simpa [dfiBilateralWindow_eq_Ioc] using hz
  have hz' : ¬ (-(R : ℤ) < z ∧ z ≤ (R : ℤ)) := by
    simpa [Finset.mem_Ioc] using hzIoc
  by_cases hleft : z ≤ -(R : ℤ)
  · have hleft' : (z : ℝ) ≤ -(R : ℝ) := by exact_mod_cast hleft
    exact (not_lt_of_ge hleft') hrange.1
  · have hright : (R : ℤ) < z := by omega
    have hright' : (R : ℝ) < (z : ℝ) := by exact_mod_cast hright
    exact (not_lt_of_ge hrange.2.le) hright'

/-- Exact decomposition of a compactly supported integer sample into its
zero, positive, and negative modes. -/
theorem tsum_int_eq_zero_add_positive_negative
    (g : ℝ → ℝ) (R : ℕ)
    (hsupp : tsupport g ⊆ Set.Ioo (-(R : ℝ)) (R : ℝ)) :
    (∑' z : ℤ, g z) = g 0 +
      (∑' n : ℕ, g (n + 1 : ℕ)) +
      ∑' n : ℕ, g (-((n + 1 : ℕ) : ℤ)) := by
  have hsum := summable_int_of_tsupport_subset_Ioo g R hsupp
  have hdecomp := tsum_int_eq_zero_add_tsum_pnat hsum
  have hpos : (∑' n : ℕ+, g ((((n : ℕ) : ℤ) : ℝ))) =
      ∑' n : ℕ, g ((((n + 1 : ℕ) : ℤ) : ℝ)) := by
    simpa using (tsum_pnat_eq_tsum_succ
      (M := ℝ) (f := fun k : ℕ => g (((k : ℕ) : ℤ) : ℝ)))
  have hneg : (∑' n : ℕ+, g (((-((n : ℕ) : ℤ) : ℤ) : ℝ))) =
      ∑' n : ℕ, g (((-((n + 1 : ℕ) : ℤ) : ℤ) : ℝ)) := by
    simpa using (tsum_pnat_eq_tsum_succ
      (M := ℝ) (f := fun k : ℕ => g (((-(k : ℤ) : ℤ) : ℝ))))
  rw [hpos, hneg] at hdecomp
  simpa using hdecomp

/-- Whole-line bilateral Euler--Maclaurin for a smooth compactly supported
test function.  This is the second summation formula in the proof of DFI
(12), now stated with the literal infinite integer sum and whole-line
integrals. -/
theorem dfi_bilateral_euler_maclaurin_compact
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hcompact : HasCompactSupport g)
    (j : ℕ) (hj : 1 ≤ j) :
    (∑' z : ℤ, g z) =
      (∫ x : ℝ, g x) +
        (-1 : ℝ) ^ (j + 1) *
          ∫ x : ℝ, dfiPsi j x * iteratedDeriv j g x := by
  obtain ⟨R, hsupp⟩ := exists_nat_tsupport_subset_Ioo hcompact
  have hnegNot : (-(R : ℝ)) ∉ tsupport g := by
    intro hmem
    exact (lt_irrefl (-(R : ℝ))) (hsupp hmem).1
  have hposNot : (R : ℝ) ∉ tsupport g := by
    intro hmem
    exact (lt_irrefl (R : ℝ)) (hsupp hmem).2
  have hneg : g =ᶠ[𝓝 (-(R : ℝ))] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hnegNot
  have hpos : g =ᶠ[𝓝 (R : ℝ)] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hposNot
  have hremSupp :
      tsupport (fun x : ℝ => dfiPsi j x * iteratedDeriv j g x) ⊆
        Set.Ioo (-(R : ℝ)) (R : ℝ) :=
    tsupport_mul_subset_right.trans
      ((tsupport_iteratedDeriv_subset g j).trans hsupp)
  calc
    (∑' z : ℤ, g z) = ∑ z ∈ dfiBilateralWindow R, g z :=
      tsum_int_eq_sum_dfiBilateralWindow g R hsupp
    _ = (∫ x in (-(R : ℝ))..R, g x) +
        (-1 : ℝ) ^ (j + 1) *
          ∫ x in (-(R : ℝ))..R,
            dfiPsi j x * iteratedDeriv j g x :=
      dfi_bilateral_euler_maclaurin g hg R j hj hneg hpos
    _ = (∫ x : ℝ, g x) +
        (-1 : ℝ) ^ (j + 1) *
          ∫ x : ℝ, dfiPsi j x * iteratedDeriv j g x := by
      rw [intervalIntegral_eq_integral_of_tsupport_subset_Ioo g R hsupp,
        intervalIntegral_eq_integral_of_tsupport_subset_Ioo _ R hremSupp]

/-- The source's second Euler--Maclaurin formula, specialized to
`r ↦ f(q u r)` for positive `q,u`.  Both the Jacobian in the leading term
and the factor `(q u)^j` in the remainder are explicit. -/
theorem dfi_scaled_sample_euler_maclaurin
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    (q : ℕ) (hq : 0 < q) (u : ℝ) (hu : 0 < u) (j : ℕ) (hj : 1 ≤ j) :
    (∑' r : ℤ, f ((q : ℝ) * u * r)) =
      ((q : ℝ) * u)⁻¹ * (∫ x : ℝ, f x) +
        (-1 : ℝ) ^ (j + 1) * ((q : ℝ) * u) ^ j *
          ∫ r : ℝ, dfiPsi j r * iteratedDeriv j f ((q : ℝ) * u * r) := by
  let c : ℝ := (q : ℝ) * u
  let g : ℝ → ℝ := fun r => f (c * r)
  have hcpos : 0 < c := mul_pos (by exact_mod_cast hq) hu
  have hg : ContDiff ℝ ∞ g := hf.comp (by fun_prop)
  have hgcompact : HasCompactSupport g := by
    have h := hcompact.comp_smul hcpos.ne'
    simpa [g, c, smul_eq_mul] using h
  have hEM := dfi_bilateral_euler_maclaurin_compact g hg hgcompact j hj
  have hlead : (∫ r : ℝ, g r) = c⁻¹ * ∫ x : ℝ, f x := by
    have h := MeasureTheory.Measure.integral_comp_mul_left f c
    simpa [g, abs_of_pos (inv_pos.mpr hcpos)] using h
  have hderiv : iteratedDeriv j g =
      fun r => c ^ j * iteratedDeriv j f (c * r) := by
    exact iteratedDeriv_comp_const_mul
      (hf.of_le (WithTop.coe_le_coe.mpr
        (le_of_lt (ENat.coe_lt_top j)))) c
  rw [hlead, hderiv] at hEM
  have hrem :
      (∫ r : ℝ, dfiPsi j r *
          (c ^ j * iteratedDeriv j f (c * r))) =
        c ^ j * ∫ r : ℝ, dfiPsi j r * iteratedDeriv j f (c * r) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with r
    ring
  rw [hrem] at hEM
  dsimp [g, c] at hEM ⊢
  convert hEM using 1
  all_goals ring

/-- Signed-scale version of the sampled test-function expansion.  The
Jacobian is `|c|⁻¹`, while the `j`th derivative retains the signed factor
`c^j`. -/
theorem dfi_scaled_sample_euler_maclaurin_nonzero
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    (c : ℝ) (hc : c ≠ 0) (j : ℕ) (hj : 1 ≤ j) :
    (∑' r : ℤ, f (c * r)) =
      |c|⁻¹ * (∫ x : ℝ, f x) +
        (-1 : ℝ) ^ (j + 1) * c ^ j *
          ∫ r : ℝ, dfiPsi j r * iteratedDeriv j f (c * r) := by
  let g : ℝ → ℝ := fun r => f (c * r)
  have hg : ContDiff ℝ ∞ g := hf.comp (by fun_prop)
  have hgcompact : HasCompactSupport g := by
    have h := hcompact.comp_smul hc
    simpa [g, smul_eq_mul] using h
  have hEM := dfi_bilateral_euler_maclaurin_compact g hg hgcompact j hj
  have hlead : (∫ r : ℝ, g r) = |c|⁻¹ * ∫ x : ℝ, f x := by
    simpa [g] using MeasureTheory.Measure.integral_comp_mul_left f c
  have hderiv : iteratedDeriv j g =
      fun r => c ^ j * iteratedDeriv j f (c * r) :=
    iteratedDeriv_comp_const_mul
      (hf.of_le (WithTop.coe_le_coe.mpr
        (le_of_lt (ENat.coe_lt_top j)))) c
  rw [hlead, hderiv] at hEM
  have hrem :
      (∫ r : ℝ, dfiPsi j r *
          (c ^ j * iteratedDeriv j f (c * r))) =
        c ^ j * ∫ r : ℝ, dfiPsi j r * iteratedDeriv j f (c * r) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with r
    ring
  rw [hrem] at hEM
  dsimp [g] at hEM ⊢
  convert hEM using 1
  all_goals ring

/-- Monotonicity of the explicit delta-kernel support radius in the absolute
size of its argument. -/
theorem dfiDeltaRadius_mono_abs {Q u v : ℝ} (hQ : 0 < Q)
    (huv : |u| ≤ |v|) : dfiDeltaRadius Q u ≤ dfiDeltaRadius Q v := by
  unfold dfiDeltaRadius
  gcongr

/-- On a bounded test-function support, one explicit radius works for every
delta kernel in the integral. -/
theorem dfiDeltaKernel_eq_uniform_sum
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (u : ℝ) (U : ℕ) (hu : |u| ≤ U) :
    dfiDeltaKernel w q u =
      ∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q U),
        (w ((q * r : ℕ) : ℝ) - w (u / (q * r : ℕ))) / (q * r : ℕ) := by
  rw [dfiDeltaKernel_eq_tsum w q hq u]
  symm
  rw [tsum_eq_sum (s := Finset.Icc 1 (dfiDeltaRadius Q U))]
  intro r hr
  simp only [Finset.mem_Icc, not_and_or, not_le] at hr
  rcases hr with hr0 | hrR
  · have hrz : r = 0 := by omega
    simp [hrz]
  · have hrad : dfiDeltaRadius Q u ≤ dfiDeltaRadius Q U := by
      apply dfiDeltaRadius_mono_abs w.Q_pos
      simpa [abs_of_nonneg
        (show (0 : ℝ) ≤ (U : ℝ) from Nat.cast_nonneg U)] using hu
    have hqr : dfiDeltaRadius Q u ≤ q * r := by
      exact hrad.trans ((Nat.le_of_lt hrR).trans
        (Nat.le_mul_of_pos_left r hq))
    have hrpos : 0 < r := by omega
    obtain ⟨hfirst, hsecond⟩ :=
      dfiDeltaWeight_pair_eq_zero_of_radius_le w (q * r)
        (Nat.mul_pos hq hrpos) hqr
    rw [hfirst, hsecond, sub_self, zero_div]

/-- The exact positive scaling substitution used to remove `(qr)⁻¹` from
the second half of the delta kernel. -/
theorem integral_mul_scaledWeight_div
    (f w : ℝ → ℝ) (k : ℕ) (hk : 0 < k) :
    (∫ u : ℝ, f u * w (u / (k : ℝ)) / (k : ℝ)) =
      ∫ v : ℝ, w v * f ((k : ℝ) * v) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  let G : ℝ → ℝ := fun u => f u * w (u / (k : ℝ))
  have hscale := MeasureTheory.Measure.integral_comp_mul_left G (k : ℝ)
  have hpoint : (fun v : ℝ => G ((k : ℝ) * v)) =
      fun v => f ((k : ℝ) * v) * w v := by
    funext v
    dsimp [G]
    rw [mul_div_cancel_left₀ v hkreal.ne']
  rw [hpoint, abs_of_pos (inv_pos.mpr hkreal)] at hscale
  have hleft :
      (∫ u : ℝ, f u * w (u / (k : ℝ)) / (k : ℝ)) =
        ((k : ℝ)⁻¹ * ∫ u : ℝ, G u) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with u
    dsimp [G]
    field_simp
  calc
    (∫ u : ℝ, f u * w (u / (k : ℝ)) / (k : ℝ)) =
        (k : ℝ)⁻¹ * ∫ u : ℝ, G u := hleft
    _ = ∫ v : ℝ, f ((k : ℝ) * v) * w v := by
      simpa [smul_eq_mul] using hscale.symm
    _ = ∫ v : ℝ, w v * f ((k : ℝ) * v) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with v
      ring

/-- The annular source condition gives the DFI cutoff genuine compact
support, not merely pointwise decay. -/
theorem DFIDeltaWeight.hasCompactSupport {Q : ℝ} (w : DFIDeltaWeight Q) :
    HasCompactSupport w := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℝ) (2 * Q))
  intro x hx
  have hann := w.support_annulus hx
  simpa [Metric.mem_closedBall, Real.dist_eq] using hann.2

/-- Continuous compact support makes every product with the test function
integrable.  This small interface is used repeatedly when finite DFI sums
are moved through an integral. -/
theorem integrable_test_mul
    (f h : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hh : Continuous h) : Integrable (fun x => f x * h x) := by
  have hcont : Continuous (fun x => f x * h x) := hf.continuous.mul hh
  have hcomp : HasCompactSupport (fun x => f x * h x) := by
    change HasCompactSupport (f * h)
    exact hfc.mul_right
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- The literal left side of DFI equation (12). -/
noncomputable def dfiEquation12Left {Q : ℝ} (w : DFIDeltaWeight Q)
    (q : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ u : ℝ, f u * dfiDeltaKernel w q u

/-- After expanding the kernel and applying the source's change of
variables term by term, the left side of DFI (12) is an exact difference of
two finite sums of integrals. -/
theorem dfiEquation12Left_eq_split
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ)) :
    dfiEquation12Left w q f =
      (∫ u : ℝ, f u) *
          ∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q U),
            w ((q * r : ℕ) : ℝ) / (q * r : ℕ) -
        ∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q U),
          ∫ v : ℝ, w v * f ((q * r : ℕ) * v) := by
  let S := Finset.Icc 1 (dfiDeltaRadius Q U)
  have hkernel (u : ℝ) :
      f u * dfiDeltaKernel w q u =
        ∑ r ∈ S,
          (f u * w ((q * r : ℕ) : ℝ) / (q * r : ℕ) -
            f u * w (u / (q * r : ℕ)) / (q * r : ℕ)) := by
    by_cases hfu : f u = 0
    · simp [hfu]
    · have huS : u ∈ support f := by simpa [Function.mem_support]
      have huT : u ∈ tsupport f := by
        change u ∈ closure (support f)
        exact subset_closure huS
      have hu := hsupp huT
      rw [dfiDeltaKernel_eq_uniform_sum w q hq u U
        (by rcases hu with ⟨hu1, hu2⟩; rw [abs_le]; constructor <;> linarith)]
      dsimp [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring
  have hfirstInt (r : ℕ) (hr : r ∈ S) : Integrable
      (fun u : ℝ => f u * w ((q * r : ℕ) : ℝ) / (q * r : ℕ)) := by
    have hc := hf.continuous.mul_const
      (w ((q * r : ℕ) : ℝ) / (q * r : ℕ))
    have hs : HasCompactSupport
        (fun u : ℝ => f u * (w ((q * r : ℕ) : ℝ) / (q * r : ℕ))) := by
      simpa only [Pi.mul_apply] using
        hfc.mul_right (f' := fun _ : ℝ =>
          w ((q * r : ℕ) : ℝ) / (q * r : ℕ))
    simpa [div_eq_mul_inv, mul_assoc] using
      hc.integrable_of_hasCompactSupport hs
  have hsecondInt (r : ℕ) (hr : r ∈ S) : Integrable
      (fun u : ℝ => f u * w (u / (q * r : ℕ)) / (q * r : ℕ)) := by
    have hwcont : Continuous (fun u : ℝ => w (u / (q * r : ℕ))) :=
      w.smooth.continuous.comp (by fun_prop)
    have hp := integrable_test_mul f
      (fun u : ℝ => w (u / (q * r : ℕ))) hf hfc hwcont
    have hp' := hp.mul_const ((q * r : ℝ)⁻¹)
    simpa [div_eq_mul_inv, mul_assoc] using hp'
  have hint (r : ℕ) (hr : r ∈ S) :
      Integrable (fun u : ℝ =>
        f u * w ((q * r : ℕ) : ℝ) / (q * r : ℕ) -
          f u * w (u / (q * r : ℕ)) / (q * r : ℕ)) :=
    (hfirstInt r hr).sub (hsecondInt r hr)
  unfold dfiEquation12Left
  rw [MeasureTheory.integral_congr_ae (ae_of_all _ hkernel)]
  rw [MeasureTheory.integral_finsetSum S hint]
  have hsplit (r : ℕ) (hr : r ∈ S) :
      (∫ u : ℝ,
          (f u * w ((q * r : ℕ) : ℝ) / (q * r : ℕ) -
            f u * w (u / (q * r : ℕ)) / (q * r : ℕ))) =
        (∫ u : ℝ, f u * w ((q * r : ℕ) : ℝ) / (q * r : ℕ)) -
          ∫ u : ℝ, f u * w (u / (q * r : ℕ)) / (q * r : ℕ) := by
    rw [MeasureTheory.integral_sub (hfirstInt r hr) (hsecondInt r hr)]
  have hsumSplit :
      (∑ r ∈ S, ∫ u : ℝ,
          (f u * w ((q * r : ℕ) : ℝ) / (q * r : ℕ) -
            f u * w (u / (q * r : ℕ)) / (q * r : ℕ))) =
        ∑ r ∈ S,
          ((∫ u : ℝ, f u * w ((q * r : ℕ) : ℝ) / (q * r : ℕ)) -
            ∫ u : ℝ, f u * w (u / (q * r : ℕ)) / (q * r : ℕ)) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact hsplit r hr
  rw [hsumSplit]
  rw [Finset.sum_sub_distrib]
  have hfirst (r : ℕ) (hr : r ∈ S) :
      (∫ u : ℝ, f u * w ((q * r : ℕ) : ℝ) / (q * r : ℕ)) =
        (∫ u : ℝ, f u) * (w ((q * r : ℕ) : ℝ) / (q * r : ℕ)) := by
    rw [← MeasureTheory.integral_mul_const]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with u
    ring
  have hsumFirst :
      (∑ r ∈ S,
          ∫ u : ℝ, f u * w ((q * r : ℕ) : ℝ) / (q * r : ℕ)) =
        ∑ r ∈ S,
          (∫ u : ℝ, f u) *
            (w ((q * r : ℕ) : ℝ) / (q * r : ℕ)) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact hfirst r hr
  rw [hsumFirst]
  rw [← Finset.mul_sum]
  apply congrArg₂ (· - ·) rfl
  apply Finset.sum_congr rfl
  intro r hr
  exact integral_mul_scaledWeight_div f w (q * r)
    (Nat.mul_pos hq (Finset.mem_Icc.mp hr).1)

/-- The common support radius used to expand the delta kernel can be
shrunk back to the source radius of the first Euler--Maclaurin sum. -/
theorem sum_weight_quotient_eq_scaled_sum
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (U : ℕ) :
    (∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q U),
        w ((q * r : ℕ) : ℝ) / (q * r : ℕ)) =
      ∑ r ∈ Finset.Ioc 0 (dfiDeltaRadius Q 0),
        dfiScaledWeightQuotient w q r := by
  let R0 := dfiDeltaRadius Q 0
  let RU := dfiDeltaRadius Q U
  have hR : R0 ≤ RU := by
    dsimp [R0, RU]
    apply dfiDeltaRadius_mono_abs w.Q_pos
    simp
  have hsub : Finset.Icc 1 R0 ⊆ Finset.Icc 1 RU := by
    intro r hr
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hr).1, (Finset.mem_Icc.mp hr).2.trans hR⟩
  have hzero (r : ℕ) (hr : r ∈ Finset.Icc 1 RU)
      (hr0 : r ∉ Finset.Icc 1 R0) :
      w ((q * r : ℕ) : ℝ) / (q * r : ℕ) = 0 := by
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    have hR0r : R0 ≤ r := by
      have hnle := Finset.mem_Icc.not.mp hr0
      omega
    have hR0qr : dfiDeltaRadius Q 0 ≤ q * r := by
      dsimp [R0] at hR0r
      exact hR0r.trans (Nat.le_mul_of_pos_left r hq)
    have hwzero := (dfiDeltaWeight_pair_eq_zero_of_radius_le
      w (q * r) (Nat.mul_pos hq hrpos) hR0qr).1
    rw [hwzero, zero_div]
  have hshrink :
      (∑ r ∈ Finset.Icc 1 RU,
          w ((q * r : ℕ) : ℝ) / (q * r : ℕ)) =
        ∑ r ∈ Finset.Icc 1 R0,
          w ((q * r : ℕ) : ℝ) / (q * r : ℕ) := by
    symm
    exact Finset.sum_subset hsub hzero
  rw [hshrink]
  have hset : Finset.Icc 1 R0 = Finset.Ioc 0 R0 := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset]
  apply Finset.sum_congr rfl
  intro r _hr
  unfold dfiScaledWeightQuotient
  congr 1 <;> push_cast <;> ring

/-- On the support of `w`, the positive sampled test-function series is
exactly truncated by the same explicit radius used for the delta kernel. -/
theorem dfi_weight_mul_positive_tsum_eq_sum
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (U : ℕ)
    (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ)) (v : ℝ) :
    w v * (∑' n : ℕ, f ((q : ℝ) * v * (n + 1 : ℕ))) =
      w v * ∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q U),
        f ((q * r : ℕ) * v) := by
  by_cases hwv : w v = 0
  · simp [hwv]
  have hvann := w.support_annulus hwv
  let R := dfiDeltaRadius Q U
  have htail : ∀ n : ℕ, n ∉ Finset.range R →
      f ((q : ℝ) * v * (n + 1 : ℕ)) = 0 := by
    intro n hn
    have hRn : R ≤ n := by simpa using hn
    have hRspec := dfiDeltaRadius_spec (Q := Q) (u := (U : ℝ))
    have hRQ : (U : ℝ) < (R : ℝ) * Q := by
      have hQ := w.Q_pos
      have hbase : (U : ℝ) / Q < (R : ℝ) := by
        rw [abs_of_nonneg
          (show (0 : ℝ) ≤ (U : ℝ) from Nat.cast_nonneg U)] at hRspec
        nlinarith [mul_pos two_pos hQ]
      exact (div_lt_iff₀ hQ).mp hbase
    have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hnreal : (R : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_of_le hRn
    have hvQ : Q ≤ |v| := hvann.1
    have hlarge : (U : ℝ) < |(q : ℝ) * v * (n + 1 : ℕ)| := by
      rw [abs_mul, abs_mul]
      rw [abs_of_nonneg (show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q),
        abs_of_nonneg
          (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) from Nat.cast_nonneg (n + 1))]
      have hnQ : (R : ℝ) * Q < ((n + 1 : ℕ) : ℝ) * Q :=
        mul_lt_mul_of_pos_right hnreal w.Q_pos
      have hnv : ((n + 1 : ℕ) : ℝ) * Q ≤
          ((n + 1 : ℕ) : ℝ) * |v| :=
        mul_le_mul_of_nonneg_left hvQ (Nat.cast_nonneg _)
      have hbase : 0 ≤ ((n + 1 : ℕ) : ℝ) * |v| :=
        mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
      have hqmul : ((n + 1 : ℕ) : ℝ) * |v| ≤
          ((n + 1 : ℕ) : ℝ) * |v| * (q : ℝ) :=
        by simpa using mul_le_mul_of_nonneg_left hqreal hbase
      nlinarith
    apply eq_zero_of_notMem_tsupport
    intro hmem
    have hrange := hsupp hmem
    have habs : |(q : ℝ) * v * (n + 1 : ℕ)| ≤ U :=
      (abs_le.mpr ⟨hrange.1, hrange.2⟩)
    exact (not_lt_of_ge habs) hlarge
  rw [tsum_eq_sum htail]
  congr 1
  rw [show Finset.Icc 1 R = Finset.Ico 1 (R + 1) by
    ext r
    simp]
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _hn
  congr 1
  push_cast
  ring

/-- The matching negative-mode truncation, obtained from the positive one
by the evenness of the DFI cutoff. -/
theorem dfi_weight_mul_negative_tsum_eq_sum
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (U : ℕ)
    (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ)) (v : ℝ) :
    w v * (∑' n : ℕ, f (-((q : ℝ) * v * (n + 1 : ℕ)))) =
      w v * ∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q U),
        f (-((q * r : ℕ) * v)) := by
  have h := dfi_weight_mul_positive_tsum_eq_sum
    w q hq f U hsupp (-v)
  rw [w.even] at h
  convert h using 1
  · congr 2
    funext n
    congr 1
    ring
  · congr 2
    funext r
    congr 1
    push_cast
    ring

/-- After separating the zero integer mode, the bilateral sample is exactly
the two finite positive/negative sums on the support of `w`. -/
theorem dfi_weight_mul_tsum_sub_zero_eq_finite_sym
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hfc : HasCompactSupport f)
    (U : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (v : ℝ) :
    w v * ((∑' z : ℤ, f ((q : ℝ) * v * z)) - f 0) =
      w v * (∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q U),
        (f ((q * r : ℕ) * v) + f (-((q * r : ℕ) * v)))) := by
  by_cases hwv : w v = 0
  · simp [hwv]
  have hvne : v ≠ 0 := by
    intro hv
    subst v
    exact hwv w.zero
  let g : ℝ → ℝ := fun x => f ((q : ℝ) * v * x)
  have hc : (q : ℝ) * v ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hq.ne') hvne
  have hgcomp : HasCompactSupport g := by
    have h := hfc.comp_smul hc
    simpa [g, smul_eq_mul] using h
  obtain ⟨R, hRsupp⟩ := exists_nat_tsupport_subset_Ioo hgcomp
  have hdecomp := tsum_int_eq_zero_add_positive_negative g R hRsupp
  have hpos := dfi_weight_mul_positive_tsum_eq_sum
    w q hq f U hsupp v
  have hneg := dfi_weight_mul_negative_tsum_eq_sum
    w q hq f U hsupp v
  dsimp [g] at hdecomp
  have hnegCast :
      (∑' n : ℕ, f ((q : ℝ) * v *
        -((((n : ℤ) + 1 : ℤ) : ℝ)))) =
        ∑' n : ℕ, f (-((q : ℝ) * v * (n + 1 : ℕ))) := by
    apply tsum_congr
    intro n
    congr 1
    push_cast
    ring_nf
  calc
    w v * ((∑' z : ℤ, f ((q : ℝ) * v * z)) - f 0) =
        w v * ((∑' n : ℕ, f ((q : ℝ) * v * (n + 1 : ℕ))) +
          ∑' n : ℕ, f (-((q : ℝ) * v * (n + 1 : ℕ)))) := by
      rw [hdecomp]
      rw [hnegCast]
      ring_nf
    _ = w v * (∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q U),
          f ((q * r : ℕ) * v)) +
        w v * (∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q U),
          f (-((q * r : ℕ) * v))) := by
      rw [mul_add, hpos, hneg]
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _hr
      ring

/-- Reflection in the even DFI cutoff identifies the negative and positive
sample integrals.  This is the exact symmetry which produces the factor two
in the second Euler--Maclaurin application in DFI equation (12). -/
theorem integral_weight_mul_reflected_sample
    {Q : ℝ} (w : DFIDeltaWeight Q) (f : ℝ → ℝ)
    (k : ℝ) :
    (∫ v : ℝ, w v * f (-(k * v))) = ∫ v : ℝ, w v * f (k * v) := by
  let G : ℝ → ℝ := fun v => w v * f (k * v)
  have h := MeasureTheory.Measure.integral_comp_mul_left G (-1 : ℝ)
  simpa [G, w.even] using h

/-- Compact support of the DFI cutoff supplies integrability uniformly for
every scaled sample of a continuous test function. -/
theorem integrable_weight_mul_sample
    {Q : ℝ} (w : DFIDeltaWeight Q) (f : ℝ → ℝ)
    (hf : Continuous f) (k : ℝ) :
    Integrable (fun v : ℝ => w v * f (k * v)) := by
  have hcont : Continuous (fun v : ℝ => w v * f (k * v)) :=
    w.smooth.continuous.mul (hf.comp (by fun_prop))
  have hcomp : HasCompactSupport (fun v : ℝ => w v * f (k * v)) := by
    change HasCompactSupport (w.toFun * fun v : ℝ => f (k * v))
    exact w.hasCompactSupport.mul_right
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- Integrated form of the signed lattice decomposition: the nonzero
integer modes are exactly twice the finite positive-frequency sample sum.
No convergence exchange is hidden here; compact support makes the source
sum finite before it is moved through the integral. -/
theorem integral_weight_mul_tsum_sub_zero_eq_two_sum
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ)) :
    (∫ v : ℝ, w v * ((∑' z : ℤ, f ((q : ℝ) * v * z)) - f 0)) =
      2 * ∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q U),
        ∫ v : ℝ, w v * f ((q * r : ℕ) * v) := by
  let S : Finset ℕ := Finset.Icc 1 (dfiDeltaRadius Q U)
  have hpoint (v : ℝ) :
      w v * ((∑' z : ℤ, f ((q : ℝ) * v * z)) - f 0) =
        ∑ r ∈ S, w v *
          (f ((q * r : ℕ) * v) + f (-((q * r : ℕ) * v))) := by
    rw [dfi_weight_mul_tsum_sub_zero_eq_finite_sym
      w q hq f hfc U hsupp v]
    dsimp [S]
    rw [Finset.mul_sum]
  have hpos (r : ℕ) :
      Integrable (fun v : ℝ => w v * f ((q * r : ℕ) * v)) :=
    integrable_weight_mul_sample w f hf.continuous (q * r : ℕ)
  have hneg (r : ℕ) :
      Integrable (fun v : ℝ => w v * f (-((q * r : ℕ) * v))) := by
    simpa only [neg_mul] using
      integrable_weight_mul_sample w f hf.continuous (-(q * r : ℕ) : ℝ)
  have hpair (r : ℕ) :
      Integrable (fun v : ℝ => w v *
        (f ((q * r : ℕ) * v) + f (-((q * r : ℕ) * v)))) := by
    simpa only [Pi.add_apply, mul_add] using (hpos r).add (hneg r)
  calc
    (∫ v : ℝ, w v * ((∑' z : ℤ, f ((q : ℝ) * v * z)) - f 0)) =
        ∫ v : ℝ, ∑ r ∈ S, w v *
          (f ((q * r : ℕ) * v) + f (-((q * r : ℕ) * v))) := by
      apply MeasureTheory.integral_congr_ae
      exact ae_of_all _ hpoint
    _ = ∑ r ∈ S, ∫ v : ℝ, w v *
          (f ((q * r : ℕ) * v) + f (-((q * r : ℕ) * v))) := by
      rw [MeasureTheory.integral_finsetSum S]
      intro r _hr
      exact hpair r
    _ = ∑ r ∈ S, 2 * (∫ v : ℝ, w v * f ((q * r : ℕ) * v)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      have href := integral_weight_mul_reflected_sample
        w f ((q * r : ℕ) : ℝ)
      calc
        (∫ v : ℝ, w v *
            (f ((q * r : ℕ) * v) + f (-((q * r : ℕ) * v)))) =
            (∫ v : ℝ, w v * f ((q * r : ℕ) * v)) +
              ∫ v : ℝ, w v * f (-((q * r : ℕ) * v)) := by
          rw [← MeasureTheory.integral_add (hpos r) (hneg r)]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with v
          ring
        _ = 2 * (∫ v : ℝ, w v * f ((q * r : ℕ) * v)) := by
          rw [href]
          ring
    _ = 2 * ∑ r ∈ S, ∫ v : ℝ, w v * f ((q * r : ℕ) * v) := by
      rw [Finset.mul_sum]
    _ = _ := by rfl

/-- Exact assembly of the two Euler--Maclaurin expansions before the final
changes of variables in DFI equation (12).  This theorem already consumes
the literal delta kernel; the remaining work is analytic normalization of
its three displayed integrals, not an assumed bridge. -/
theorem dfiEquation12_pre_change_of_variables
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (j : ℕ) (hj : 1 ≤ j) :
    dfiEquation12Left w q f =
      (∫ u : ℝ, f u) *
        ((∫ x in (0 : ℝ)..(dfiDeltaRadius Q 0),
            dfiScaledWeightQuotient w q x) +
          (-1 : ℝ) ^ (j + 1) *
            ∫ x in (0 : ℝ)..(dfiDeltaRadius Q 0),
              dfiPsi j x *
                iteratedDeriv j (dfiScaledWeightQuotient w q) x) -
        (2 : ℝ)⁻¹ *
          ∫ v : ℝ, w v *
            ((∑' z : ℤ, f ((q : ℝ) * v * z)) - f 0) := by
  have hsplit := dfiEquation12Left_eq_split
    w q hq f hf hfc U hsupp
  have hfirst := dfiScaledWeightQuotient_euler_maclaurin
    w q j hj
  have hsecond := integral_weight_mul_tsum_sub_zero_eq_two_sum
    w q hq f hf hfc U hsupp
  rw [sum_weight_quotient_eq_scaled_sum w q hq U] at hsplit
  rw [hfirst] at hsplit
  rw [hsecond]
  rw [hsplit]
  ring

/-- The second Euler--Maclaurin formula inserted pointwise under the DFI
cutoff.  At `v = 0` the cutoff itself vanishes; away from zero the signed
scale is nonzero and the bilateral formula applies verbatim. -/
theorem integral_weight_mul_tsum_sub_zero_euler_maclaurin
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (j : ℕ) (hj : 1 ≤ j) :
    (∫ v : ℝ, w v * ((∑' z : ℤ, f ((q : ℝ) * v * z)) - f 0)) =
      ∫ v : ℝ, w v *
        (|(q : ℝ) * v|⁻¹ * (∫ u : ℝ, f u) - f 0 +
          (-1 : ℝ) ^ (j + 1) * ((q : ℝ) * v) ^ j *
            ∫ x : ℝ, dfiPsi j x *
              iteratedDeriv j f ((q : ℝ) * v * x)) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with v
  by_cases hv : v = 0
  · subst v
    simp [w.zero]
  · have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hc : (q : ℝ) * v ≠ 0 := mul_ne_zero hqreal hv
    have hEM := dfi_scaled_sample_euler_maclaurin_nonzero
      f hf hfc ((q : ℝ) * v) hc j hj
    rw [hEM]
    ring

/-- The absolute-value quotient needed for the leading-integral
cancellation in DFI (12).  The apparent singularity is removable because
the annular cutoff vanishes on a neighborhood of zero. -/
noncomputable def dfiWeightAbsQuotient {Q : ℝ} (w : DFIDeltaWeight Q)
    (x : ℝ) : ℝ := w x / |x|

theorem continuous_dfiWeightAbsQuotient
    {Q : ℝ} (w : DFIDeltaWeight Q) :
    Continuous (dfiWeightAbsQuotient w) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hzero : dfiWeightAbsQuotient w =ᶠ[𝓝 (0 : ℝ)] 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) w.Q_pos] with y hy
      have hyabs : |y| < Q := by simpa [Real.dist_eq] using hy
      simp [dfiWeightAbsQuotient, w.eq_zero_of_abs_lt hyabs]
    exact continuousAt_const.congr_of_eventuallyEq hzero
  · exact w.smooth.continuous.continuousAt.div
      continuous_abs.continuousAt (abs_ne_zero.mpr hx)

theorem dfiWeightAbsQuotient_hasCompactSupport
    {Q : ℝ} (w : DFIDeltaWeight Q) :
    HasCompactSupport (dfiWeightAbsQuotient w) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℝ) (2 * Q))
  intro x hx
  have hwx : w x ≠ 0 := by
    intro hw
    exact hx (by simp [dfiWeightAbsQuotient, hw])
  have hann := w.support_annulus hwx
  simpa [Metric.mem_closedBall, Real.dist_eq] using hann.2

theorem integrable_dfiWeightAbsQuotient
    {Q : ℝ} (w : DFIDeltaWeight Q) :
    Integrable (dfiWeightAbsQuotient w) :=
  (continuous_dfiWeightAbsQuotient w).integrable_of_hasCompactSupport
    (dfiWeightAbsQuotient_hasCompactSupport w)

/-- Evenness of the DFI cutoff converts its whole-line absolute quotient
integral to twice the positive half-line integral. -/
theorem integral_dfiWeightAbsQuotient_eq_two_mul
    {Q : ℝ} (w : DFIDeltaWeight Q) :
    (∫ x : ℝ, dfiWeightAbsQuotient w x) =
      2 * ∫ x in Set.Ioi (0 : ℝ), dfiWeightQuotient w x := by
  have heven (x : ℝ) :
      dfiWeightAbsQuotient w x = dfiWeightQuotient w |x| := by
    by_cases hx : 0 ≤ x
    · simp [dfiWeightAbsQuotient, dfiWeightQuotient, abs_of_nonneg hx]
    · have hxneg : x < 0 := lt_of_not_ge hx
      simp [dfiWeightAbsQuotient, dfiWeightQuotient,
        abs_of_neg hxneg, w.even]
  calc
    (∫ x : ℝ, dfiWeightAbsQuotient w x) =
        ∫ x : ℝ, dfiWeightQuotient w |x| := by
      apply MeasureTheory.integral_congr_ae
      exact ae_of_all _ heven
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), dfiWeightQuotient w x :=
      integral_comp_abs

/-- The same evenness identity without the quotient. -/
theorem integral_dfiWeight_eq_two_mul
    {Q : ℝ} (w : DFIDeltaWeight Q) :
    (∫ x : ℝ, w x) = 2 * ∫ x in Set.Ioi (0 : ℝ), w x := by
  have heven (x : ℝ) : w x = w |x| := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx), w.even]
  calc
    (∫ x : ℝ, w x) = ∫ x : ℝ, w |x| := by
      apply MeasureTheory.integral_congr_ae
      exact ae_of_all _ heven
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), w x :=
      integral_comp_abs

/-- A compactly terminated positive integral agrees with the corresponding
half-line set integral. -/
theorem intervalIntegral_eq_integral_Ioi_of_eq_zero_above
    (g : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ x : ℝ, B < x → g x = 0) :
    (∫ x in (0 : ℝ)..B, g x) = ∫ x in Set.Ioi (0 : ℝ), g x := by
  rw [intervalIntegral.integral_of_le hB]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc,
    ← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) B
  · have hxpos : x ∈ Set.Ioi (0 : ℝ) := hx.1
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hxpos]
  · by_cases hxpos : x ∈ Set.Ioi (0 : ℝ)
    · have hxB : B < x := by
        have := hxpos
        simp only [Set.mem_Ioi] at this
        simp only [Set.mem_Ioc, this, true_and] at hx
        exact lt_of_not_ge hx
      simp [Set.indicator_of_notMem hx, Set.indicator_of_mem hxpos,
        hzero x hxB]
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxpos]

/-- The leading integral in the first Euler--Maclaurin expansion, after
the source change of variables `r = qx`. -/
theorem integral_dfiScaledWeightQuotient_eq
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q) :
    (∫ x in (0 : ℝ)..(dfiDeltaRadius Q 0),
        dfiScaledWeightQuotient w q x) =
      (q : ℝ)⁻¹ * ∫ r in Set.Ioi (0 : ℝ), dfiWeightQuotient w r := by
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  let R : ℝ := dfiDeltaRadius Q 0
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    exact Nat.cast_nonneg _
  have hBnonneg : 0 ≤ (q : ℝ) * R :=
    mul_nonneg (Nat.cast_nonneg _) hRnonneg
  have hBlarge : 2 * Q < (q : ℝ) * R := by
    have hspec := dfiDeltaRadius_spec (Q := Q) (u := (0 : ℝ))
    have hRlarge : 2 * Q < R := by simpa [R] using hspec
    have hscale : R ≤ (q : ℝ) * R := by nlinarith
    exact hRlarge.trans_le hscale
  have htruncate :
      (∫ r in (0 : ℝ)..((q : ℝ) * R), dfiWeightQuotient w r) =
        ∫ r in Set.Ioi (0 : ℝ), dfiWeightQuotient w r := by
    apply intervalIntegral_eq_integral_Ioi_of_eq_zero_above _ hBnonneg
    intro r hr
    unfold dfiWeightQuotient
    rw [w.eq_zero_of_two_mul_lt_abs]
    · simp
    · have hrpos : 0 < r := lt_of_lt_of_le
        (mul_pos two_pos w.Q_pos) (le_of_lt (hBlarge.trans hr))
      simpa [abs_of_pos hrpos] using hBlarge.trans hr
  have hscale := intervalIntegral.integral_comp_mul_left
    (f := dfiWeightQuotient w) (a := (0 : ℝ)) (b := R) hqreal
  norm_num [smul_eq_mul] at hscale
  rw [htruncate] at hscale
  simpa [R, dfiScaledWeightQuotient_eq_comp, smul_eq_mul] using hscale

/-- The remainder integral in the first Euler--Maclaurin expansion.  The
chain-rule factor `q^j` and the Jacobian `q⁻¹` combine to the exact source
factor `q^(j-1)`. -/
theorem integral_dfiScaledWeightQuotient_remainder_eq
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (j : ℕ) (hj : 1 ≤ j) :
    (∫ x in (0 : ℝ)..(dfiDeltaRadius Q 0),
        dfiPsi j x * iteratedDeriv j (dfiScaledWeightQuotient w q) x) =
      (q : ℝ) ^ (j - 1) *
        ∫ r in Set.Ioi (0 : ℝ),
          dfiPsi j (r / q) *
            iteratedDeriv j (dfiWeightQuotient w) r := by
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  let R : ℝ := dfiDeltaRadius Q 0
  let H : ℝ → ℝ := fun r => dfiPsi j (r / q) *
    iteratedDeriv j (dfiWeightQuotient w) r
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    exact Nat.cast_nonneg _
  have hBnonneg : 0 ≤ (q : ℝ) * R :=
    mul_nonneg hqpos.le hRnonneg
  have hBlarge : 2 * Q < (q : ℝ) * R := by
    have hspec := dfiDeltaRadius_spec (Q := Q) (u := (0 : ℝ))
    have hRlarge : 2 * Q < R := by simpa [R] using hspec
    have hscale : R ≤ (q : ℝ) * R := by nlinarith
    exact hRlarge.trans_le hscale
  have htruncate :
      (∫ r in (0 : ℝ)..((q : ℝ) * R), H r) =
        ∫ r in Set.Ioi (0 : ℝ), H r := by
    apply intervalIntegral_eq_integral_Ioi_of_eq_zero_above _ hBnonneg
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le
      (mul_pos two_pos w.Q_pos) (le_of_lt (hBlarge.trans hr))
    have hrabs : 2 * Q < |r| := by
      simpa [abs_of_pos hrpos] using hBlarge.trans hr
    have hzero : dfiWeightQuotient w =ᶠ[𝓝 r] 0 := by
      have hopen : IsOpen {x : ℝ | 2 * Q < |x|} :=
        isOpen_lt continuous_const continuous_abs
      filter_upwards [hopen.mem_nhds hrabs] with x hx
      simp [dfiWeightQuotient, w.eq_zero_of_two_mul_lt_abs hx]
    have hderivzero := iteratedDeriv_eq_zero_of_eventuallyEq_zero
      (dfiWeightQuotient w) r hzero j
    simp [H, hderivzero]
  have hscale := intervalIntegral.integral_comp_mul_left
    (f := H) (a := (0 : ℝ)) (b := R) hqreal
  have hcomp : (fun x : ℝ => H ((q : ℝ) * x)) =
      fun x : ℝ => dfiPsi j x *
        iteratedDeriv j (dfiWeightQuotient w) ((q : ℝ) * x) := by
    funext x
    dsimp [H]
    rw [mul_div_cancel_left₀ x hqreal]
  rw [hcomp] at hscale
  norm_num [smul_eq_mul] at hscale
  rw [htruncate] at hscale
  rw [iteratedDeriv_dfiScaledWeightQuotient]
  rw [show (fun x : ℝ => dfiPsi j x *
      ((q : ℝ) ^ j * iteratedDeriv j (dfiWeightQuotient w) ((q : ℝ) * x))) =
      fun x : ℝ => (q : ℝ) ^ j *
        (dfiPsi j x * iteratedDeriv j (dfiWeightQuotient w) ((q : ℝ) * x)) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul]
  rw [hscale]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 1 + k - 1 = k by omega, show 1 + k = k + 1 by omega,
    pow_succ]
  field_simp
  dsimp [H]
  rw [Nat.add_comm 1 k]

/-- The inner change of variables `r = qx` in the second
Euler--Maclaurin remainder. -/
theorem integral_dfiPsi_iteratedDeriv_scaled_eq
    (f : ℝ → ℝ) (q : ℕ) (hq : 0 < q) (j : ℕ) (v : ℝ) :
    (∫ x : ℝ, dfiPsi j x *
        iteratedDeriv j f ((q : ℝ) * v * x)) =
      (q : ℝ)⁻¹ * ∫ r : ℝ, dfiPsi j (r / q) *
        iteratedDeriv j f (v * r) := by
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  let H : ℝ → ℝ := fun r => dfiPsi j (r / q) *
    iteratedDeriv j f (v * r)
  have hscale := MeasureTheory.Measure.integral_comp_mul_left H (q : ℝ)
  have hcomp : (fun x : ℝ => H ((q : ℝ) * x)) =
      fun x : ℝ => dfiPsi j x *
        iteratedDeriv j f ((q : ℝ) * v * x) := by
    funext x
    dsimp [H]
    rw [mul_div_cancel_left₀ x hqreal]
    congr 2
    ring
  rw [hcomp] at hscale
  simpa [H, smul_eq_mul, abs_of_pos (inv_pos.mpr (by exact_mod_cast hq))]
    using hscale

/-- After the inner scale change, the second Euler--Maclaurin remainder
also carries the source factor `q^(j-1)`. -/
theorem integral_weight_second_remainder_scaled_eq
    {Q : ℝ} (w : DFIDeltaWeight Q) (f : ℝ → ℝ)
    (q : ℕ) (hq : 0 < q) (j : ℕ) (hj : 1 ≤ j) :
    (∫ v : ℝ, w v * (((q : ℝ) * v) ^ j *
        ∫ x : ℝ, dfiPsi j x *
          iteratedDeriv j f ((q : ℝ) * v * x))) =
      (q : ℝ) ^ (j - 1) *
        ∫ v : ℝ, w v * (v ^ j *
          ∫ r : ℝ, dfiPsi j (r / q) *
            iteratedDeriv j f (v * r)) := by
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with v
  rw [integral_dfiPsi_iteratedDeriv_scaled_eq f q hq j v]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 1 + k - 1 = k by omega, show 1 + k = k + 1 by omega,
    mul_pow, pow_succ]
  field_simp
  simp only [div_eq_mul_inv, mul_comm]

/-- Fubini in the exact DFI remainder.  For order at least two the periodic
Bernoulli factor is continuous; the annular `w` support and compact support
of `f^(j)` make the two-variable integrand compactly supported. -/
theorem integral_weight_remainder_swap
    {Q : ℝ} (w : DFIDeltaWeight Q) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (U : ℕ)
    (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (q : ℕ) (j : ℕ) (hj : 2 ≤ j) :
    (∫ v : ℝ, w v * (v ^ j *
        ∫ r : ℝ, dfiPsi j (r / q) *
          iteratedDeriv j f (v * r))) =
      ∫ r : ℝ, dfiPsi j (r / q) *
        ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v)) := by
  let K : ℝ → ℝ → ℝ := fun v r =>
    w v * v ^ j * dfiPsi j (r / q) * iteratedDeriv j f (v * r)
  have hfd : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))
  have hKcont : Continuous K.uncurry := by
    have hpsi : Continuous (dfiPsi j) := continuous_dfiPsi (by omega)
    dsimp [K, Function.uncurry]
    exact (((w.smooth.continuous.comp continuous_fst).mul
      (continuous_fst.pow j)).mul
        (hpsi.comp (continuous_snd.div_const (q : ℝ)))).mul
          (hfd.comp (continuous_fst.mul continuous_snd))
  have hKcomp : HasCompactSupport K.uncurry := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : ℝ) (2 * Q)).prod
        (isCompact_closedBall (0 : ℝ) (U : ℝ)))
    intro p hp
    have hKne : K p.1 p.2 ≠ 0 := hp
    have hwne : w p.1 ≠ 0 := by
      intro hw
      exact hKne (by simp [K, hw])
    have hdne : iteratedDeriv j f (p.1 * p.2) ≠ 0 := by
      intro hd
      exact hKne (by simp [K, hd])
    have hvann := w.support_annulus hwne
    have hderivmem : p.1 * p.2 ∈ tsupport (iteratedDeriv j f) := by
      exact subset_tsupport _ hdne
    have hfmem : p.1 * p.2 ∈ tsupport f :=
      tsupport_iteratedDeriv_subset f j hderivmem
    have hfrange := hsupp hfmem
    have hvlow : 1 ≤ |p.1| := w.one_le_Q.trans hvann.1
    have hvhigh : |p.1| ≤ 2 * Q := hvann.2
    have hprod : |p.1| * |p.2| ≤ U := by
      rw [← abs_mul]
      exact abs_le.mpr hfrange
    have hrhigh : |p.2| ≤ U := by
      nlinarith [abs_nonneg p.2]
    constructor
    · simpa [Metric.mem_closedBall, Real.dist_eq] using hvhigh
    · simpa [Metric.mem_closedBall, Real.dist_eq] using hrhigh
  have hswap := integral_integral_swap_of_hasCompactSupport
    (μ := MeasureTheory.volume) (ν := MeasureTheory.volume) hKcont hKcomp
  calc
    (∫ v : ℝ, w v * (v ^ j *
        ∫ r : ℝ, dfiPsi j (r / q) *
          iteratedDeriv j f (v * r))) =
        ∫ v : ℝ, ∫ r : ℝ, K v r := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with v
      calc
        w v * (v ^ j * ∫ r : ℝ, dfiPsi j (r / q) *
            iteratedDeriv j f (v * r)) =
            (w v * v ^ j) * ∫ r : ℝ, dfiPsi j (r / q) *
              iteratedDeriv j f (v * r) := by ring
        _ = ∫ r : ℝ, (w v * v ^ j) *
              (dfiPsi j (r / q) * iteratedDeriv j f (v * r)) := by
          rw [MeasureTheory.integral_const_mul]
        _ = ∫ r : ℝ, K v r := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with r
          dsimp [K]
          ring
    _ = ∫ r : ℝ, ∫ v : ℝ, K v r := hswap
    _ = ∫ r : ℝ, dfiPsi j (r / q) *
        ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with r
      calc
        (∫ v : ℝ, K v r) =
            ∫ v : ℝ, dfiPsi j (r / q) *
              (w v * (v ^ j * iteratedDeriv j f (r * v))) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with v
          dsimp [K]
          rw [mul_comm v r]
          ring
        _ = dfiPsi j (r / q) *
            ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v)) := by
          rw [MeasureTheory.integral_const_mul]

/-- The inner `u`-integral in DFI (12) has the same parity as its derivative
order.  Reflection preserves Lebesgue measure and `w` is even. -/
theorem integral_weight_power_iteratedDeriv_neg
    {Q : ℝ} (w : DFIDeltaWeight Q) (f : ℝ → ℝ)
    (j : ℕ) (r : ℝ) :
    (∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f ((-r) * v))) =
      (-1 : ℝ) ^ j *
        ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v)) := by
  let G : ℝ → ℝ := fun v =>
    w v * (v ^ j * iteratedDeriv j f ((-r) * v))
  have href := MeasureTheory.Measure.integral_comp_mul_left G (-1 : ℝ)
  have hmeasure : (∫ v : ℝ, G (-v)) = ∫ v : ℝ, G v := by
    simpa [smul_eq_mul] using href
  calc
    (∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f ((-r) * v))) =
        ∫ v : ℝ, G v := by rfl
    _ = ∫ v : ℝ, G (-v) := hmeasure.symm
    _ = ∫ v : ℝ, (-1 : ℝ) ^ j *
          (w v * (v ^ j * iteratedDeriv j f (r * v))) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with v
      dsimp [G]
      rw [w.even, neg_pow]
      rw [show (-r) * (-v) = r * v by ring]
      ring
    _ = (-1 : ℝ) ^ j *
        ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v)) := by
      rw [MeasureTheory.integral_const_mul]

/-- After parity is combined, the whole-line remainder is exactly twice
the positive half-line remainder printed in DFI equation (12). -/
theorem integral_dfi_remainder_eq_two_mul_Ioi
    {Q : ℝ} (w : DFIDeltaWeight Q) (f : ℝ → ℝ)
    (q : ℕ) (j : ℕ) (hj : 2 ≤ j) :
    (∫ r : ℝ, dfiPsi j (r / q) *
        ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v))) =
      2 * ∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
        ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v)) := by
  let A : ℝ → ℝ := fun r => dfiPsi j (r / q) *
    ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v))
  have hAeven (r : ℝ) : A (-r) = A r := by
    dsimp [A]
    rw [show (-r) / (q : ℝ) = -(r / (q : ℝ)) by ring,
      dfiPsi_neg (by omega)]
    rw [integral_weight_power_iteratedDeriv_neg w f j r]
    have hsign : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
      rw [← pow_add, (Even.add_self j).neg_one_pow]
    calc
      (-1 : ℝ) ^ j * dfiPsi j (r / q) *
          ((-1 : ℝ) ^ j *
            ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v))) =
          (((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) *
            (dfiPsi j (r / q) *
              ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v)))) := by
        ring
      _ = dfiPsi j (r / q) *
          ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v)) := by
        rw [hsign, one_mul]
  have habs (r : ℝ) : A r = A |r| := by
    by_cases hr : 0 ≤ r
    · rw [abs_of_nonneg hr]
    · rw [abs_of_neg (lt_of_not_ge hr), hAeven]
  calc
    (∫ r : ℝ, dfiPsi j (r / q) *
        ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v))) =
        ∫ r : ℝ, A |r| := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with r
      exact habs r
    _ = 2 * ∫ r in Set.Ioi (0 : ℝ), A r := integral_comp_abs
    _ = _ := by rfl

/-- The compactly supported signed lattice expression under `w` is
integrable.  This follows from its exact finite-mode identity, not from an
unjustified exchange with an infinite series. -/
theorem integrable_weight_mul_tsum_sub_zero
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ)) :
    Integrable (fun v : ℝ =>
      w v * ((∑' z : ℤ, f ((q : ℝ) * v * z)) - f 0)) := by
  let S := Finset.Icc 1 (dfiDeltaRadius Q U)
  have hterm (r : ℕ) : Integrable (fun v : ℝ =>
      w v * (f ((q * r : ℕ) * v) + f (-((q * r : ℕ) * v)))) := by
    have hp := integrable_weight_mul_sample w f hf.continuous (q * r : ℕ)
    have hn : Integrable (fun v : ℝ =>
        w v * f (-((q * r : ℕ) * v))) := by
      simpa only [neg_mul] using
        integrable_weight_mul_sample w f hf.continuous
          (-(q * r : ℕ) : ℝ)
    simpa only [mul_add, Pi.add_apply] using hp.add hn
  have hsum : Integrable (fun v : ℝ =>
      ∑ r ∈ S, w v *
        (f ((q * r : ℕ) * v) + f (-((q * r : ℕ) * v)))) := by
    exact integrable_finsetSum S (fun r _hr => hterm r)
  apply hsum.congr
  filter_upwards [] with v
  rw [dfi_weight_mul_tsum_sub_zero_eq_finite_sym
    w q hq f hfc U hsupp v]
  dsimp [S]
  rw [Finset.mul_sum]

/-- The leading absolute-quotient term in the pointwise second
Euler--Maclaurin formula is integrable. -/
theorem integrable_weight_abs_scale
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (C : ℝ) :
    Integrable (fun v : ℝ => w v * (|(q : ℝ) * v|⁻¹ * C)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hbase := (integrable_dfiWeightAbsQuotient w).const_mul
    ((q : ℝ)⁻¹ * C)
  apply hbase.congr
  filter_upwards [] with v
  by_cases hv : v = 0
  · subst v
    simp [dfiWeightAbsQuotient, w.zero]
  · unfold dfiWeightAbsQuotient
    rw [abs_mul, abs_of_pos hqpos, mul_inv_rev]
    field_simp

/-- Pointwise version of the second Euler--Maclaurin insertion. -/
theorem weight_mul_tsum_sub_zero_eq_euler_maclaurin
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (j : ℕ) (hj : 1 ≤ j) (v : ℝ) :
    w v * ((∑' z : ℤ, f ((q : ℝ) * v * z)) - f 0) =
      w v * (|(q : ℝ) * v|⁻¹ * (∫ u : ℝ, f u) - f 0 +
        (-1 : ℝ) ^ (j + 1) * ((q : ℝ) * v) ^ j *
          ∫ x : ℝ, dfiPsi j x *
            iteratedDeriv j f ((q : ℝ) * v * x)) := by
  by_cases hv : v = 0
  · subst v
    simp [w.zero]
  · have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hc : (q : ℝ) * v ≠ 0 := mul_ne_zero hqreal hv
    rw [dfi_scaled_sample_euler_maclaurin_nonzero
      f hf hfc ((q : ℝ) * v) hc j hj]
    ring

/-- The integrated pointwise formula split into its leading, zero-mode,
and derivative-remainder pieces.  All linearity steps are justified by the
finite-mode integrability theorem above. -/
theorem integral_weight_euler_maclaurin_split
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (j : ℕ) (hj : 1 ≤ j) :
    (∫ v : ℝ, w v *
        (|(q : ℝ) * v|⁻¹ * (∫ u : ℝ, f u) - f 0 +
          (-1 : ℝ) ^ (j + 1) * ((q : ℝ) * v) ^ j *
            ∫ x : ℝ, dfiPsi j x *
              iteratedDeriv j f ((q : ℝ) * v * x))) =
      (q : ℝ)⁻¹ * (∫ u : ℝ, f u) *
          (∫ v : ℝ, dfiWeightAbsQuotient w v) -
        f 0 * (∫ v : ℝ, w v) +
        (-1 : ℝ) ^ (j + 1) *
          ∫ v : ℝ, w v * (((q : ℝ) * v) ^ j *
            ∫ x : ℝ, dfiPsi j x *
              iteratedDeriv j f ((q : ℝ) * v * x)) := by
  let C : ℝ := ∫ u : ℝ, f u
  let s : ℝ := (-1 : ℝ) ^ (j + 1)
  let L : ℝ → ℝ := fun v => w v * (|(q : ℝ) * v|⁻¹ * C)
  let Z : ℝ → ℝ := fun v => w v * f 0
  let R : ℝ → ℝ := fun v => w v * (((q : ℝ) * v) ^ j *
    ∫ x : ℝ, dfiPsi j x * iteratedDeriv j f ((q : ℝ) * v * x))
  let E : ℝ → ℝ := fun v => L v - Z v + s * R v
  have hT := integrable_weight_mul_tsum_sub_zero
    w q hq f hf hfc U hsupp
  have hE : Integrable E := by
    apply hT.congr
    filter_upwards [] with v
    rw [weight_mul_tsum_sub_zero_eq_euler_maclaurin
      w q hq f hf hfc j hj v]
    dsimp [E, L, Z, R, C, s]
    ring
  have hL : Integrable L := integrable_weight_abs_scale w q hq C
  have hZ : Integrable Z := by
    simpa [Z] using integrable_weight_mul_sample w
      (fun _ : ℝ => f 0) continuous_const 0
  have hsR : Integrable (fun v => s * R v) := by
    have h := hE.sub (hL.sub hZ)
    apply h.congr
    filter_upwards [] with v
    dsimp [E]
    ring
  have hsplit : (∫ v : ℝ, E v) =
      (∫ v : ℝ, L v) - (∫ v : ℝ, Z v) +
        ∫ v : ℝ, s * R v := by
    calc
      (∫ v : ℝ, E v) = ∫ v : ℝ, (L v - Z v) + s * R v := by rfl
      _ = (∫ v : ℝ, L v - Z v) + ∫ v : ℝ, s * R v := by
        simpa only [Pi.sub_apply, Pi.add_apply] using
          MeasureTheory.integral_add (hL.sub hZ) hsR
      _ = (∫ v : ℝ, L v) - (∫ v : ℝ, Z v) +
          ∫ v : ℝ, s * R v := by
        rw [MeasureTheory.integral_sub hL hZ]
  have hLint : (∫ v : ℝ, L v) =
      (q : ℝ)⁻¹ * C * ∫ v : ℝ, dfiWeightAbsQuotient w v := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with v
    by_cases hv : v = 0
    · subst v
      simp [L, dfiWeightAbsQuotient, w.zero]
    · dsimp [L]
      unfold dfiWeightAbsQuotient
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < q by exact_mod_cast hq),
        mul_inv_rev]
      field_simp
  have hZint : (∫ v : ℝ, Z v) = f 0 * ∫ v : ℝ, w v := by
    dsimp [Z]
    rw [MeasureTheory.integral_mul_const]
    ring
  have hsRint : (∫ v : ℝ, s * R v) = s * ∫ v : ℝ, R v := by
    rw [MeasureTheory.integral_const_mul]
  calc
    (∫ v : ℝ, w v *
        (|(q : ℝ) * v|⁻¹ * (∫ u : ℝ, f u) - f 0 +
          (-1 : ℝ) ^ (j + 1) * ((q : ℝ) * v) ^ j *
            ∫ x : ℝ, dfiPsi j x *
              iteratedDeriv j f ((q : ℝ) * v * x))) =
        ∫ v : ℝ, E v := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with v
      dsimp [E, L, Z, R, C, s]
      ring
    _ = (∫ v : ℝ, L v) - (∫ v : ℝ, Z v) +
        ∫ v : ℝ, s * R v := hsplit
    _ = _ := by
      rw [hLint, hZint, hsRint]

/-- DFI equation (12), with the two terms inside the final source bracket
displayed as a difference of positive-half-line integrals.  The following
lemma packages that difference back under one integral sign. -/
theorem dfiEquation12_separated
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (j : ℕ) (hj : 2 ≤ j) :
    dfiEquation12Left w q f =
      f 0 * (∫ r in Set.Ioi (0 : ℝ), w r) +
        (-1 : ℝ) ^ (j + 1) * (q : ℝ) ^ (j - 1) *
          ((∫ u : ℝ, f u) *
              (∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
                iteratedDeriv j (dfiWeightQuotient w) r) -
            ∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
              ∫ u : ℝ, w u *
                (u ^ j * iteratedDeriv j f (r * u))) := by
  have hpre := dfiEquation12_pre_change_of_variables
    w q hq f hf hfc U hsupp j (by omega)
  have hinsert := integral_weight_mul_tsum_sub_zero_euler_maclaurin
    w q hq f hf hfc j (by omega)
  have hEM := integral_weight_euler_maclaurin_split
    w q hq f hf hfc U hsupp j (by omega)
  have hlead := integral_dfiScaledWeightQuotient_eq w q hq
  have hfirstRem := integral_dfiScaledWeightQuotient_remainder_eq
    w q hq j (by omega)
  have habs := integral_dfiWeightAbsQuotient_eq_two_mul w
  have hw := integral_dfiWeight_eq_two_mul w
  have hsecondScale := integral_weight_second_remainder_scaled_eq
    w f q hq j (by omega)
  have hswap := integral_weight_remainder_swap
    w f hf U hsupp q j hj
  have hhalf := integral_dfi_remainder_eq_two_mul_Ioi
    w f q j hj
  rw [hinsert, hEM] at hpre
  rw [hlead, hfirstRem, habs, hw] at hpre
  rw [hsecondScale, hswap, hhalf] at hpre
  rw [hpre]
  ring

theorem dfiWeightQuotient_hasCompactSupport
    {Q : ℝ} (w : DFIDeltaWeight Q) :
    HasCompactSupport (dfiWeightQuotient w) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℝ) (2 * Q))
  intro x hx
  have hwx : w x ≠ 0 := by
    intro hw
    exact hx (by simp [dfiWeightQuotient, hw])
  simpa [Metric.mem_closedBall, Real.dist_eq] using
    (w.support_annulus hwx).2

theorem integrableOn_dfi_first_remainder
    {Q : ℝ} (w : DFIDeltaWeight Q) (q j : ℕ) (hj : 2 ≤ j) :
    IntegrableOn (fun r : ℝ => dfiPsi j (r / q) *
      iteratedDeriv j (dfiWeightQuotient w) r) (Set.Ioi 0) := by
  have hcont : Continuous (fun r : ℝ => dfiPsi j (r / q) *
      iteratedDeriv j (dfiWeightQuotient w) r) := by
    exact (continuous_dfiPsi (by omega) |>.comp
      (continuous_id.div_const (q : ℝ))).mul
        ((contDiff_dfiWeightQuotient w).continuous_iteratedDeriv j
          (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j))))
  have hcomp : HasCompactSupport (fun r : ℝ => dfiPsi j (r / q) *
      iteratedDeriv j (dfiWeightQuotient w) r) := by
    have hderiv_aux : ∀ k : ℕ, HasCompactSupport
        (iteratedDeriv k (dfiWeightQuotient w)) := by
      intro k
      induction k with
      | zero =>
          simpa using dfiWeightQuotient_hasCompactSupport w
      | succ k ih =>
          rw [iteratedDeriv_succ]
          exact ih.deriv
    have hderiv := hderiv_aux j
    change HasCompactSupport
      ((fun r : ℝ => dfiPsi j (r / q)) *
        iteratedDeriv j (dfiWeightQuotient w))
    apply HasCompactSupport.mul_left
    exact hderiv
  exact (hcont.integrable_of_hasCompactSupport hcomp).integrableOn

/-- Integrability of the outer source remainder follows from the same
compact two-variable kernel used in the proved Fubini step. -/
theorem integrableOn_dfi_second_remainder
    {Q : ℝ} (w : DFIDeltaWeight Q) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (U : ℕ)
    (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (q j : ℕ) (hj : 2 ≤ j) :
    IntegrableOn (fun r : ℝ => dfiPsi j (r / q) *
      ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v)))
      (Set.Ioi 0) := by
  let K : ℝ × ℝ → ℝ := fun p =>
    w p.1 * p.1 ^ j * dfiPsi j (p.2 / q) *
      iteratedDeriv j f (p.1 * p.2)
  have hfd : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))
  have hKcont : Continuous K := by
    have hpsi : Continuous (dfiPsi j) := continuous_dfiPsi (by omega)
    dsimp [K]
    exact (((w.smooth.continuous.comp continuous_fst).mul
      (continuous_fst.pow j)).mul
        (hpsi.comp (continuous_snd.div_const (q : ℝ)))).mul
          (hfd.comp (continuous_fst.mul continuous_snd))
  have hKcomp : HasCompactSupport K := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : ℝ) (2 * Q)).prod
        (isCompact_closedBall (0 : ℝ) (U : ℝ)))
    intro p hp
    have hKne : K p ≠ 0 := hp
    have hwne : w p.1 ≠ 0 := by
      intro hw
      exact hKne (by simp [K, hw])
    have hdne : iteratedDeriv j f (p.1 * p.2) ≠ 0 := by
      intro hd
      exact hKne (by simp [K, hd])
    have hvann := w.support_annulus hwne
    have hderivmem : p.1 * p.2 ∈ tsupport (iteratedDeriv j f) :=
      subset_tsupport _ hdne
    have hfrange := hsupp
      (tsupport_iteratedDeriv_subset f j hderivmem)
    have hvlow : 1 ≤ |p.1| := w.one_le_Q.trans hvann.1
    have hprod : |p.1| * |p.2| ≤ U := by
      rw [← abs_mul]
      exact abs_le.mpr hfrange
    have hrhigh : |p.2| ≤ U := by
      nlinarith [abs_nonneg p.2]
    constructor
    · simpa [Metric.mem_closedBall, Real.dist_eq] using hvann.2
    · simpa [Metric.mem_closedBall, Real.dist_eq] using hrhigh
  have hKint : Integrable K
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    hKcont.integrable_of_hasCompactSupport hKcomp
  have hout := hKint.integral_prod_right
  have hout' : Integrable (fun r : ℝ => dfiPsi j (r / q) *
      ∫ v : ℝ, w v * (v ^ j * iteratedDeriv j f (r * v))) := by
    apply hout.congr
    filter_upwards [] with r
    change (∫ v : ℝ, K (v, r)) = _
    calc
      (∫ v : ℝ, K (v, r)) =
          ∫ v : ℝ, dfiPsi j (r / q) *
            (w v * (v ^ j * iteratedDeriv j f (r * v))) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with v
        dsimp [K]
        rw [mul_comm v r]
        ring
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  exact hout'.integrableOn

/-- DFI equation (12), with the two Euler--Maclaurin remainders assembled
under the single positive-half-line integral occurring in the source. -/
theorem dfiEquation12_outer
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (j : ℕ) (hj : 2 ≤ j) :
    dfiEquation12Left w q f =
      f 0 * (∫ r in Set.Ioi (0 : ℝ), w r) +
        (-1 : ℝ) ^ (j + 1) * (q : ℝ) ^ (j - 1) *
          ∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
            ((∫ u : ℝ, f u) * iteratedDeriv j (dfiWeightQuotient w) r -
              ∫ u : ℝ, w u *
                (u ^ j * iteratedDeriv j f (r * u))) := by
  have hfirst := (integrableOn_dfi_first_remainder w q j hj).const_mul
    (∫ u : ℝ, f u)
  have hsecond := integrableOn_dfi_second_remainder
    w f hf U hsupp q j hj
  have hpack :
      (∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
          ((∫ u : ℝ, f u) * iteratedDeriv j (dfiWeightQuotient w) r -
            ∫ u : ℝ, w u *
              (u ^ j * iteratedDeriv j f (r * u)))) =
        (∫ u : ℝ, f u) *
            (∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
              iteratedDeriv j (dfiWeightQuotient w) r) -
          ∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
            ∫ u : ℝ, w u *
              (u ^ j * iteratedDeriv j f (r * u)) := by
    calc
      _ = ∫ r in Set.Ioi (0 : ℝ),
          (∫ u : ℝ, f u) *
              (dfiPsi j (r / q) *
                iteratedDeriv j (dfiWeightQuotient w) r) -
            dfiPsi j (r / q) *
              (∫ u : ℝ, w u *
                (u ^ j * iteratedDeriv j f (r * u))) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro r _
          ring
      _ = (∫ r in Set.Ioi (0 : ℝ),
            (∫ u : ℝ, f u) *
              (dfiPsi j (r / q) *
                iteratedDeriv j (dfiWeightQuotient w) r)) -
          ∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
            (∫ u : ℝ, w u *
              (u ^ j * iteratedDeriv j f (r * u))) := by
          exact MeasureTheory.integral_sub hfirst hsecond
      _ = _ := by
          rw [MeasureTheory.integral_const_mul]
  rw [dfiEquation12_separated w q hq f hf hfc U hsupp j hj, hpack]

/-- The second summand in the inner source integral of DFI (12) is
integrable for every fixed outer variable. -/
theorem integrable_dfiEquation12_inner_second
    {Q : ℝ} (w : DFIDeltaWeight Q) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (r : ℝ) :
    Integrable (fun u : ℝ => w u *
      (u ^ j * iteratedDeriv j f (r * u))) := by
  have hfd : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))
  have hcont : Continuous (fun u : ℝ => w u *
      (u ^ j * iteratedDeriv j f (r * u))) := by
    exact w.smooth.continuous.mul
      ((continuous_id.pow j).mul
        (hfd.comp (continuous_const.mul continuous_id)))
  have hcomp : HasCompactSupport (fun u : ℝ => w u *
      (u ^ j * iteratedDeriv j f (r * u))) := by
    change HasCompactSupport
      (w.toFun * fun u : ℝ => u ^ j * iteratedDeriv j f (r * u))
    exact w.hasCompactSupport.mul_right
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- Corrected exact form of DFI equation (12).  Direct changes of variables
in the two Euler--Maclaurin remainders produce `q^(j-1)`; this theorem keeps
that Jacobian visible and retains the source's single nested integral. -/
theorem dfiEquation12
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (j : ℕ) (hj : 2 ≤ j) :
    dfiEquation12Left w q f =
      f 0 * (∫ r in Set.Ioi (0 : ℝ), w r) +
        (-1 : ℝ) ^ (j + 1) * (q : ℝ) ^ (j - 1) *
          ∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
            ∫ u : ℝ,
              f u * iteratedDeriv j (dfiWeightQuotient w) r -
                w u * (u ^ j * iteratedDeriv j f (r * u)) := by
  rw [dfiEquation12_outer w q hq f hf hfc U hsupp j hj]
  congr 2
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro r _hr
  apply congrArg (fun z : ℝ => dfiPsi j (r / q) * z)
  have hfint : Integrable f :=
    hf.continuous.integrable_of_hasCompactSupport hfc
  have hfirst : Integrable (fun u : ℝ =>
      f u * iteratedDeriv j (dfiWeightQuotient w) r) :=
    hfint.mul_const _
  have hsecond := integrable_dfiEquation12_inner_second w f hf j r
  rw [MeasureTheory.integral_sub hfirst hsecond,
    MeasureTheory.integral_mul_const]

end RiemannZeta.GuthMaynard
