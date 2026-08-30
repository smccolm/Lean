import PrimeNumberTheoremAnd.EulerMaclaurin
import RiemannZeta.GuthMaynard.DFIDelta

open Complex Finset Set
open scoped BigOperators ContDiff Interval Topology

namespace RiemannZeta.GuthMaynard

/-!
# Euler--Maclaurin on the DFI lattice

This file supplies the analytic engine used in DFI equations (12)--(20).
The first theorem is the pinned PNT+ first-order Euler--Maclaurin formula
specialized to samples `g(q*r)`.  Keeping the endpoint terms visible is
essential: their difference is the `f(0) * ∫₀∞ w` main term in DFI Lemma 1.
-/

/-- First-order Euler--Maclaurin for a function sampled on the positive
`q`-lattice.  This is the exact finite identity used before DFI let the
support radius tend past the compact support. -/
theorem dfi_scaled_euler_maclaurin
    (g : ℝ → ℂ) (q R : ℕ)
    (hgDiff : Differentiable ℝ g)
    (hgDeriv : Continuous (deriv g)) :
    ∑ r ∈ Finset.Ioc 0 R, g ((q * r : ℕ) : ℝ) =
      g 0 * (B1 0 : ℂ) - g ((q * R : ℕ) : ℝ) * (B1 R : ℂ) +
        (∫ t in (0 : ℝ)..R, g ((q : ℝ) * t)) +
        ∫ t in (0 : ℝ)..R,
          ((q : ℂ) * deriv g ((q : ℝ) * t)) * (B1 t : ℂ) := by
  let h : ℝ → ℂ := fun t => g ((q : ℝ) * t)
  have hhDiff : Differentiable ℝ h := by
    dsimp [h]
    fun_prop
  have hhDeriv (t : ℝ) : deriv h t = (q : ℂ) * deriv g ((q : ℝ) * t) := by
    have hc : HasDerivAt (fun x => g ((q : ℝ) * x))
        ((q : ℂ) * deriv g ((q : ℝ) * t)) t := by
      convert (hgDiff ((q : ℝ) * t)).hasDerivAt.scomp t
        (hasDerivAt_const_mul (q : ℝ)) using 1
    simpa [h] using hc.deriv
  have hhDerivCont : Continuous (deriv h) := by
    rw [show deriv h = fun t => (q : ℂ) * deriv g ((q : ℝ) * t) by
      funext t
      exact hhDeriv t]
    fun_prop
  have hEM := sum_eq_integral_add_integral_deriv
    (f := h) (a := (0 : ℝ)) (b := (R : ℝ))
    (by positivity) (Nat.cast_nonneg R)
    (fun t _ht => hhDiff.differentiableAt)
    hhDerivCont.continuousOn
  simpa [h, hhDeriv, Nat.floor_natCast] using hEM

/-- The same lattice formula after the physical change of variables
`x = q*t`.  In particular, the Bernoulli factor has exactly the source
argument `B₁(x/q)`. -/
theorem dfi_scaled_euler_maclaurin_physical
    (g : ℝ → ℂ) (q R : ℕ) (hq : 0 < q)
    (hgDiff : Differentiable ℝ g)
    (hgDeriv : Continuous (deriv g)) :
    ∑ r ∈ Finset.Ioc 0 R, g ((q * r : ℕ) : ℝ) =
      g 0 * (B1 0 : ℂ) - g ((q * R : ℕ) : ℝ) * (B1 R : ℂ) +
        ((q : ℂ)⁻¹ * ∫ x in (0 : ℝ)..(q * R : ℕ), g x) +
        ∫ x in (0 : ℝ)..(q * R : ℕ),
          deriv g x * (B1 (x / q) : ℂ) := by
  rw [dfi_scaled_euler_maclaurin g q R hgDiff hgDeriv]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hscale := intervalIntegral.integral_comp_mul_left
    (f := g) (a := (0 : ℝ)) (b := (R : ℝ)) hq0
  have hfirst :
      (∫ t in (0 : ℝ)..R, g ((q : ℝ) * t)) =
        (q : ℂ)⁻¹ * ∫ x in (0 : ℝ)..(q * R : ℕ), g x := by
    simpa [smul_eq_mul] using hscale
  rw [hfirst]
  congr 1
  let F : ℝ → ℂ := fun x => deriv g x * (B1 (x / q) : ℂ)
  have hFscale := intervalIntegral.integral_comp_mul_left
    (f := F) (a := (0 : ℝ)) (b := (R : ℝ)) hq0
  have hweighted :
      (∫ t in (0 : ℝ)..R,
        ((q : ℂ) * deriv g ((q : ℝ) * t)) * (B1 t : ℂ)) =
        (q : ℂ) * ∫ t in (0 : ℝ)..R, F ((q : ℝ) * t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp [F]
    have hdiv : (q : ℝ) * t / (q : ℝ) = t := by field_simp
    rw [hdiv]
    ring
  rw [hweighted, hFscale]
  simp [F, Nat.cast_mul, hq.ne']

/-! ## The smooth DFI kernel profile -/

/-- The continuous extension at zero of
`(w(x) - w(u/x))/x`.  DFI equation (20) applies Euler--Maclaurin to this
function. -/
noncomputable def dfiDeltaProfile {Q : ℝ} (w : DFIDeltaWeight Q)
    (u x : ℝ) : ℝ :=
  if x = 0 then 0 else (w x - w (u / x)) / x

@[simp]
theorem dfiDeltaProfile_zero {Q : ℝ} (w : DFIDeltaWeight Q) (u : ℝ) :
    dfiDeltaProfile w u 0 = 0 := by simp [dfiDeltaProfile]

/-- The apparent singularity of the DFI profile at zero is removable.
Annular support makes the profile identically zero on a neighborhood of
zero, including when `u = 0`. -/
theorem contDiff_dfiDeltaProfile {Q : ℝ} (w : DFIDeltaWeight Q) (u : ℝ) :
    ContDiff ℝ ∞ (dfiDeltaProfile w u) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hconst : ContDiffAt ℝ ∞ (fun _y : ℝ => (0 : ℝ)) 0 := contDiffAt_const
    apply hconst.congr_of_eventuallyEq
    by_cases hu : u = 0
    · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) w.Q_pos] with y hyBall
      have hyQ : |y| < Q := by simpa [Real.dist_eq] using hyBall
      by_cases hy : y = 0
      · simp [hy, dfiDeltaProfile]
      · simp [dfiDeltaProfile, hy, hu, w.zero, w.eq_zero_of_abs_lt hyQ]
    · let δ : ℝ := min Q (|u| / (2 * Q))
      have hδ : 0 < δ := by
        dsimp [δ]
        exact lt_min w.Q_pos (div_pos (abs_pos.mpr hu) (mul_pos two_pos w.Q_pos))
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with y hy
      have hyabs : |y| < δ := by simpa [Real.dist_eq] using hy
      by_cases hy0 : y = 0
      · simp [hy0, dfiDeltaProfile]
      · have hyQ : |y| < Q := hyabs.trans_le (min_le_left _ _)
        have hyu : |y| < |u| / (2 * Q) :=
          hyabs.trans_le (min_le_right _ _)
        have hlarge : 2 * Q < |u / y| := by
          rw [abs_div]
          rw [lt_div_iff₀ (abs_pos.mpr hy0)]
          rw [lt_div_iff₀ (mul_pos two_pos w.Q_pos)] at hyu
          nlinarith
        rw [dfiDeltaProfile, if_neg hy0,
          w.eq_zero_of_abs_lt hyQ,
          w.eq_zero_of_two_mul_lt_abs hlarge]
        simp
  · have hrecip : ContDiffAt ℝ ∞ (fun y : ℝ => u / y) x :=
      contDiffAt_const.div contDiffAt_id hx
    have hcomp : ContDiffAt ℝ ∞ (fun y : ℝ => w (u / y)) x :=
      w.smooth.contDiffAt.comp x hrecip
    have hquot : ContDiffAt ℝ ∞
        (fun y : ℝ => (w y - w (u / y)) / y) x :=
      w.smooth.contDiffAt.sub hcomp |>.div contDiffAt_id hx
    apply hquot.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [dfiDeltaProfile, hy]

/-- The ordinary derivative of the DFI profile away from its removable
singularity.  This is the differential appearing in source equation (20). -/
theorem deriv_dfiDeltaProfile {Q : ℝ} (w : DFIDeltaWeight Q)
    (u x : ℝ) (hx : x ≠ 0) :
    deriv (dfiDeltaProfile w u) x =
      (deriv w x - ((-u / x ^ 2) * deriv w (u / x))) / x -
        (w x - w (u / x)) / x ^ 2 := by
  have hwDiff : Differentiable ℝ w := w.smooth.differentiable (by simp)
  have hrecip : HasDerivAt (fun y : ℝ => u / y) (-u / x ^ 2) x := by
    convert (hasDerivAt_const x u).div (hasDerivAt_id x) hx using 1
    simp only [id_eq]
    field_simp [hx]
    ring
  have hcomp : HasDerivAt (fun y : ℝ => w (u / y))
      ((-u / x ^ 2) * deriv w (u / x)) x := by
    convert (hwDiff (u / x)).hasDerivAt.comp x hrecip using 1
    ring
  have hquot : HasDerivAt (fun y : ℝ => (w y - w (u / y)) / y)
      (((deriv w x - ((-u / x ^ 2) * deriv w (u / x))) * x -
          (w x - w (u / x))) / x ^ 2) x := by
    simpa only [Pi.div_apply, id_eq, Pi.sub_apply, mul_one] using
      ((hwDiff x).hasDerivAt.sub hcomp).div (hasDerivAt_id x) hx
  have heq : dfiDeltaProfile w u =ᶠ[𝓝 x]
      (fun y : ℝ => (w y - w (u / y)) / y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [dfiDeltaProfile, hy]
  rw [heq.deriv_eq, hquot.deriv]
  field_simp

/-- On every positive integer lattice point the smooth profile is exactly
the summand in DFI equation (11). -/
theorem dfiDeltaProfile_nat_mul {Q : ℝ} (w : DFIDeltaWeight Q)
    (u : ℝ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    dfiDeltaProfile w u ((q * r : ℕ) : ℝ) =
      (w ((q * r : ℕ) : ℝ) - w (u / (q * r : ℕ))) / (q * r : ℕ) := by
  rw [dfiDeltaProfile, if_neg]
  exact_mod_cast (Nat.mul_pos hq hr).ne'

/-- Real-valued physical form of first-order Euler--Maclaurin.  This is kept
separate from the complex form because DFI equation (20) estimates a real
kernel before any additive character is introduced. -/
theorem dfi_scaled_euler_maclaurin_physical_real
    (g : ℝ → ℝ) (q R : ℕ) (hq : 0 < q)
    (hgDiff : Differentiable ℝ g)
    (hgDeriv : Continuous (deriv g)) :
    ∑ r ∈ Finset.Ioc 0 R, g ((q * r : ℕ) : ℝ) =
      g 0 * B1 0 - g ((q * R : ℕ) : ℝ) * B1 R +
        ((q : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(q * R : ℕ), g x) +
        ∫ x in (0 : ℝ)..(q * R : ℕ), deriv g x * B1 (x / q) := by
  let h : ℝ → ℝ := fun t => g ((q : ℝ) * t)
  have hhDiff : Differentiable ℝ h := by
    dsimp [h]
    fun_prop
  have hhDeriv (t : ℝ) : deriv h t = (q : ℝ) * deriv g ((q : ℝ) * t) := by
    have hc : HasDerivAt (fun x => g ((q : ℝ) * x))
        ((q : ℝ) * deriv g ((q : ℝ) * t)) t := by
      convert (hgDiff ((q : ℝ) * t)).hasDerivAt.comp t
        (hasDerivAt_const_mul (q : ℝ)) using 1
      ring
    simpa [h] using hc.deriv
  have hhDerivCont : Continuous (deriv h) := by
    rw [show deriv h = fun t => (q : ℝ) * deriv g ((q : ℝ) * t) by
      funext t
      exact hhDeriv t]
    fun_prop
  have hEM := sum_eq_integral_add_integral_deriv
    (f := h) (a := (0 : ℝ)) (b := (R : ℝ))
    (by positivity) (Nat.cast_nonneg R)
    (fun t _ht => hhDiff.differentiableAt)
    hhDerivCont.continuousOn
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hscale := intervalIntegral.integral_comp_mul_left
    (f := g) (a := (0 : ℝ)) (b := (R : ℝ)) hq0
  let F : ℝ → ℝ := fun x => deriv g x * B1 (x / q)
  have hFscale := intervalIntegral.integral_comp_mul_left
    (f := F) (a := (0 : ℝ)) (b := (R : ℝ)) hq0
  have hweighted :
      (∫ t in (0 : ℝ)..R,
        ((q : ℝ) * deriv g ((q : ℝ) * t)) * B1 t) =
        (q : ℝ) * ∫ t in (0 : ℝ)..R, F ((q : ℝ) * t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp [F]
    have hdiv : (q : ℝ) * t / (q : ℝ) = t := by field_simp
    rw [hdiv]
    ring
  rw [show (∑ r ∈ Finset.Ioc 0 R, g ((q * r : ℕ) : ℝ)) =
      g 0 * B1 0 - g ((q * R : ℕ) : ℝ) * B1 R +
        (∫ t in (0 : ℝ)..R, g ((q : ℝ) * t)) +
        ∫ t in (0 : ℝ)..R,
          ((q : ℝ) * deriv g ((q : ℝ) * t)) * B1 t by
        simpa [h, hhDeriv, Nat.floor_natCast] using hEM]
  rw [show (∫ t in (0 : ℝ)..R, g ((q : ℝ) * t)) =
      (q : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(q * R : ℕ), g x by
        simpa [smul_eq_mul] using hscale,
    hweighted, hFscale]
  simp [F, Nat.cast_mul, hq.ne']

/-- Exact first-order Euler--Maclaurin expansion of the DFI kernel.  This is
equation (20) before rewriting `B₁(x/q) = {x/q} - 1/2`; unlike a bound, it
retains the mean integral and the complete variation term. -/
theorem dfiDeltaKernel_euler_maclaurin {Q : ℝ} (w : DFIDeltaWeight Q)
    (q : ℕ) (hq : 0 < q) (u : ℝ) :
    dfiDeltaKernel w q u =
      (q : ℝ)⁻¹ *
          (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
            dfiDeltaProfile w u x) +
        ∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
          deriv (dfiDeltaProfile w u) x * B1 (x / q) := by
  let R := dfiDeltaRadius Q u
  have hprof := contDiff_dfiDeltaProfile w u
  have hdiff : Differentiable ℝ (dfiDeltaProfile w u) :=
    hprof.differentiable (by simp)
  have hderiv : Continuous (deriv (dfiDeltaProfile w u)) :=
    hprof.continuous_deriv (by simp)
  have hEM := dfi_scaled_euler_maclaurin_physical_real
    (dfiDeltaProfile w u) q R hq hdiff hderiv
  have hRpos : 0 < R := by
    dsimp [R, dfiDeltaRadius]
    omega
  have hendpoint : dfiDeltaProfile w u ((q * R : ℕ) : ℝ) = 0 := by
    rw [dfiDeltaProfile_nat_mul w u q R hq hRpos]
    obtain ⟨hfirst, hsecond⟩ :=
      dfiDeltaWeight_pair_eq_zero_of_radius_le w (q * R)
        (Nat.mul_pos hq hRpos) (Nat.le_mul_of_pos_left R hq)
    rw [hfirst, hsecond]
    simp
  simp only [dfiDeltaProfile_zero, hendpoint, zero_mul, sub_zero, zero_add] at hEM
  have hsum :
      ∑ r ∈ Finset.Ioc 0 R, dfiDeltaProfile w u ((q * r : ℕ) : ℝ) =
        (q : ℝ)⁻¹ *
            (∫ x in (0 : ℝ)..(q * R : ℕ), dfiDeltaProfile w u x) +
          ∫ x in (0 : ℝ)..(q * R : ℕ),
            deriv (dfiDeltaProfile w u) x * B1 (x / q) := by
    simpa using hEM
  rw [show (q * dfiDeltaRadius Q u : ℕ) = q * R by rfl, ← hsum]
  unfold dfiDeltaKernel
  apply Finset.sum_congr
  · ext r
    simp [R]
    omega
  · intro r hr
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    exact (dfiDeltaProfile_nat_mul w u q r hq hrpos).symm

/-- The total derivative of the compact DFI profile has zero integral on
the Euler--Maclaurin interval.  This removes the constant `-1/2` in `B1`.
-/
theorem integral_deriv_dfiDeltaProfile_eq_zero {Q : ℝ}
    (w : DFIDeltaWeight Q) (q : ℕ) (u : ℝ) :
    (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
      deriv (dfiDeltaProfile w u) x) = 0 := by
  let R : ℕ := dfiDeltaRadius Q u
  have hprof := contDiff_dfiDeltaProfile w u
  have hderiv : Continuous (deriv (dfiDeltaProfile w u)) :=
    hprof.continuous_deriv (by simp)
  have hftc := intervalIntegral.integral_deriv_eq_sub'
    (dfiDeltaProfile w u) rfl
    (fun _x _ => (hprof.differentiable (by simp)).differentiableAt)
    hderiv.continuousOn
    (a := (0 : ℝ)) (b := ((q * R : ℕ) : ℝ))
  have hRpos : 0 < R := by
    dsimp [R, dfiDeltaRadius]
    omega
  by_cases hq : q = 0
  · subst q
    simp
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hendpoint :
        dfiDeltaProfile w u ((q * R : ℕ) : ℝ) = 0 := by
      rw [dfiDeltaProfile_nat_mul w u q R hqpos hRpos]
      obtain ⟨hfirst, hsecond⟩ :=
        dfiDeltaWeight_pair_eq_zero_of_radius_le w (q * R)
          (Nat.mul_pos hqpos hRpos) (Nat.le_mul_of_pos_left R hqpos)
      rw [hfirst, hsecond]
      simp
    have hendpoint' :
        dfiDeltaProfile w u ((q : ℝ) * (R : ℝ)) = 0 := by
      simpa [Nat.cast_mul] using hendpoint
    simpa [R, hendpoint'] using hftc

/-- Corrected fractional-part form of DFI equation (20).  The source omits
the first term; it vanishes for `u ≠ 0` after the inversion substitution,
while at `u = 0` it must be retained and estimated separately. -/
theorem dfiDeltaKernel_euler_maclaurin_fract {Q : ℝ}
    (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q) (u : ℝ) :
    dfiDeltaKernel w q u =
      (q : ℝ)⁻¹ *
          (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
            dfiDeltaProfile w u x) +
        ∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
          deriv (dfiDeltaProfile w u) x * Int.fract (x / q) := by
  rw [dfiDeltaKernel_euler_maclaurin w q hq u]
  congr 1
  have hderivCont : Continuous (deriv (dfiDeltaProfile w u)) :=
    (contDiff_dfiDeltaProfile w u).continuous_deriv (by simp)
  have hderivInt : IntervalIntegrable (deriv (dfiDeltaProfile w u))
      MeasureTheory.volume 0 ((q * dfiDeltaRadius Q u : ℕ) : ℝ) :=
    hderivCont.intervalIntegrable _ _
  have hfractInt : IntervalIntegrable
      (fun x : ℝ => deriv (dfiDeltaProfile w u) x * Int.fract (x / q))
      MeasureTheory.volume 0 ((q * dfiDeltaRadius Q u : ℕ) : ℝ) :=
    ⟨hderivInt.1.mul_bdd
        ((measurable_id.div_const (q : ℝ)).fract.aestronglyMeasurable)
        (by filter_upwards [] with x
            rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
            exact (Int.fract_lt_one _).le),
      hderivInt.2.mul_bdd
        ((measurable_id.div_const (q : ℝ)).fract.aestronglyMeasurable)
        (by filter_upwards [] with x
            rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
            exact (Int.fract_lt_one _).le)⟩
  have hhalfInt : IntervalIntegrable
      (fun x : ℝ => deriv (dfiDeltaProfile w u) x * (1 / 2 : ℝ))
      MeasureTheory.volume 0 ((q * dfiDeltaRadius Q u : ℕ) : ℝ) :=
    hderivInt.mul_const _
  calc
    (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
        deriv (dfiDeltaProfile w u) x * B1 (x / q)) =
      ∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
        (deriv (dfiDeltaProfile w u) x * Int.fract (x / q) -
          deriv (dfiDeltaProfile w u) x * (1 / 2 : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hright : (0 : ℝ) ≤ ((q * dfiDeltaRadius Q u : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        have hxnonneg : 0 ≤ x := by
          rw [uIcc_of_le hright] at hx
          exact hx.1
        have hdivnonneg : 0 ≤ x / (q : ℝ) :=
          div_nonneg hxnonneg (Nat.cast_nonneg q)
        have hfloor :
            (Nat.floor (x / (q : ℝ)) : ℝ) =
              (Int.floor (x / (q : ℝ)) : ℝ) := by
          simpa using natCast_floor_eq_intCast_floor
            (R := ℝ) (a := x / (q : ℝ)) hdivnonneg
        unfold B1 Int.fract
        dsimp only
        rw [hfloor]
        ring
    _ = (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
          deriv (dfiDeltaProfile w u) x * Int.fract (x / q)) -
        ∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
          deriv (dfiDeltaProfile w u) x * (1 / 2 : ℝ) :=
      intervalIntegral.integral_sub hfractInt hhalfInt
    _ = (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
          deriv (dfiDeltaProfile w u) x * Int.fract (x / q)) -
        (1 / 2 : ℝ) *
          ∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
            deriv (dfiDeltaProfile w u) x := by
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _hx
      ring
    _ = _ := by rw [integral_deriv_dfiDeltaProfile_eq_zero w q u]; ring

/-- Restrict an interval integral to a subinterval when the integrand
vanishes on both complementary pieces. -/
theorem intervalIntegral_eq_subinterval_of_eq_zero
    (g : ℝ → ℝ) (hg : Continuous g) {a b B : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ B)
    (hleft : ∀ x ∈ Set.Ioo 0 a, g x = 0)
    (hright : ∀ x ∈ Set.Ioo b B, g x = 0) :
    (∫ x in (0 : ℝ)..B, g x) = ∫ x in a..b, g x := by
  have h0a : IntervalIntegrable g MeasureTheory.volume 0 a :=
    hg.intervalIntegrable _ _
  have habInt : IntervalIntegrable g MeasureTheory.volume a b :=
    hg.intervalIntegrable _ _
  have hbB : IntervalIntegrable g MeasureTheory.volume b B :=
    hg.intervalIntegrable _ _
  have hleftZero : (∫ x in (0 : ℝ)..a, g x) = 0 := by
    calc
      (∫ x in (0 : ℝ)..a, g x) = ∫ _x in (0 : ℝ)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume a] with x hxa
        intro hx
        rw [uIoc_of_le ha] at hx
        exact hleft x ⟨hx.1, lt_of_le_of_ne hx.2 hxa⟩
      _ = 0 := intervalIntegral.integral_zero
  have hrightZero : (∫ x in b..B, g x) = 0 := by
    calc
      (∫ x in b..B, g x) = ∫ _x in b..B, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume B] with x hxB
        intro hx
        rw [uIoc_of_le hb] at hx
        exact hright x ⟨hx.1, lt_of_le_of_ne hx.2 hxB⟩
      _ = 0 := intervalIntegral.integral_zero
  calc
    (∫ x in (0 : ℝ)..B, g x) =
        (∫ x in (0 : ℝ)..a, g x) + ∫ x in a..B, g x := by
      rw [intervalIntegral.integral_add_adjacent_intervals h0a
        (habInt.trans hbB)]
    _ = (∫ x in a..b, g x) + ∫ x in b..B, g x := by
      rw [hleftZero, zero_add,
        intervalIntegral.integral_add_adjacent_intervals habInt hbB]
    _ = ∫ x in a..b, g x := by rw [hrightZero, add_zero]

/-- The mean integral omitted in the printed DFI equation (20) really does
cancel when `u ≠ 0`.  The proof uses the source substitution `y = |u|/x`
and the evenness of the cutoff. -/
theorem integral_dfiDeltaProfile_eq_zero_of_ne_zero {Q : ℝ}
    (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (u : ℝ) (hu : u ≠ 0) :
    (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
      dfiDeltaProfile w u x) = 0 := by
  let a : ℝ := |u|
  let R : ℕ := dfiDeltaRadius Q u
  let B : ℝ := (q * R : ℕ)
  let g₁ : ℝ → ℝ := dfiDeltaProfile w 0
  let g₂ : ℝ → ℝ := fun x => g₁ x - dfiDeltaProfile w u x
  have ha : 0 < a := abs_pos.mpr hu
  have hRbound : 2 * Q + a / Q < (R : ℝ) := by
    simpa [a, R] using dfiDeltaRadius_spec (Q := Q) (u := u)
  have hRleB : (R : ℝ) ≤ B := by
    dsimp [B]
    exact_mod_cast Nat.le_mul_of_pos_left R hq
  have haQpos : 0 < a / Q := div_pos ha w.Q_pos
  have htwoQB : 2 * Q ≤ B := by
    have : 2 * Q < (R : ℝ) := by linarith
    exact this.le.trans hRleB
  have haQB : a / Q ≤ B := by
    have : a / Q < (R : ℝ) := by nlinarith [mul_pos two_pos w.Q_pos]
    exact this.le.trans hRleB
  have hg₁ : Continuous g₁ :=
    (contDiff_dfiDeltaProfile w 0).continuous
  have hg₂ : Continuous g₂ := by
    exact hg₁.sub (contDiff_dfiDeltaProfile w u).continuous
  have hg₁left : ∀ x ∈ Set.Ioo (0 : ℝ) Q, g₁ x = 0 := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hwx : w x = 0 := w.eq_zero_of_abs_lt (by
      rw [abs_of_pos hx.1]
      exact hx.2)
    simp [g₁, dfiDeltaProfile, hx0, hwx]
  have hg₁right : ∀ x ∈ Set.Ioo (2 * Q) B, g₁ x = 0 := by
    intro x hx
    have hxpos : 0 < x := (mul_pos two_pos w.Q_pos).trans hx.1
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hwx : w x = 0 := w.eq_zero_of_two_mul_lt_abs (by
      rw [abs_of_pos hxpos]
      exact hx.1)
    simp [g₁, dfiDeltaProfile, hx0, hwx]
  have hg₂value {x : ℝ} (hx : 0 < x) : g₂ x = w (u / x) / x := by
    have hx0 : x ≠ 0 := ne_of_gt hx
    simp only [g₂, g₁, dfiDeltaProfile, hx0, if_false]
    rw [zero_div, w.zero]
    ring
  have hg₂left : ∀ x ∈ Set.Ioo (0 : ℝ) (a / (2 * Q)), g₂ x = 0 := by
    intro x hx
    rw [hg₂value hx.1]
    have habsdiv : |u / x| = a / x := by
      rw [abs_div, abs_of_pos hx.1]
    have hlarge : 2 * Q < |u / x| := by
      rw [habsdiv]
      rw [lt_div_iff₀ hx.1]
      have hden : 0 < 2 * Q := mul_pos two_pos w.Q_pos
      have hmul := (lt_div_iff₀ hden).mp hx.2
      simpa [mul_comm] using hmul
    rw [w.eq_zero_of_two_mul_lt_abs hlarge, zero_div]
  have hg₂right : ∀ x ∈ Set.Ioo (a / Q) B, g₂ x = 0 := by
    intro x hx
    have hxpos : 0 < x := by
      have : 0 < a / Q := div_pos ha w.Q_pos
      exact this.trans hx.1
    rw [hg₂value hxpos]
    have habsdiv : |u / x| = a / x := by
      rw [abs_div, abs_of_pos hxpos]
    have hsmall : |u / x| < Q := by
      rw [habsdiv]
      rw [div_lt_iff₀ hxpos]
      have hmul := (div_lt_iff₀ w.Q_pos).mp hx.1
      simpa [mul_comm] using hmul
    rw [w.eq_zero_of_abs_lt hsmall, zero_div]
  have hg₁restrict : (∫ x in (0 : ℝ)..B, g₁ x) =
      ∫ x in Q..(2 * Q), g₁ x :=
    intervalIntegral_eq_subinterval_of_eq_zero g₁ hg₁ w.Q_pos.le htwoQB
      hg₁left hg₁right
  have hlow : 0 ≤ a / (2 * Q) := (div_pos ha (mul_pos two_pos w.Q_pos)).le
  have hg₂restrict : (∫ x in (0 : ℝ)..B, g₂ x) =
      ∫ x in (a / (2 * Q))..(a / Q), g₂ x :=
    intervalIntegral_eq_subinterval_of_eq_zero g₂ hg₂ hlow haQB
      hg₂left hg₂right
  let φ : ℝ → ℝ := fun x => a / x
  let φ' : ℝ → ℝ := fun x => -a / x ^ 2
  have hlpos : 0 < a / (2 * Q) := div_pos ha (mul_pos two_pos w.Q_pos)
  have hintervalPos : ∀ x ∈ Set.uIcc (a / (2 * Q)) (a / Q), 0 < x := by
    intro x hx
    have horder : a / (2 * Q) ≤ a / Q := by
      exact div_le_div_of_nonneg_left ha.le w.Q_pos (by nlinarith [w.Q_pos])
    rw [uIcc_of_le horder] at hx
    exact hlpos.trans_le hx.1
  have hφderiv : ∀ x ∈ Set.uIcc (a / (2 * Q)) (a / Q),
      HasDerivAt φ (φ' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hintervalPos x hx)
    dsimp [φ, φ']
    convert (hasDerivAt_const x a).div (hasDerivAt_id x) hx0 using 1
    simp only [id_eq]
    field_simp [hx0]
    ring
  have hφ'cont : ContinuousOn φ'
      (Set.uIcc (a / (2 * Q)) (a / Q)) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hintervalPos x hx)
    dsimp [φ']
    exact ((continuousAt_const : ContinuousAt (fun _ : ℝ => -a) x).div
      (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)).continuousWithinAt
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    hφderiv hφ'cont hg₁.continuousOn
  have hφlow : φ (a / (2 * Q)) = 2 * Q := by
    dsimp [φ]
    field_simp [ha.ne', w.Q_pos.ne']
  have hφhigh : φ (a / Q) = Q := by
    dsimp [φ]
    field_simp [ha.ne', w.Q_pos.ne']
  have hintegrand : ∀ x ∈ Set.uIcc (a / (2 * Q)) (a / Q),
      (g₁ ∘ φ) x * φ' x = -g₂ x := by
    intro x hx
    have hxpos := hintervalPos x hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    rw [hg₂value hxpos]
    have hφpos : 0 < φ x := div_pos ha hxpos
    have hφ0 : φ x ≠ 0 := ne_of_gt hφpos
    have hwu : w (φ x) = w (u / x) := by
      dsimp [φ, a]
      by_cases huPos : 0 < u
      · rw [abs_of_pos huPos]
      · have huNeg : u < 0 := lt_of_le_of_ne (le_of_not_gt huPos) hu
        rw [abs_of_neg huNeg]
        have heq : (-u) / x = -(u / x) := by ring
        rw [heq, w.even]
    simp only [Function.comp_apply]
    rw [show g₁ (φ x) = w (φ x) / φ x by
      simp [g₁, dfiDeltaProfile, hφ0], hwu]
    dsimp [φ, φ']
    field_simp [hx0, ha.ne']
  have hsubst' :
      (∫ x in (a / (2 * Q))..(a / Q), -g₂ x) =
        ∫ y in (2 * Q)..Q, g₁ y := by
    calc
      _ = ∫ x in (a / (2 * Q))..(a / Q), (g₁ ∘ φ) x * φ' x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact (hintegrand x hx).symm
      _ = ∫ y in φ (a / (2 * Q))..φ (a / Q), g₁ y := hsubst
      _ = _ := by rw [hφlow, hφhigh]
  have hmiddle : (∫ x in (a / (2 * Q))..(a / Q), g₂ x) =
      ∫ y in Q..(2 * Q), g₁ y := by
    have hright : (∫ y in (2 * Q)..Q, g₁ y) =
        -(∫ y in Q..(2 * Q), g₁ y) :=
      intervalIntegral.integral_symm _ _
    rw [intervalIntegral.integral_neg, hright] at hsubst'
    exact neg_inj.mp hsubst'
  have hprofile : dfiDeltaProfile w u = fun x => g₁ x - g₂ x := by
    funext x
    dsimp [g₂]
    ring
  rw [hprofile]
  have hg₁Int : IntervalIntegrable g₁ MeasureTheory.volume 0 B :=
    hg₁.intervalIntegrable _ _
  have hg₂Int : IntervalIntegrable g₂ MeasureTheory.volume 0 B :=
    hg₂.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hg₁Int hg₂Int,
    hg₁restrict, hg₂restrict, hmiddle, sub_self]

/-- DFI equation (20) in its literal fractional-part form, on the range
`u ≠ 0` where the source's omitted mean term is proved to cancel. -/
theorem dfiEquation20 {Q : ℝ} (w : DFIDeltaWeight Q)
    (q : ℕ) (hq : 0 < q) (u : ℝ) (hu : u ≠ 0) :
    dfiDeltaKernel w q u =
      ∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
        deriv (dfiDeltaProfile w u) x * Int.fract (x / q) := by
  rw [dfiDeltaKernel_euler_maclaurin_fract w q hq u,
    integral_dfiDeltaProfile_eq_zero_of_ne_zero w q hq u hu]
  ring

end RiemannZeta.GuthMaynard
