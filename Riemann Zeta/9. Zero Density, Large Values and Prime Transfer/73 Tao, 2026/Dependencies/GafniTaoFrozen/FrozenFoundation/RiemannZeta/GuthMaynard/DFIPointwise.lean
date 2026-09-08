import RiemannZeta.GuthMaynard.DFIEstimates
import RiemannZeta.GuthMaynard.DFIEulerMaclaurin

open Set Filter Function MeasureTheory
open scoped BigOperators ContDiff Interval Topology

namespace RiemannZeta.GuthMaynard

/-!
# DFI equation (19): pointwise delta-symbol decay

This module proves the two scale-sensitive variation estimates entering the
pointwise delta-symbol bound.  The direct cutoff lives at scale `Q`; the
inverted cutoff lives at scale `|u| / Q`.
-/

/-- The elementary majorant for the fractional part on the positive
Euler--Maclaurin interval. -/
noncomputable def dfiFractMajorant (q : ℕ) (x : ℝ) : ℝ :=
  min 1 (x / q)

theorem abs_fract_le_dfiFractMajorant
    (q : ℕ) (hq : 0 < q) {x : ℝ} (hx : 0 ≤ x) :
    |Int.fract (x / q)| ≤ dfiFractMajorant q x := by
  have hqreal : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hz : 0 ≤ x / (q : ℝ) := div_nonneg hx hqreal.le
  have hfract0 : 0 ≤ Int.fract (x / (q : ℝ)) := Int.fract_nonneg _
  have hfract1 : Int.fract (x / (q : ℝ)) ≤ 1 := (Int.fract_lt_one _).le
  have hfloor0 : (0 : ℤ) ≤ Int.floor (x / (q : ℝ)) :=
    Int.floor_nonneg.mpr hz
  have hfloor0' : (0 : ℝ) ≤ (Int.floor (x / (q : ℝ)) : ℝ) := by
    exact_mod_cast hfloor0
  have hfractx : Int.fract (x / (q : ℝ)) ≤ x / q := by
    rw [Int.fract]
    linarith
  rw [abs_of_nonneg hfract0]
  exact le_min hfract1 hfractx

theorem dfiFractMajorant_nonneg
    (q : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ dfiFractMajorant q x := by
  dsimp [dfiFractMajorant]
  exact le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg q))

theorem dfiFractMajorant_le_one (q : ℕ) (x : ℝ) :
    dfiFractMajorant q x ≤ 1 := min_le_left _ _

theorem dfiFractMajorant_le_div (q : ℕ) (x : ℝ) :
    dfiFractMajorant q x ≤ x / q := min_le_right _ _

/-- The reciprocal-sum comparison converting the two elementary `min`
bounds into DFI's displayed denominator. -/
theorem min_inv_le_two_mul_inv_add
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    min A⁻¹ B⁻¹ ≤ 2 * (A + B)⁻¹ := by
  by_cases hAB : A ≤ B
  · rw [min_eq_right ((inv_le_inv₀ hB hA).2 hAB)]
    have hsum : A + B ≤ 2 * B := by linarith
    have htwoB : 0 < 2 * B := mul_pos two_pos hB
    have hsumPos : 0 < A + B := add_pos hA hB
    have hinv : (2 * B)⁻¹ ≤ (A + B)⁻¹ :=
      (inv_le_inv₀ htwoB hsumPos).2 hsum
    calc
      B⁻¹ = 2 * (2 * B)⁻¹ := by field_simp [hB.ne']
      _ ≤ 2 * (A + B)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv zero_le_two
  · have hBA : B ≤ A := le_of_not_ge hAB
    rw [min_eq_left ((inv_le_inv₀ hA hB).2 hBA)]
    have hsum : A + B ≤ 2 * A := by linarith
    have htwoA : 0 < 2 * A := mul_pos two_pos hA
    have hsumPos : 0 < A + B := add_pos hA hB
    have hinv : (2 * A)⁻¹ ≤ (A + B)⁻¹ :=
      (inv_le_inv₀ htwoA hsumPos).2 hsum
    calc
      A⁻¹ = 2 * (2 * A)⁻¹ := by field_simp [hA.ne']
      _ ≤ 2 * (A + B)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv zero_le_two

/-- The direct part of the DFI profile derivative. -/
theorem deriv_dfiDeltaProfile_zero
    {Q : ℝ} (w : DFIDeltaWeight Q) {x : ℝ} (hx : x ≠ 0) :
    deriv (dfiDeltaProfile w 0) x =
      deriv w x / x - w x / x ^ 2 := by
  rw [deriv_dfiDeltaProfile w 0 x hx]
  simp only [zero_div, neg_zero, zero_mul, w.zero]
  ring

/-- A single positive constant controls the zeroth and first derivatives at
the two source scales needed in equation (19). -/
theorem exists_dfiWeight_zero_one_bounds
    {Q : ℝ} (w : DFIDeltaWeight Q) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x : ℝ, |w x| ≤ C * Q⁻¹) ∧
      (∀ x : ℝ, |deriv w x| ≤ C * (Q ^ 2)⁻¹) := by
  obtain ⟨C₀, hC₀, h₀⟩ := w.derivativeBound 0
  obtain ⟨C₁, hC₁, h₁⟩ := w.derivativeBound 1
  let C := max C₀ C₁
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_, ?_⟩
  · intro x
    have hx : |w x| ≤ C₀ * Q⁻¹ := by
      simpa [Real.norm_eq_abs] using h₀ x
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left C₀ C₁)
      (inv_nonneg.mpr w.Q_pos.le))
  · intro x
    have hx : |deriv w x| ≤ C₁ * (Q ^ 2)⁻¹ := by
      simpa [iteratedDeriv_one, Real.norm_eq_abs] using h₁ x
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_right C₀ C₁)
      (inv_nonneg.mpr (sq_nonneg Q)))

/-- Zeroth and first equation-(9) bounds from one explicit profile. -/
theorem dfiWeight_zero_one_bounds_of_profile
    {Q : ℝ} {w : DFIDeltaWeight Q} {D : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D) :
    (∀ x : ℝ, |w x| ≤ max (D 0) (D 1) * Q⁻¹) ∧
    (∀ x : ℝ, |deriv w x| ≤ max (D 0) (D 1) * (Q ^ 2)⁻¹) := by
  constructor
  · intro x
    have hx : |w x| ≤ D 0 * Q⁻¹ := by
      simpa [Real.norm_eq_abs] using hD.bound 0 x
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left (D 0) (D 1))
      (inv_nonneg.mpr w.Q_pos.le))
  · intro x
    have hx : |deriv w x| ≤ D 1 * (Q ^ 2)⁻¹ := by
      simpa [iteratedDeriv_one, Real.norm_eq_abs] using hD.bound 1 x
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_right (D 0) (D 1))
      (inv_nonneg.mpr (sq_nonneg Q)))

/-- A smooth DFI cutoff and its derivative vanish throughout the inner
support gap. -/
theorem dfiWeight_and_deriv_eq_zero_of_pos_lt
    {Q x : ℝ} (w : DFIDeltaWeight Q) (hx0 : 0 < x) (hxQ : x < Q) :
    w x = 0 ∧ deriv w x = 0 := by
  have heq : w.toFun =ᶠ[𝓝 x] 0 := by
    have hopen : IsOpen (Set.Ioo (0 : ℝ) Q) := isOpen_Ioo
    filter_upwards [hopen.mem_nhds ⟨hx0, hxQ⟩] with y hy
    exact w.eq_zero_of_abs_lt (by simpa [abs_of_pos hy.1] using hy.2)
  refine ⟨heq.self_of_nhds, ?_⟩
  simpa using heq.deriv_eq

/-- A smooth DFI cutoff and its derivative vanish past the outer support
boundary on the positive axis. -/
theorem dfiWeight_and_deriv_eq_zero_of_twoQ_lt
    {Q x : ℝ} (w : DFIDeltaWeight Q) (hx : 2 * Q < x) :
    w x = 0 ∧ deriv w x = 0 := by
  have hx0 : 0 < x := (mul_pos two_pos w.Q_pos).trans hx
  have heq : w.toFun =ᶠ[𝓝 x] 0 := by
    have hopen : IsOpen {y : ℝ | 2 * Q < y} :=
      isOpen_lt continuous_const continuous_id
    filter_upwards [hopen.mem_nhds hx] with y hy
    have hy0 : 0 < y := (mul_pos two_pos w.Q_pos).trans hy
    exact w.eq_zero_of_two_mul_lt_abs (by simpa [abs_of_pos hy0] using hy)
  refine ⟨heq.self_of_nhds, ?_⟩
  simpa using heq.deriv_eq

theorem dfiWeight_and_deriv_eq_zero_of_abs_lt
    {Q x : ℝ} (w : DFIDeltaWeight Q) (hx : |x| < Q) :
    w x = 0 ∧ deriv w x = 0 := by
  have heq : w.toFun =ᶠ[𝓝 x] 0 := by
    have hopen : IsOpen {y : ℝ | |y| < Q} :=
      isOpen_lt continuous_abs continuous_const
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact w.eq_zero_of_abs_lt hy
  refine ⟨heq.self_of_nhds, ?_⟩
  simpa using heq.deriv_eq

theorem dfiWeight_and_deriv_eq_zero_of_twoQ_lt_abs
    {Q x : ℝ} (w : DFIDeltaWeight Q) (hx : 2 * Q < |x|) :
    w x = 0 ∧ deriv w x = 0 := by
  have heq : w.toFun =ᶠ[𝓝 x] 0 := by
    have hopen : IsOpen {y : ℝ | 2 * Q < |y|} :=
      isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact w.eq_zero_of_two_mul_lt_abs hy
  refine ⟨heq.self_of_nhds, ?_⟩
  simpa using heq.deriv_eq

/-- Direct-profile integrands vanish before the inner cutoff. -/
theorem dfiDirectIntegrand_eq_zero_of_pos_lt
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    {x : ℝ} (hx0 : 0 < x) (hxQ : x < Q) :
    (deriv w x / x - w x / x ^ 2) * Int.fract (x / q) = 0 := by
  obtain ⟨hw, hdw⟩ := dfiWeight_and_deriv_eq_zero_of_pos_lt w hx0 hxQ
  simp [hw, hdw]

/-- Direct-profile integrands vanish after the outer cutoff. -/
theorem dfiDirectIntegrand_eq_zero_of_twoQ_lt
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    {x : ℝ} (hx : 2 * Q < x) :
    (deriv w x / x - w x / x ^ 2) * Int.fract (x / q) = 0 := by
  obtain ⟨hw, hdw⟩ := dfiWeight_and_deriv_eq_zero_of_twoQ_lt w hx
  simp [hw, hdw]

/-- The direct derivative formula also holds at the removable point. -/
theorem deriv_dfiDeltaProfile_zero_all
    {Q : ℝ} (w : DFIDeltaWeight Q) (x : ℝ) :
    deriv (dfiDeltaProfile w 0) x = deriv w x / x - w x / x ^ 2 := by
  by_cases hx : x = 0
  · subst x
    have hlocal : dfiDeltaProfile w 0 =ᶠ[𝓝 (0 : ℝ)] 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) w.Q_pos] with y hy
      have hyQ : |y| < Q := by simpa [Real.dist_eq] using hy
      have hwy := w.eq_zero_of_abs_lt hyQ
      by_cases hy0 : y = 0
      · simp [hy0, dfiDeltaProfile]
      · simp [dfiDeltaProfile, hy0, hwy, w.zero]
    have hprofile : deriv (dfiDeltaProfile w 0) 0 = 0 := by
      simpa using hlocal.deriv_eq
    simp [hprofile, w.zero]
  · exact deriv_dfiDeltaProfile_zero w hx

/-- The direct derivative has the source scale `Q⁻³` on its annulus. -/
theorem abs_dfiDirectDerivative_le
    {Q C x : ℝ} (w : DFIDeltaWeight Q)
    (hC : 0 ≤ C)
    (hw : ∀ y : ℝ, |w y| ≤ C * Q⁻¹)
    (hdw : ∀ y : ℝ, |deriv w y| ≤ C * (Q ^ 2)⁻¹)
    (hx : x ∈ Set.Icc Q (2 * Q)) :
    |deriv w x / x - w x / x ^ 2| ≤ 2 * C / Q ^ 3 := by
  have hxpos : 0 < x := w.Q_pos.trans_le hx.1
  have hQ2 : 0 < Q ^ 2 := pow_pos w.Q_pos _
  have hx2 : 0 < x ^ 2 := pow_pos hxpos _
  calc
    |deriv w x / x - w x / x ^ 2| ≤
        |deriv w x / x| + |w x / x ^ 2| := abs_sub _ _
    _ = |deriv w x| / x + |w x| / x ^ 2 := by
      rw [abs_div, abs_of_pos hxpos, abs_div, abs_of_pos hx2]
    _ ≤ (C / Q ^ 2) / Q + (C / Q) / Q ^ 2 := by
      have hd : |deriv w x| / x ≤ (C / Q ^ 2) / Q := by
        calc
          |deriv w x| / x ≤ (C / Q ^ 2) / x :=
            div_le_div_of_nonneg_right (by simpa [div_eq_mul_inv] using hdw x)
              hxpos.le
          _ ≤ (C / Q ^ 2) / Q :=
            div_le_div_of_nonneg_left (div_nonneg hC hQ2.le) w.Q_pos hx.1
      have hv : |w x| / x ^ 2 ≤ (C / Q) / Q ^ 2 := by
        calc
          |w x| / x ^ 2 ≤ (C / Q) / x ^ 2 :=
            div_le_div_of_nonneg_right (by simpa [div_eq_mul_inv] using hw x)
              hx2.le
          _ ≤ (C / Q) / Q ^ 2 :=
            div_le_div_of_nonneg_left (div_nonneg hC w.Q_pos.le) hQ2
              (pow_le_pow_left₀ w.Q_pos.le hx.1 2)
      exact add_le_add hd hv
    _ = 2 * C / Q ^ 3 := by field_simp [w.Q_pos.ne']; ring

/-- The inverted part of the profile derivative. -/
noncomputable def dfiInvertedDerivative {Q : ℝ} (w : DFIDeltaWeight Q)
    (u x : ℝ) : ℝ :=
  u * deriv w (u / x) / x ^ 3 + w (u / x) / x ^ 2

/-- Exact direct/inverted splitting of the DFI profile derivative away
from the removable point. -/
theorem deriv_dfiDeltaProfile_eq_direct_add_inverted
    {Q : ℝ} (w : DFIDeltaWeight Q) (u : ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (dfiDeltaProfile w u) x =
      (deriv w x / x - w x / x ^ 2) + dfiInvertedDerivative w u x := by
  rw [deriv_dfiDeltaProfile w u x hx]
  dsimp [dfiInvertedDerivative]
  field_simp [hx]
  ring

/-- The direct part of equation (20) has both the `Q⁻²` and `(qQ)⁻¹`
bounds whose minimum gives the first denominator in DFI equation (19). -/
theorem abs_integral_dfiDirect_le
    {Q C : ℝ} (w : DFIDeltaWeight Q) (hC : 0 < C)
    (hw : ∀ y : ℝ, |w y| ≤ C * Q⁻¹)
    (hdw : ∀ y : ℝ, |deriv w y| ≤ C * (Q ^ 2)⁻¹)
    (q : ℕ) (hq : 0 < q) (u : ℝ) :
    |∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
        (deriv w x / x - w x / x ^ 2) * Int.fract (x / q)| ≤
      8 * C * ((q : ℝ) * Q + Q ^ 2)⁻¹ := by
  let B : ℝ := (q * dfiDeltaRadius Q u : ℕ)
  let F : ℝ → ℝ := fun x =>
    (deriv w x / x - w x / x ^ 2) * Int.fract (x / q)
  have hqreal : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hR := dfiDeltaRadius_spec (Q := Q) (u := u)
  have hRleB : (dfiDeltaRadius Q u : ℝ) ≤ B := by
    dsimp [B]
    exact_mod_cast Nat.le_mul_of_pos_left (dfiDeltaRadius Q u) hq
  have htwoQB : 2 * Q ≤ B := by
    have : 2 * Q < (dfiDeltaRadius Q u : ℝ) := by
      nlinarith [abs_nonneg u, div_nonneg (abs_nonneg u) w.Q_pos.le]
    exact this.le.trans hRleB
  have hleft : ∀ x ∈ Set.Ioo (0 : ℝ) Q, F x = 0 := by
    intro x hx
    exact dfiDirectIntegrand_eq_zero_of_pos_lt w q hx.1 hx.2
  have hright : ∀ x ∈ Set.Ioo (2 * Q) B, F x = 0 := by
    intro x hx
    exact dfiDirectIntegrand_eq_zero_of_twoQ_lt w q hx.1
  have hdirectCont : Continuous (fun x : ℝ => deriv w x / x - w x / x ^ 2) := by
    rw [show (fun x : ℝ => deriv w x / x - w x / x ^ 2) =
        deriv (dfiDeltaProfile w 0) by
      funext x
      exact (deriv_dfiDeltaProfile_zero_all w x).symm]
    exact (contDiff_dfiDeltaProfile w 0).continuous_deriv (by simp)
  have hdirectInt : IntervalIntegrable
      (fun x : ℝ => deriv w x / x - w x / x ^ 2)
      MeasureTheory.volume 0 B := hdirectCont.intervalIntegrable _ _
  have hFInt : IntervalIntegrable F MeasureTheory.volume 0 B := by
    dsimp [F]
    exact ⟨hdirectInt.1.mul_bdd
        ((measurable_id.div_const (q : ℝ)).fract.aestronglyMeasurable)
        (by filter_upwards [] with x
            rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
            exact (Int.fract_lt_one _).le),
      hdirectInt.2.mul_bdd
        ((measurable_id.div_const (q : ℝ)).fract.aestronglyMeasurable)
        (by filter_upwards [] with x
            rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
            exact (Int.fract_lt_one _).le)⟩
  have hQtwoQ : Q ≤ 2 * Q := by nlinarith [w.Q_pos]
  have h0B : (0 : ℝ) ≤ B :=
    (mul_nonneg (by norm_num) w.Q_pos.le).trans htwoQB
  have h0Q : IntervalIntegrable F MeasureTheory.volume 0 Q :=
    hFInt.mono_set (by
      intro x hx
      rw [uIcc_of_le w.Q_pos.le] at hx
      rw [uIcc_of_le h0B]
      exact ⟨hx.1, hx.2.trans (hQtwoQ.trans htwoQB)⟩)
  have hQ2Q : IntervalIntegrable F MeasureTheory.volume Q (2 * Q) :=
    hFInt.mono_set (by
      intro x hx
      rw [uIcc_of_le (by nlinarith [w.Q_pos])] at hx
      rw [uIcc_of_le h0B]
      exact ⟨w.Q_pos.le.trans hx.1, hx.2.trans htwoQB⟩)
  have h2QB : IntervalIntegrable F MeasureTheory.volume (2 * Q) B :=
    hFInt.mono_set (by
      intro x hx
      rw [uIcc_of_le htwoQB] at hx
      rw [uIcc_of_le h0B]
      exact ⟨(mul_pos two_pos w.Q_pos).le.trans hx.1, hx.2⟩)
  have hleftZero : (∫ x in (0 : ℝ)..Q, F x) = 0 := by
    calc
      (∫ x in (0 : ℝ)..Q, F x) = ∫ _x in (0 : ℝ)..Q, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume Q] with x hxQ
        intro hx
        rw [uIoc_of_le w.Q_pos.le] at hx
        exact hleft x ⟨hx.1, lt_of_le_of_ne hx.2 hxQ⟩
      _ = 0 := intervalIntegral.integral_zero
  have hrightZero : (∫ x in (2 * Q)..B, F x) = 0 := by
    calc
      (∫ x in (2 * Q)..B, F x) = ∫ _x in (2 * Q)..B, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume B] with x hxB
        intro hx
        rw [uIoc_of_le htwoQB] at hx
        exact hright x ⟨hx.1, lt_of_le_of_ne hx.2 hxB⟩
      _ = 0 := intervalIntegral.integral_zero
  have hrestrict : (∫ x in (0 : ℝ)..B, F x) = ∫ x in Q..(2 * Q), F x := by
    calc
      (∫ x in (0 : ℝ)..B, F x) =
          (∫ x in (0 : ℝ)..Q, F x) + ∫ x in Q..B, F x := by
        rw [intervalIntegral.integral_add_adjacent_intervals h0Q (hQ2Q.trans h2QB)]
      _ = (∫ x in Q..(2 * Q), F x) + ∫ x in (2 * Q)..B, F x := by
        rw [hleftZero, zero_add,
          intervalIntegral.integral_add_adjacent_intervals hQ2Q h2QB]
      _ = ∫ x in Q..(2 * Q), F x := by rw [hrightZero, add_zero]
  have hfractOne : ∀ x ∈ Set.Icc Q (2 * Q), |Int.fract (x / q)| ≤ 1 := by
    intro x hx
    exact (abs_fract_le_dfiFractMajorant q hq
      (w.Q_pos.le.trans hx.1)).trans (dfiFractMajorant_le_one q x)
  have hfractDiv : ∀ x ∈ Set.Icc Q (2 * Q),
      |Int.fract (x / q)| ≤ x / q := by
    intro x hx
    exact (abs_fract_le_dfiFractMajorant q hq
      (w.Q_pos.le.trans hx.1)).trans (dfiFractMajorant_le_div q x)
  have hboundOne : |∫ x in Q..(2 * Q), F x| ≤ 4 * C / Q ^ 2 := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 2 * C / Q ^ 3) (f := F) (a := Q) (b := 2 * Q) (by
        intro x hx
        rw [uIoc_of_le (by nlinarith [w.Q_pos])] at hx
        have hx' : x ∈ Set.Icc Q (2 * Q) := ⟨hx.1.le, hx.2⟩
        simp only [Real.norm_eq_abs, F, abs_mul]
        calc
          |deriv w x / x - w x / x ^ 2| * |Int.fract (x / q)| ≤
              (2 * C / Q ^ 3) * 1 :=
            mul_le_mul (abs_dfiDirectDerivative_le w hC.le hw hdw hx')
              (hfractOne x hx') (abs_nonneg _)
              (div_nonneg (mul_nonneg two_pos.le hC.le) (pow_pos w.Q_pos 3).le)
          _ = 2 * C / Q ^ 3 := by ring)
    calc
      |∫ x in Q..(2 * Q), F x| ≤
          (2 * C / Q ^ 3) * |2 * Q - Q| := hnorm
      _ = 2 * C / Q ^ 2 := by
        rw [abs_of_pos (by linarith [w.Q_pos])]
        field_simp [w.Q_pos.ne']
        ring
      _ ≤ 4 * C / Q ^ 2 := by
        have hinv : 0 ≤ (Q ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg Q)
        simp only [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by nlinarith [hC]) hinv
  have hboundDiv : |∫ x in Q..(2 * Q), F x| ≤ 4 * C / ((q : ℝ) * Q) := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 4 * C / ((q : ℝ) * Q ^ 2)) (f := F) (a := Q) (b := 2 * Q) (by
        intro x hx
        rw [uIoc_of_le (by nlinarith [w.Q_pos])] at hx
        have hx' : x ∈ Set.Icc Q (2 * Q) := ⟨hx.1.le, hx.2⟩
        simp only [Real.norm_eq_abs, F, abs_mul]
        have hA := abs_dfiDirectDerivative_le w hC.le hw hdw hx'
        have hX : x ≤ 2 * Q := hx'.2
        calc
          |deriv w x / x - w x / x ^ 2| * |Int.fract (x / q)| ≤
              (2 * C / Q ^ 3) * (x / q) :=
            mul_le_mul hA (hfractDiv x hx') (abs_nonneg _)
              (div_nonneg (mul_nonneg two_pos.le hC.le) (pow_pos w.Q_pos 3).le)
          _ ≤ 4 * C / ((q : ℝ) * Q ^ 2) := by
            let D : ℝ := 2 * C / ((q : ℝ) * Q ^ 3)
            have hD : 0 ≤ D := by
              dsimp [D]
              exact div_nonneg (mul_nonneg two_pos.le hC.le)
                (mul_nonneg hqreal.le (pow_pos w.Q_pos 3).le)
            calc
              (2 * C / Q ^ 3) * (x / (q : ℝ)) = D * x := by
                dsimp [D]
                field_simp [w.Q_pos.ne', hqreal.ne']
              _ ≤ D * (2 * Q) := mul_le_mul_of_nonneg_left hX hD
              _ = 4 * C / ((q : ℝ) * Q ^ 2) := by
                dsimp [D]
                field_simp [w.Q_pos.ne', hqreal.ne']; ring_nf)
    calc
      |∫ x in Q..(2 * Q), F x| ≤
          (4 * C / ((q : ℝ) * Q ^ 2)) * |2 * Q - Q| := hnorm
      _ = 4 * C / ((q : ℝ) * Q) := by
        rw [abs_of_pos (by linarith [w.Q_pos])]
        field_simp [w.Q_pos.ne', hqreal.ne']
        ring
  rw [show (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
      (deriv w x / x - w x / x ^ 2) * Int.fract (x / q)) =
      ∫ x in (0 : ℝ)..B, F x by rfl, hrestrict]
  have hmin : |∫ x in Q..(2 * Q), F x| ≤
      4 * C * min (Q ^ 2)⁻¹ ((q : ℝ) * Q)⁻¹ := by
    rw [mul_min_of_nonneg _ _ (show 0 ≤ 4 * C by positivity)]
    apply le_min
    · simpa [div_eq_mul_inv] using hboundOne
    · simpa [div_eq_mul_inv] using hboundDiv
  have hcompare := min_inv_le_two_mul_inv_add
    (pow_pos w.Q_pos 2)
    (mul_pos hqreal w.Q_pos)
  calc
    |∫ x in Q..(2 * Q), F x| ≤
        4 * C * min (Q ^ 2)⁻¹ ((q : ℝ) * Q)⁻¹ := hmin
    _ ≤ 4 * C * (2 * (Q ^ 2 + (q : ℝ) * Q)⁻¹) :=
      mul_le_mul_of_nonneg_left hcompare (by positivity)
    _ = 8 * C * ((q : ℝ) * Q + Q ^ 2)⁻¹ := by ring

/-- On the inverted support interval, the differentiated reciprocal cutoff
has size `O(C Q / |u|²)`. -/
theorem abs_dfiInvertedDerivative_le
    {Q C u x : ℝ} (w : DFIDeltaWeight Q) (hC : 0 ≤ C)
    (hw : ∀ y : ℝ, |w y| ≤ C * Q⁻¹)
    (hdw : ∀ y : ℝ, |deriv w y| ≤ C * (Q ^ 2)⁻¹)
    (hu : u ≠ 0)
    (hx : x ∈ Set.Icc (|u| / (2 * Q)) (|u| / Q)) :
    |dfiInvertedDerivative w u x| ≤ 12 * C * Q / |u| ^ 2 := by
  have ha : 0 < |u| := abs_pos.mpr hu
  have htwoQ : 0 < 2 * Q := mul_pos two_pos w.Q_pos
  have hL : 0 < |u| / (2 * Q) := div_pos ha htwoQ
  have hxpos : 0 < x := hL.trans_le hx.1
  have hx2 : 0 < x ^ 2 := pow_pos hxpos _
  have hx3 : 0 < x ^ 3 := pow_pos hxpos _
  have hL2 : 0 < (|u| / (2 * Q)) ^ 2 := pow_pos hL _
  have hL3 : 0 < (|u| / (2 * Q)) ^ 3 := pow_pos hL _
  have hpow2 : (|u| / (2 * Q)) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ hL.le hx.1 2
  have hpow3 : (|u| / (2 * Q)) ^ 3 ≤ x ^ 3 :=
    pow_le_pow_left₀ hL.le hx.1 3
  have hfirst : |u * deriv w (u / x) / x ^ 3| ≤
      8 * C * Q / |u| ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos hx3]
    calc
      |u| * |deriv w (u / x)| / x ^ 3 ≤
          (|u| * (C / Q ^ 2)) / x ^ 3 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa [div_eq_mul_inv] using hdw (u / x)) (abs_nonneg u))
          hx3.le
      _ ≤ (|u| * (C / Q ^ 2)) / (|u| / (2 * Q)) ^ 3 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (abs_nonneg u) (div_nonneg hC (sq_nonneg Q))) hL3 hpow3
      _ = 8 * C * Q / |u| ^ 2 := by
        field_simp [ha.ne', w.Q_pos.ne']
        ring
  have hsecond : |w (u / x) / x ^ 2| ≤ 4 * C * Q / |u| ^ 2 := by
    rw [abs_div, abs_of_pos hx2]
    calc
      |w (u / x)| / x ^ 2 ≤ (C / Q) / x ^ 2 :=
        div_le_div_of_nonneg_right
          (by simpa [div_eq_mul_inv] using hw (u / x)) hx2.le
      _ ≤ (C / Q) / (|u| / (2 * Q)) ^ 2 :=
        div_le_div_of_nonneg_left (div_nonneg hC w.Q_pos.le) hL2 hpow2
      _ = 4 * C * Q / |u| ^ 2 := by
        field_simp [ha.ne', w.Q_pos.ne']
        ring
  dsimp [dfiInvertedDerivative]
  calc
    |u * deriv w (u / x) / x ^ 3 + w (u / x) / x ^ 2| ≤
        |u * deriv w (u / x) / x ^ 3| + |w (u / x) / x ^ 2| :=
      abs_add_le _ _
    _ ≤ 8 * C * Q / |u| ^ 2 + 4 * C * Q / |u| ^ 2 :=
      add_le_add hfirst hsecond
    _ = 12 * C * Q / |u| ^ 2 := by ring

/-- The inverted derivative is supported on the reciprocal annulus. -/
theorem dfiInvertedIntegrand_eq_zero_of_pos_lt
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) {u x : ℝ}
    (hx0 : 0 < x) (hx : x < |u| / (2 * Q)) :
    dfiInvertedDerivative w u x * Int.fract (x / q) = 0 := by
  have hlarge : 2 * Q < |u / x| := by
    rw [abs_div, abs_of_pos hx0]
    rw [lt_div_iff₀ hx0]
    have := (lt_div_iff₀ (mul_pos two_pos w.Q_pos)).mp hx
    nlinarith
  obtain ⟨hw, hdw⟩ := dfiWeight_and_deriv_eq_zero_of_twoQ_lt_abs w hlarge
  simp [dfiInvertedDerivative, hw, hdw]

theorem dfiInvertedIntegrand_eq_zero_of_div_lt
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) {u x : ℝ}
    (hu : u ≠ 0) (hx : |u| / Q < x) :
    dfiInvertedDerivative w u x * Int.fract (x / q) = 0 := by
  have hxpos : 0 < x := (div_pos (abs_pos.mpr hu) w.Q_pos).trans hx
  have hsmall : |u / x| < Q := by
    rw [abs_div, abs_of_pos hxpos]
    rw [div_lt_iff₀ hxpos]
    have := (div_lt_iff₀ w.Q_pos).mp hx
    nlinarith
  obtain ⟨hw, hdw⟩ := dfiWeight_and_deriv_eq_zero_of_abs_lt w hsmall
  simp [dfiInvertedDerivative, hw, hdw]

/-- The direct/inverted derivative splitting is valid at the removable
point as well. -/
theorem deriv_dfiDeltaProfile_eq_direct_add_inverted_all
    {Q : ℝ} (w : DFIDeltaWeight Q) (u x : ℝ) :
    deriv (dfiDeltaProfile w u) x =
      (deriv w x / x - w x / x ^ 2) + dfiInvertedDerivative w u x := by
  by_cases hx : x = 0
  · subst x
    have huCase : deriv (dfiDeltaProfile w u) 0 = 0 := by
      by_cases hu : u = 0
      · subst u
        simpa using deriv_dfiDeltaProfile_zero_all w 0
      · have ha : 0 < |u| := abs_pos.mpr hu
        let δ : ℝ := min Q (|u| / (2 * Q))
        have hδ : 0 < δ := lt_min w.Q_pos
          (div_pos ha (mul_pos two_pos w.Q_pos))
        have heq : dfiDeltaProfile w u =ᶠ[𝓝 (0 : ℝ)] 0 := by
          filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with y hy
          have hyδ : |y| < δ := by simpa [Real.dist_eq] using hy
          have hyQ : |y| < Q := hyδ.trans_le (min_le_left _ _)
          have hwy : w y = 0 := w.eq_zero_of_abs_lt hyQ
          by_cases hy0 : y = 0
          · simp [hy0, dfiDeltaProfile]
          · have hyabs : 0 < |y| := abs_pos.mpr hy0
            have hysmall : |y| < |u| / (2 * Q) :=
              hyδ.trans_le (min_le_right _ _)
            have hlarge : 2 * Q < |u / y| := by
              rw [abs_div]
              rw [lt_div_iff₀ hyabs]
              have := (lt_div_iff₀ (mul_pos two_pos w.Q_pos)).mp hysmall
              nlinarith
            have hwuy : w (u / y) = 0 :=
              w.eq_zero_of_two_mul_lt_abs hlarge
            simp [dfiDeltaProfile, hy0, hwy, hwuy]
        simpa using heq.deriv_eq
    simp [huCase, dfiInvertedDerivative, w.zero]
  · exact deriv_dfiDeltaProfile_eq_direct_add_inverted w u hx

/-- The inverted contribution supplies the second denominator in DFI (19). -/
theorem abs_integral_dfiInverted_le
    {Q C : ℝ} (w : DFIDeltaWeight Q) (hC : 0 < C)
    (hw : ∀ y : ℝ, |w y| ≤ C * Q⁻¹)
    (hdw : ∀ y : ℝ, |deriv w y| ≤ C * (Q ^ 2)⁻¹)
    (q : ℕ) (hq : 0 < q) (u : ℝ) (hu : u ≠ 0) :
    |∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
        dfiInvertedDerivative w u x * Int.fract (x / q)| ≤
      24 * C * ((q : ℝ) * Q + |u|)⁻¹ := by
  let a : ℝ := |u|
  let L : ℝ := a / (2 * Q)
  let U : ℝ := a / Q
  let B : ℝ := (q * dfiDeltaRadius Q u : ℕ)
  let F : ℝ → ℝ := fun x =>
    dfiInvertedDerivative w u x * Int.fract (x / q)
  have ha : 0 < a := by simpa [a] using abs_pos.mpr hu
  have hqreal : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hL : 0 < L := by
    dsimp [L]
    exact div_pos ha (mul_pos two_pos w.Q_pos)
  have hLUlt : L < U := by
    dsimp [L, U]
    exact div_lt_div_of_pos_left ha w.Q_pos (by nlinarith [w.Q_pos])
  have hLU : L ≤ U := by
    exact hLUlt.le
  have hR := dfiDeltaRadius_spec (Q := Q) (u := u)
  have hRleB : (dfiDeltaRadius Q u : ℝ) ≤ B := by
    dsimp [B]
    exact_mod_cast Nat.le_mul_of_pos_left (dfiDeltaRadius Q u) hq
  have hUB : U ≤ B := by
    have : U < (dfiDeltaRadius Q u : ℝ) := by
      dsimp [U, a]
      nlinarith [mul_pos two_pos w.Q_pos]
    exact this.le.trans hRleB
  have hleft : ∀ x ∈ Set.Ioo (0 : ℝ) L, F x = 0 := by
    intro x hx
    exact dfiInvertedIntegrand_eq_zero_of_pos_lt w q hx.1 (by simpa [L, a] using hx.2)
  have hright : ∀ x ∈ Set.Ioo U B, F x = 0 := by
    intro x hx
    exact dfiInvertedIntegrand_eq_zero_of_div_lt w q hu (by simpa [U, a] using hx.1)
  have hinvCont : Continuous (dfiInvertedDerivative w u) := by
    rw [show dfiInvertedDerivative w u = fun x : ℝ =>
        deriv (dfiDeltaProfile w u) x -
          (deriv w x / x - w x / x ^ 2) by
      funext x
      rw [deriv_dfiDeltaProfile_eq_direct_add_inverted_all w u x]
      ring]
    exact ((contDiff_dfiDeltaProfile w u).continuous_deriv (by simp)).sub
      (by
        rw [show (fun x : ℝ => deriv w x / x - w x / x ^ 2) =
            deriv (dfiDeltaProfile w 0) by
          funext x
          exact (deriv_dfiDeltaProfile_zero_all w x).symm]
        exact (contDiff_dfiDeltaProfile w 0).continuous_deriv (by simp))
  have hinvInt : IntervalIntegrable (dfiInvertedDerivative w u)
      MeasureTheory.volume 0 B := hinvCont.intervalIntegrable _ _
  have hFInt : IntervalIntegrable F MeasureTheory.volume 0 B := by
    dsimp [F]
    exact ⟨hinvInt.1.mul_bdd
        ((measurable_id.div_const (q : ℝ)).fract.aestronglyMeasurable)
        (by filter_upwards [] with x
            rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
            exact (Int.fract_lt_one _).le),
      hinvInt.2.mul_bdd
        ((measurable_id.div_const (q : ℝ)).fract.aestronglyMeasurable)
        (by filter_upwards [] with x
            rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
            exact (Int.fract_lt_one _).le)⟩
  have h0B : (0 : ℝ) ≤ B := hL.le.trans (hLU.trans hUB)
  have h0L : IntervalIntegrable F MeasureTheory.volume 0 L :=
    hFInt.mono_set (by
      intro x hx
      rw [uIcc_of_le hL.le] at hx
      rw [uIcc_of_le h0B]
      exact ⟨hx.1, hx.2.trans (hLU.trans hUB)⟩)
  have hLUInt : IntervalIntegrable F MeasureTheory.volume L U :=
    hFInt.mono_set (by
      intro x hx
      rw [uIcc_of_le hLU] at hx
      rw [uIcc_of_le h0B]
      exact ⟨hL.le.trans hx.1, hx.2.trans hUB⟩)
  have hUBInt : IntervalIntegrable F MeasureTheory.volume U B :=
    hFInt.mono_set (by
      intro x hx
      rw [uIcc_of_le hUB] at hx
      rw [uIcc_of_le h0B]
      exact ⟨hL.le.trans (hLU.trans hx.1), hx.2⟩)
  have hleftZero : (∫ x in (0 : ℝ)..L, F x) = 0 := by
    calc
      (∫ x in (0 : ℝ)..L, F x) = ∫ _x in (0 : ℝ)..L, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume L] with x hxL
        intro hx
        rw [uIoc_of_le hL.le] at hx
        exact hleft x ⟨hx.1, lt_of_le_of_ne hx.2 hxL⟩
      _ = 0 := intervalIntegral.integral_zero
  have hrightZero : (∫ x in U..B, F x) = 0 := by
    calc
      (∫ x in U..B, F x) = ∫ _x in U..B, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume B] with x hxB
        intro hx
        rw [uIoc_of_le hUB] at hx
        exact hright x ⟨hx.1, lt_of_le_of_ne hx.2 hxB⟩
      _ = 0 := intervalIntegral.integral_zero
  have hrestrict : (∫ x in (0 : ℝ)..B, F x) = ∫ x in L..U, F x := by
    calc
      (∫ x in (0 : ℝ)..B, F x) =
          (∫ x in (0 : ℝ)..L, F x) + ∫ x in L..B, F x := by
        rw [intervalIntegral.integral_add_adjacent_intervals h0L
          (hLUInt.trans hUBInt)]
      _ = (∫ x in L..U, F x) + ∫ x in U..B, F x := by
        rw [hleftZero, zero_add,
          intervalIntegral.integral_add_adjacent_intervals hLUInt hUBInt]
      _ = ∫ x in L..U, F x := by rw [hrightZero, add_zero]
  have hfractOne : ∀ x ∈ Set.Icc L U, |Int.fract (x / q)| ≤ 1 := by
    intro x hx
    exact (abs_fract_le_dfiFractMajorant q hq (hL.le.trans hx.1)).trans
      (dfiFractMajorant_le_one q x)
  have hfractDiv : ∀ x ∈ Set.Icc L U, |Int.fract (x / q)| ≤ x / q := by
    intro x hx
    exact (abs_fract_le_dfiFractMajorant q hq (hL.le.trans hx.1)).trans
      (dfiFractMajorant_le_div q x)
  have hpoint : ∀ x ∈ Set.Icc L U,
      |dfiInvertedDerivative w u x| ≤ 12 * C * Q / a ^ 2 := by
    intro x hx
    simpa [L, U, a] using abs_dfiInvertedDerivative_le w hC.le hw hdw hu hx
  have hboundOne : |∫ x in L..U, F x| ≤ 12 * C / a := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 12 * C * Q / a ^ 2) (f := F) (a := L) (b := U) (by
        intro x hx
        rw [uIoc_of_le hLU] at hx
        have hx' : x ∈ Set.Icc L U := ⟨hx.1.le, hx.2⟩
        simp only [Real.norm_eq_abs, F, abs_mul]
        exact (mul_le_mul (hpoint x hx') (hfractOne x hx') (abs_nonneg _)
          (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC.le) w.Q_pos.le)
            (pow_pos ha 2).le)).trans_eq (mul_one _))
    calc
      |∫ x in L..U, F x| ≤ (12 * C * Q / a ^ 2) * |U - L| := hnorm
      _ = 6 * C / a := by
        rw [abs_of_pos (sub_pos.mpr hLUlt)]
        dsimp [L, U]
        field_simp [ha.ne', w.Q_pos.ne']
        ring
      _ ≤ 12 * C / a := by
        have hainv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
        simp only [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by nlinarith [hC]) hainv
  have hboundDiv : |∫ x in L..U, F x| ≤ 12 * C / ((q : ℝ) * Q) := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 12 * C / (a * (q : ℝ))) (f := F) (a := L) (b := U) (by
        intro x hx
        rw [uIoc_of_le hLU] at hx
        have hx' : x ∈ Set.Icc L U := ⟨hx.1.le, hx.2⟩
        simp only [Real.norm_eq_abs, F, abs_mul]
        calc
          |dfiInvertedDerivative w u x| * |Int.fract (x / q)| ≤
              (12 * C * Q / a ^ 2) * (x / q) :=
            mul_le_mul (hpoint x hx') (hfractDiv x hx') (abs_nonneg _)
              (div_nonneg
                (mul_nonneg (mul_nonneg (by norm_num) hC.le) w.Q_pos.le)
                (pow_pos ha 2).le)
          _ ≤ 12 * C / (a * (q : ℝ)) := by
            let D : ℝ := 12 * C * Q / (a ^ 2 * (q : ℝ))
            have hD : 0 ≤ D := by
              dsimp [D]
              exact div_nonneg
                (mul_nonneg (mul_nonneg (by norm_num) hC.le) w.Q_pos.le)
                (mul_nonneg (pow_pos ha 2).le hqreal.le)
            calc
              (12 * C * Q / a ^ 2) * (x / (q : ℝ)) = D * x := by
                dsimp [D]
                field_simp [ha.ne', hqreal.ne']
              _ ≤ D * U := mul_le_mul_of_nonneg_left hx'.2 hD
              _ = 12 * C / (a * (q : ℝ)) := by
                dsimp [D, U]
                field_simp [ha.ne', hqreal.ne', w.Q_pos.ne'])
    calc
      |∫ x in L..U, F x| ≤
          (12 * C / (a * (q : ℝ))) * |U - L| := hnorm
      _ = 6 * C / ((q : ℝ) * Q) := by
        rw [abs_of_pos (sub_pos.mpr hLUlt)]
        dsimp [L, U]
        field_simp [ha.ne', hqreal.ne', w.Q_pos.ne']
        ring
      _ ≤ 12 * C / ((q : ℝ) * Q) := by
        have hinv : 0 ≤ ((q : ℝ) * Q)⁻¹ :=
          inv_nonneg.mpr (mul_nonneg hqreal.le w.Q_pos.le)
        simp only [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by nlinarith [hC]) hinv
  rw [show (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
      dfiInvertedDerivative w u x * Int.fract (x / q)) =
      ∫ x in (0 : ℝ)..B, F x by rfl, hrestrict]
  have hmin : |∫ x in L..U, F x| ≤
      12 * C * min a⁻¹ ((q : ℝ) * Q)⁻¹ := by
    rw [mul_min_of_nonneg _ _ (show 0 ≤ 12 * C by positivity)]
    apply le_min
    · simpa [div_eq_mul_inv] using hboundOne
    · simpa [div_eq_mul_inv] using hboundDiv
  have hcompare := min_inv_le_two_mul_inv_add ha (mul_pos hqreal w.Q_pos)
  calc
    |∫ x in L..U, F x| ≤ 12 * C * min a⁻¹ ((q : ℝ) * Q)⁻¹ := hmin
    _ ≤ 12 * C * (2 * (a + (q : ℝ) * Q)⁻¹) :=
      mul_le_mul_of_nonneg_left hcompare (by positivity)
    _ = 24 * C * ((q : ℝ) * Q + |u|)⁻¹ := by
      dsimp [a]
      ring

/-- Multiplication by the bounded fractional-part sawtooth preserves
interval integrability. -/
theorem intervalIntegrable_mul_fract_of_continuous
    (g : ℝ → ℝ) (hg : Continuous g) (q : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => g x * Int.fract (x / q))
      MeasureTheory.volume a b := by
  have hgInt : IntervalIntegrable g MeasureTheory.volume a b :=
    hg.intervalIntegrable _ _
  exact ⟨hgInt.1.mul_bdd
      ((measurable_id.div_const (q : ℝ)).fract.aestronglyMeasurable)
      (by filter_upwards [] with x
          rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
          exact (Int.fract_lt_one _).le),
    hgInt.2.mul_bdd
      ((measurable_id.div_const (q : ℝ)).fract.aestronglyMeasurable)
      (by filter_upwards [] with x
          rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
          exact (Int.fract_lt_one _).le)⟩

/-- The mean term retained by the corrected equation (20) at `u = 0`
has precisely the `(qQ)⁻¹` scale. -/
theorem abs_integral_dfiProfile_zero_le
    {Q C : ℝ} (w : DFIDeltaWeight Q) (hC : 0 < C)
    (hw : ∀ y : ℝ, |w y| ≤ C * Q⁻¹)
    (q : ℕ) (hq : 0 < q) :
    |∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q 0 : ℕ),
        dfiDeltaProfile w 0 x| ≤ C / Q := by
  let B : ℝ := (q * dfiDeltaRadius Q 0 : ℕ)
  let F : ℝ → ℝ := dfiDeltaProfile w 0
  have hR := dfiDeltaRadius_spec (Q := Q) (u := (0 : ℝ))
  have hRleB : (dfiDeltaRadius Q 0 : ℝ) ≤ B := by
    dsimp [B]
    exact_mod_cast Nat.le_mul_of_pos_left (dfiDeltaRadius Q 0) hq
  have htwoQB : 2 * Q ≤ B := by
    have : 2 * Q < (dfiDeltaRadius Q 0 : ℝ) := by simpa using hR
    exact this.le.trans hRleB
  have hleft : ∀ x ∈ Set.Ioo (0 : ℝ) Q, F x = 0 := by
    intro x hx
    have habs : |x| < Q := by rw [abs_of_pos hx.1]; exact hx.2
    have hwx := w.eq_zero_of_abs_lt habs
    simp [F, dfiDeltaProfile, hx.1.ne', hwx, w.zero]
  have hright : ∀ x ∈ Set.Ioo (2 * Q) B, F x = 0 := by
    intro x hx
    have hx0 : 0 < x := (mul_pos two_pos w.Q_pos).trans hx.1
    have habs : 2 * Q < |x| := by rw [abs_of_pos hx0]; exact hx.1
    have hwx := w.eq_zero_of_two_mul_lt_abs habs
    simp [F, dfiDeltaProfile, hx0.ne', hwx, w.zero]
  have hrestrict : (∫ x in (0 : ℝ)..B, F x) = ∫ x in Q..(2 * Q), F x :=
    intervalIntegral_eq_subinterval_of_eq_zero F
      (contDiff_dfiDeltaProfile w 0).continuous w.Q_pos.le htwoQB hleft hright
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := C / Q ^ 2) (f := F) (a := Q) (b := 2 * Q) (by
      intro x hx
      rw [uIoc_of_le (by nlinarith [w.Q_pos])] at hx
      have hxpos : 0 < x := w.Q_pos.trans hx.1
      simp only [Real.norm_eq_abs, F]
      rw [show dfiDeltaProfile w 0 x = w x / x by
        simp [dfiDeltaProfile, hxpos.ne', w.zero], abs_div, abs_of_pos hxpos]
      calc
        |w x| / x ≤ (C / Q) / x :=
          div_le_div_of_nonneg_right (by simpa [div_eq_mul_inv] using hw x) hxpos.le
        _ ≤ (C / Q) / Q :=
          div_le_div_of_nonneg_left (div_nonneg hC.le w.Q_pos.le) w.Q_pos hx.1.le
        _ = C / Q ^ 2 := by field_simp [w.Q_pos.ne'])
  rw [show (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q 0 : ℕ),
      dfiDeltaProfile w 0 x) = ∫ x in (0 : ℝ)..B, F x by rfl, hrestrict]
  calc
    |∫ x in Q..(2 * Q), F x| ≤ (C / Q ^ 2) * |2 * Q - Q| := hnorm
    _ = C / Q := by
      rw [abs_of_pos (by linarith [w.Q_pos])]
      field_simp [w.Q_pos.ne']
      ring

/-- DFI equation (19) for nonzero shifts, obtained by adding the exact
direct and inverted pieces of equation (20). -/
theorem dfiEquation19_of_ne_zero
    {Q C : ℝ} (w : DFIDeltaWeight Q) (hC : 0 < C)
    (hw : ∀ y : ℝ, |w y| ≤ C * Q⁻¹)
    (hdw : ∀ y : ℝ, |deriv w y| ≤ C * (Q ^ 2)⁻¹)
    (q : ℕ) (hq : 0 < q) (u : ℝ) (hu : u ≠ 0) :
    |dfiDeltaKernel w q u| ≤
      24 * C * (((q : ℝ) * Q + Q ^ 2)⁻¹ +
        ((q : ℝ) * Q + |u|)⁻¹) := by
  let B : ℝ := (q * dfiDeltaRadius Q u : ℕ)
  let D : ℝ → ℝ := fun x =>
    (deriv w x / x - w x / x ^ 2) * Int.fract (x / q)
  let I : ℝ → ℝ := fun x =>
    dfiInvertedDerivative w u x * Int.fract (x / q)
  have hdirectCont : Continuous (fun x : ℝ => deriv w x / x - w x / x ^ 2) := by
    rw [show (fun x : ℝ => deriv w x / x - w x / x ^ 2) =
        deriv (dfiDeltaProfile w 0) by
      funext x
      exact (deriv_dfiDeltaProfile_zero_all w x).symm]
    exact (contDiff_dfiDeltaProfile w 0).continuous_deriv (by simp)
  have hinvCont : Continuous (dfiInvertedDerivative w u) := by
    rw [show dfiInvertedDerivative w u = fun x : ℝ =>
        deriv (dfiDeltaProfile w u) x -
          (deriv w x / x - w x / x ^ 2) by
      funext x
      rw [deriv_dfiDeltaProfile_eq_direct_add_inverted_all w u x]
      ring]
    exact ((contDiff_dfiDeltaProfile w u).continuous_deriv (by simp)).sub hdirectCont
  have hDInt : IntervalIntegrable D MeasureTheory.volume 0 B := by
    simpa [D] using intervalIntegrable_mul_fract_of_continuous
      (fun x : ℝ => deriv w x / x - w x / x ^ 2) hdirectCont q 0 B
  have hIInt : IntervalIntegrable I MeasureTheory.volume 0 B := by
    simpa [I] using intervalIntegrable_mul_fract_of_continuous
      (dfiInvertedDerivative w u) hinvCont q 0 B
  have hsplit : (∫ x in (0 : ℝ)..B,
      deriv (dfiDeltaProfile w u) x * Int.fract (x / q)) =
      (∫ x in (0 : ℝ)..B, D x) + ∫ x in (0 : ℝ)..B, I x := by
    rw [← intervalIntegral.integral_add hDInt hIInt]
    apply intervalIntegral.integral_congr
    intro x _hx
    change deriv (dfiDeltaProfile w u) x * Int.fract (x / q) = D x + I x
    rw [deriv_dfiDeltaProfile_eq_direct_add_inverted_all w u x]
    dsimp [D, I]
    ring
  have hD := abs_integral_dfiDirect_le w hC hw hdw q hq u
  have hI := abs_integral_dfiInverted_le w hC hw hdw q hq u hu
  rw [dfiEquation20 w q hq u hu,
    show (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q u : ℕ),
      deriv (dfiDeltaProfile w u) x * Int.fract (x / q)) =
      ∫ x in (0 : ℝ)..B,
        deriv (dfiDeltaProfile w u) x * Int.fract (x / q) by rfl,
    hsplit]
  calc
    |(∫ x in (0 : ℝ)..B, D x) + ∫ x in (0 : ℝ)..B, I x| ≤
        |∫ x in (0 : ℝ)..B, D x| + |∫ x in (0 : ℝ)..B, I x| :=
      abs_add_le _ _
    _ ≤ 8 * C * ((q : ℝ) * Q + Q ^ 2)⁻¹ +
        24 * C * ((q : ℝ) * Q + |u|)⁻¹ := by
      exact add_le_add (by simpa [B, D] using hD) (by simpa [B, I] using hI)
    _ ≤ 24 * C * (((q : ℝ) * Q + Q ^ 2)⁻¹ +
        ((q : ℝ) * Q + |u|)⁻¹) := by
      have hfirst : 8 * C * ((q : ℝ) * Q + Q ^ 2)⁻¹ ≤
          24 * C * ((q : ℝ) * Q + Q ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (by nlinarith [hC])
          (inv_nonneg.mpr (add_nonneg
            (mul_nonneg (Nat.cast_nonneg q) w.Q_pos.le) (sq_nonneg Q)))
      nlinarith

/-- The zero-shift case of DFI equation (19), including the mean term that
is absent from the paper's printed equation (20). -/
theorem dfiEquation19_zero
    {Q C : ℝ} (w : DFIDeltaWeight Q) (hC : 0 < C)
    (hw : ∀ y : ℝ, |w y| ≤ C * Q⁻¹)
    (hdw : ∀ y : ℝ, |deriv w y| ≤ C * (Q ^ 2)⁻¹)
    (q : ℕ) (hq : 0 < q) :
    |dfiDeltaKernel w q 0| ≤
      24 * C * (((q : ℝ) * Q + Q ^ 2)⁻¹ +
        ((q : ℝ) * Q + |(0 : ℝ)|)⁻¹) := by
  let B : ℝ := (q * dfiDeltaRadius Q 0 : ℕ)
  have hqreal : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hmean := abs_integral_dfiProfile_zero_le w hC hw q hq
  have hdirect := abs_integral_dfiDirect_le w hC hw hdw q hq 0
  have hderivEq : (∫ x in (0 : ℝ)..B,
      deriv (dfiDeltaProfile w 0) x * Int.fract (x / q)) =
      ∫ x in (0 : ℝ)..B,
        (deriv w x / x - w x / x ^ 2) * Int.fract (x / q) := by
    apply intervalIntegral.integral_congr
    intro x _hx
    change deriv (dfiDeltaProfile w 0) x * Int.fract (x / q) =
      (deriv w x / x - w x / x ^ 2) * Int.fract (x / q)
    rw [deriv_dfiDeltaProfile_zero_all w x]
  rw [dfiDeltaKernel_euler_maclaurin_fract w q hq 0,
    show (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q 0 : ℕ),
      deriv (dfiDeltaProfile w 0) x * Int.fract (x / q)) =
      ∫ x in (0 : ℝ)..B,
        deriv (dfiDeltaProfile w 0) x * Int.fract (x / q) by rfl,
    hderivEq]
  have hmeanTerm : |(q : ℝ)⁻¹ *
      (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q 0 : ℕ),
        dfiDeltaProfile w 0 x)| ≤ C * ((q : ℝ) * Q)⁻¹ := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hqreal)]
    calc
      (q : ℝ)⁻¹ * |∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q 0 : ℕ),
          dfiDeltaProfile w 0 x| ≤ (q : ℝ)⁻¹ * (C / Q) :=
        mul_le_mul_of_nonneg_left hmean (inv_nonneg.mpr hqreal.le)
      _ = C * ((q : ℝ) * Q)⁻¹ := by
        field_simp [hqreal.ne', w.Q_pos.ne']
  have hdirect' : |∫ x in (0 : ℝ)..B,
      (deriv w x / x - w x / x ^ 2) * Int.fract (x / q)| ≤
      8 * C * ((q : ℝ) * Q + Q ^ 2)⁻¹ := by
    simpa [B] using hdirect
  calc
    |(q : ℝ)⁻¹ *
          (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q 0 : ℕ),
            dfiDeltaProfile w 0 x) +
        ∫ x in (0 : ℝ)..B,
          (deriv w x / x - w x / x ^ 2) * Int.fract (x / q)| ≤
        |(q : ℝ)⁻¹ *
          (∫ x in (0 : ℝ)..(q * dfiDeltaRadius Q 0 : ℕ),
            dfiDeltaProfile w 0 x)| +
        |∫ x in (0 : ℝ)..B,
          (deriv w x / x - w x / x ^ 2) * Int.fract (x / q)| :=
      abs_add_le _ _
    _ ≤ C * ((q : ℝ) * Q)⁻¹ +
        8 * C * ((q : ℝ) * Q + Q ^ 2)⁻¹ :=
      add_le_add hmeanTerm hdirect'
    _ ≤ 24 * C * (((q : ℝ) * Q + Q ^ 2)⁻¹ +
        ((q : ℝ) * Q + |(0 : ℝ)|)⁻¹) := by
      have hA : 0 ≤ ((q : ℝ) * Q + Q ^ 2)⁻¹ :=
        inv_nonneg.mpr (add_nonneg (mul_nonneg hqreal.le w.Q_pos.le) (sq_nonneg Q))
      have hB : 0 ≤ ((q : ℝ) * Q)⁻¹ :=
        inv_nonneg.mpr (mul_nonneg hqreal.le w.Q_pos.le)
      simp only [abs_zero, add_zero]
      nlinarith [mul_nonneg hC.le hA, mul_nonneg hC.le hB]

/-- DFI equation (19), uniformly in every positive modulus and every real
shift.  The constant depends only on the chosen normalized cutoff. -/
theorem dfiEquation19 {Q : ℝ} (w : DFIDeltaWeight Q) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ), 0 < q → ∀ u : ℝ,
      |dfiDeltaKernel w q u| ≤
        K * (((q : ℝ) * Q + Q ^ 2)⁻¹ +
          ((q : ℝ) * Q + |u|)⁻¹) := by
  obtain ⟨C, hC, hw, hdw⟩ := exists_dfiWeight_zero_one_bounds w
  refine ⟨24 * C, mul_pos (by norm_num) hC, ?_⟩
  intro q hq u
  by_cases hu : u = 0
  · subst u
    exact dfiEquation19_zero w hC hw hdw q hq
  · exact dfiEquation19_of_ne_zero w hC hw hdw q hq u hu

/-- DFI equation (19) with a constant determined solely by the fixed
equation-(9) profile. -/
theorem dfiEquation19_of_profile
    {Q : ℝ} {w : DFIDeltaWeight Q} {D : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D) (q : ℕ) (hq : 0 < q) (u : ℝ) :
    |dfiDeltaKernel w q u| ≤
      (24 * max (D 0) (D 1)) *
        (((q : ℝ) * Q + Q ^ 2)⁻¹ + ((q : ℝ) * Q + |u|)⁻¹) := by
  have hC : 0 < max (D 0) (D 1) :=
    (hD.positive 0).trans_le (le_max_left _ _)
  obtain ⟨hw, hdw⟩ := dfiWeight_zero_one_bounds_of_profile hD
  by_cases hu : u = 0
  · subst u
    exact dfiEquation19_zero w hC hw hdw q hq
  · exact dfiEquation19_of_ne_zero w hC hw hdw q hq u hu

end RiemannZeta.GuthMaynard
