import PrimeShell.ShiftKernel
import Zeta23.Taper

namespace PrimeShell

noncomputable section

open Set MeasureTheory Real
open Zeta23 Zeta23.PrimeSide

private theorem four_sine_midpoint_identity (a b c : ℝ) :
    Real.sin (a + b) + Real.sin (a - b) -
        Real.sin (c + b) - Real.sin (c - b) =
      4 * Real.cos ((a + c) / 2) * Real.cos b *
        Real.sin ((a - c) / 2) := by
  rw [show Real.sin (a + b) + Real.sin (a - b) -
      Real.sin (c + b) - Real.sin (c - b) =
      (Real.sin (a + b) + Real.sin (a - b)) -
        (Real.sin (c + b) + Real.sin (c - b)) by ring]
  rw [Real.sin_add_sin, Real.sin_add_sin]
  ring_nf
  rw [show Real.sin a * Real.cos b * 2 - Real.cos b * Real.sin c * 2 =
      2 * Real.cos b * (Real.sin a - Real.sin c) by ring]
  rw [Real.sin_sub_sin]
  ring_nf

/-- Exact pointwise formula for the two orientations of the difference-frequency
kernel.  The midpoint of the overlap interval is always `3T / 2 - x / 2`;
after the two orientations are added, the dependence on that midpoint becomes
the displayed global cosine factor. -/
theorem JmK_add_swap_eq
    {T y y' x : ℝ} (hθ : y - y' ≠ 0) :
    JmK T y y' x + JmK T y' y x =
      4 * Real.cos (3 * (y - y') * T / 2) *
        Real.cos (x * (y + y') / 2) *
        Real.sin ((y - y') * (T - |x|) / 2) / (y - y') := by
  have hθ' : y' - y ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hθ).symm
  rcases le_total x 0 with hx0 | hx0
  · have hmax : max (T - x) T = T - x := max_eq_left (by linarith)
    have hmin : min (2 * T - x) (2 * T) = 2 * T := min_eq_right (by linarith)
    have habs : |x| = -x := abs_of_nonpos hx0
    unfold JmK
    rw [hmax, hmin, Jker_of_ne hθ, Jker_of_ne hθ', habs]
    rw [show y' - y = -(y - y') by ring]
    field_simp [hθ]
    rw [show -((y - y') * 2 * T) + y' * x =
        -((y - y') * 2 * T - y' * x) by ring, Real.sin_neg]
    rw [show -((y - y') * (T - x)) + y' * x =
        -((y - y') * (T - x) - y' * x) by ring, Real.sin_neg]
    convert four_sine_midpoint_identity
      (2 * (y - y') * T + x * (y - y') / 2)
      (x * (y + y') / 2)
      ((y - y') * T - x * (y - y') / 2) using 1 <;> ring_nf
  · have hmax : max (T - x) T = T := max_eq_right (by linarith)
    have hmin : min (2 * T - x) (2 * T) = 2 * T - x := min_eq_left (by linarith)
    have habs : |x| = x := abs_of_nonneg hx0
    unfold JmK
    rw [hmax, hmin, Jker_of_ne hθ, Jker_of_ne hθ', habs]
    rw [show y' - y = -(y - y') by ring]
    field_simp [hθ]
    rw [show -((y - y') * (2 * T - x)) + y' * x =
        -((y - y') * (2 * T - x) - y' * x) by ring, Real.sin_neg]
    rw [show -((y - y') * T) + y' * x =
        -((y - y') * T - y' * x) by ring, Real.sin_neg]
    convert four_sine_midpoint_identity
      (2 * (y - y') * T - x * (y - y') / 2)
      (x * (y + y') / 2)
      ((y - y') * T + x * (y - y') / 2) using 1 <;> ring_nf

/-- If the midpoint cosine vanishes, the literal symmetrized kernel vanishes
pointwise on the complete overlap interval. -/
theorem JmK_add_swap_eq_zero_of_midpoint_cos_eq_zero
    {T y y' x : ℝ} (hθ : y - y' ≠ 0)
    (hcos : Real.cos (3 * (y - y') * T / 2) = 0) :
    JmK T y y' x + JmK T y' y x = 0 := by
  rw [JmK_add_swap_eq hθ, hcos]
  ring

/-- Integrated form of `JmK_add_swap_eq`.  This identity applies to the
actual `P.PhiR T` by specialization; it does not assume compact support or
replace the source kernel by a scalar weight. -/
theorem Aminus_add_swap_eq
    {T y y' : ℝ} (hθ : y - y' ≠ 0)
    (Phi : ℝ → ℝ) (hPhi : Continuous Phi) :
    Aminus Phi T y y' + Aminus Phi T y' y =
      ∫ x in Set.Icc (-T) T,
        Phi x ^ 2 *
          (4 * Real.cos (3 * (y - y') * T / 2) *
            Real.cos (x * (y + y') / 2) *
            Real.sin ((y - y') * (T - |x|) / 2) / (y - y')) := by
  unfold Aminus
  rw [← MeasureTheory.integral_add]
  · apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change Phi x ^ 2 * JmK T y y' x + Phi x ^ 2 * JmK T y' y x = _
    rw [← mul_add, JmK_add_swap_eq hθ]
  · exact ((hPhi.pow 2).mul (continuous_JmK T y y')).integrableOn_Icc
  · exact ((hPhi.pow 2).mul (continuous_JmK T y' y)).integrableOn_Icc

/-- Quantitative replacement of the exact truncated sine weight by its
value at the origin.  This is the off-diagonal analogue of Zeta23's
`abs_Aminus_diag_sub_le`: the entire truncation and the variation in
`|x|` cost at most one half of the first absolute moment. -/
theorem abs_truncated_sine_integral_sub_le
    {T q c : ℝ} (hT : 0 ≤ T) (hq : 0 < q)
    (Phi : ℝ → ℝ) (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|) :
    |(∫ x in Set.Icc (-T) T,
        Phi x ^ 2 * Real.cos (x * c) *
          (Real.sin (q * (T - |x|) / 2) / q)) -
      (Real.sin (q * T / 2) / q) *
        ∫ x, Phi x ^ 2 * Real.cos (x * c)| ≤
      (∫ x, Phi x ^ 2 * |x|) / 2 := by
  let f : ℝ → ℝ := fun x =>
    Phi x ^ 2 * Real.cos (x * c) *
      (Real.sin (q * (T - |x|) / 2) / q)
  let g : ℝ → ℝ := fun x => Phi x ^ 2 * Real.cos (x * c)
  have hfcont : Continuous f := by
    fun_prop
  have hA : Integrable ((Set.Icc (-T) T).indicator f) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hfcont.integrableOn_Icc
  have hg : Integrable g := by
    refine hPhi2.mul_bdd (c := 1) (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa [g] using Real.abs_cos_le_one (x * c)
  have hB : Integrable
      (fun x => (Real.sin (q * T / 2) / q) * g x) :=
    hg.const_mul _
  rw [← integral_indicator measurableSet_Icc, ← integral_const_mul,
    ← integral_sub hA hB]
  calc
    |∫ x, (Set.Icc (-T) T).indicator f x -
        (Real.sin (q * T / 2) / q) * g x| ≤
        ∫ x, |(Set.Icc (-T) T).indicator f x -
          (Real.sin (q * T / 2) / q) * g x| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, (Phi x ^ 2 * |x|) / 2 := by
      apply integral_mono (hA.sub hB).abs (hPhiAbs.div_const 2)
      intro x
      change |(Set.Icc (-T) T).indicator f x -
          (Real.sin (q * T / 2) / q) * g x| ≤
        (Phi x ^ 2 * |x|) / 2
      have hPhi0 : 0 ≤ Phi x ^ 2 := sq_nonneg _
      have hcos := Real.abs_cos_le_one (x * c)
      by_cases hx : x ∈ Set.Icc (-T) T
      · rw [Set.indicator_of_mem hx]
        change |Phi x ^ 2 * Real.cos (x * c) *
            (Real.sin (q * (T - |x|) / 2) / q) -
          (Real.sin (q * T / 2) / q) *
            (Phi x ^ 2 * Real.cos (x * c))| ≤ _
        rw [show Phi x ^ 2 * Real.cos (x * c) *
              (Real.sin (q * (T - |x|) / 2) / q) -
            (Real.sin (q * T / 2) / q) *
              (Phi x ^ 2 * Real.cos (x * c)) =
            Phi x ^ 2 * Real.cos (x * c) *
              ((Real.sin (q * (T - |x|) / 2) -
                Real.sin (q * T / 2)) / q) by ring]
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hq]
        have hsin := Real.abs_sin_sub_sin_le
          (q * (T - |x|) / 2) (q * T / 2)
        have hweight :
            |Real.sin (q * (T - |x|) / 2) -
              Real.sin (q * T / 2)| / q ≤ |x| / 2 := by
          calc
            |Real.sin (q * (T - |x|) / 2) -
                Real.sin (q * T / 2)| / q ≤
                |q * (T - |x|) / 2 - q * T / 2| / q :=
              div_le_div_of_nonneg_right hsin hq.le
            _ = |x| / 2 := by
              rw [show q * (T - |x|) / 2 - q * T / 2 =
                -(q * |x| / 2) by ring, abs_neg, abs_div,
                abs_mul, abs_of_pos hq, abs_abs]
              field_simp
              ring
        calc
          |Phi x ^ 2| * |Real.cos (x * c)| *
              (|Real.sin (q * (T - |x|) / 2) -
                Real.sin (q * T / 2)| / q) ≤
              Phi x ^ 2 * 1 * (|x| / 2) := by
            rw [abs_of_nonneg hPhi0]
            gcongr
          _ = (Phi x ^ 2 * |x|) / 2 := by ring
      · rw [Set.indicator_of_notMem hx, zero_sub, abs_neg]
        change |(Real.sin (q * T / 2) / q) *
          (Phi x ^ 2 * Real.cos (x * c))| ≤ _
        rw [abs_mul, abs_div, abs_of_pos hq, abs_mul,
          abs_of_nonneg hPhi0]
        have hs : |Real.sin (q * T / 2)| / q ≤ T / 2 := by
          calc
            |Real.sin (q * T / 2)| / q ≤ |q * T / 2| / q :=
              div_le_div_of_nonneg_right Real.abs_sin_le_abs hq.le
            _ = T / 2 := by
              rw [abs_div, abs_mul, abs_of_pos hq, abs_of_nonneg hT]
              field_simp
              ring
        have hTx : T ≤ |x| := (not_mem_Icc_neg hx).le
        calc
          (|Real.sin (q * T / 2)| / q) *
              (Phi x ^ 2 * |Real.cos (x * c)|) ≤
              (T / 2) * (Phi x ^ 2 * 1) := by gcongr
          _ ≤ (|x| / 2) * (Phi x ^ 2 * 1) := by gcongr
          _ = (Phi x ^ 2 * |x|) / 2 := by ring
    _ = (∫ x, Phi x ^ 2 * |x|) / 2 := by
      rw [integral_div]

/-- A source-facing positivity criterion for one literal dyadic kernel row.
The hypotheses mention only its two explicit trigonometric phases and the
quantitative main-term/error inequality supplied by Fourier inversion. -/
theorem dyadicShiftKernel_PhiR_pos_of_main
    (P : Params) (hP : P.Valid) {T : ℝ} (hT : 0 ≤ T)
    (hwL : 8 * P.w ≤ P.L T) {n h : ℕ}
    (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hcos : 0 < Real.cos
      (3 * (Real.log (n + h) - Real.log n) * T / 2))
    (hmain :
      (∫ x, P.PhiR T x ^ 2 * |x|) / 2 <
        (Real.sin ((Real.log (n + h) - Real.log n) * T / 2) /
            (Real.log (n + h) - Real.log n)) *
          (2 * Real.pi * P.g T
            ((Real.log n + Real.log (n + h)) / 2))) :
    0 < dyadicShiftKernel (P.PhiR T) T n h := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmpos : (0 : ℝ) < n + h := by positivity
  have hnm : (n : ℝ) < n + h := by
    exact_mod_cast Nat.lt_add_of_pos_right hh
  have hlog : Real.log n < Real.log (n + h) :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hnpos)
      (Set.mem_Ioi.mpr hmpos) hnm
  let q : ℝ := Real.log (n + h) - Real.log n
  let c : ℝ := (Real.log n + Real.log (n + h)) / 2
  have hq : 0 < q := sub_pos.mpr hlog
  have htheta : Real.log n - Real.log (n + h) ≠ 0 :=
    sub_ne_zero.mpr hlog.ne
  have hPhi := Params.PhiR_continuous hP hwL
  have hPhi2 := Params.integrable_PhiR_sq hP hwL
  have hPhiAbs := Params.integrable_PhiR_sq_mul_abs hP hwL
  let I : ℝ := ∫ x in Set.Icc (-T) T,
    P.PhiR T x ^ 2 * Real.cos (x * c) *
      (Real.sin (q * (T - |x|) / 2) / q)
  have happrox := abs_truncated_sine_integral_sub_le hT hq
    (P.PhiR T) hPhi hPhi2 hPhiAbs (c := c)
  have hfourier :
      ∫ x, P.PhiR T x ^ 2 * Real.cos (x * c) =
        2 * Real.pi * P.g T c :=
    Params.integral_PhiR_sq_mul_cos hP hwL c
  have hIpos : 0 < I := by
    have hlower := (abs_lt.mp (lt_of_le_of_lt happrox hmain)).1
    rw [hfourier] at hlower
    dsimp [I, q, c] at hlower ⊢
    linarith
  have hkernel :
      dyadicShiftKernel (P.PhiR T) T n h =
        4 * Real.cos (3 * q * T / 2) * I := by
    unfold dyadicShiftKernel
    rw [Aminus_add_swap_eq htheta (P.PhiR T) hPhi]
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp [I, q, c]
    rw [show Real.log n - Real.log (n + h) =
        -(Real.log (n + h) - Real.log n) by ring]
    rw [show 3 * -(Real.log (n + h) - Real.log n) * T / 2 =
        -(3 * (Real.log (n + h) - Real.log n) * T / 2) by ring,
      Real.cos_neg]
    rw [show -(Real.log (n + h) - Real.log n) * (T - |x|) / 2 =
        -((Real.log (n + h) - Real.log n) * (T - |x|) / 2) by ring,
      Real.sin_neg]
    field_simp [sub_ne_zero.mpr hlog.ne']
  rw [hkernel]
  exact mul_pos (mul_pos (by norm_num) (by simpa [q] using hcos)) hIpos

/-- The logarithmic first-moment loss is eventually dominated by every
positive linear main term.  This is kept separate so the eventual choice of
the concrete phase parameter is transparent. -/
theorem eventually_log_loss_lt_linear
    {A K C : ℝ} (hA : 0 < A) (hK : 0 < K) :
    ∀ᶠ L in Filter.atTop,
      4 + 4 * Real.log (K * L) < A * (L - C) := by
  have hsmall := Asymptotics.isLittleO_iff.mp
    Real.isLittleO_log_id_atTop (show 0 < A / 16 by positivity)
  filter_upwards [hsmall,
    Filter.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_gt_atTop
      (16 * (1 + |Real.log K|) / A + 2 * |C| + 1)] with L hlog hL1 hLbig
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlogeq : Real.log (K * L) = Real.log K + Real.log L :=
    Real.log_mul hK.ne' hLpos.ne'
  have hlogbound : Real.log L ≤ A / 16 * L := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlogL, abs_of_pos hLpos] using hlog
  have hconst : 4 + 4 * Real.log K ≤ A * L / 4 := by
    have hlogK : Real.log K ≤ |Real.log K| := le_abs_self _
    have hthreshold : 16 * (1 + |Real.log K|) / A < L := by
      nlinarith [abs_nonneg C]
    have := (div_lt_iff₀ hA).mp hthreshold
    nlinarith
  have hleft : 4 + 4 * Real.log (K * L) ≤ A * L / 2 := by
    rw [hlogeq]
    nlinarith
  have hright : A * L / 2 < A * (L - C) := by
    have hCL : 2 * |C| < L := by
      have hnonneg : 0 ≤ 16 * (1 + |Real.log K|) / A := by positivity
      nlinarith
    have hC : C < L / 2 := lt_of_le_of_lt (le_abs_self C) (by linarith)
    nlinarith
  exact hleft.trans_lt hright

/-! ### A concrete two-row source witness -/

/-- The small logarithmic step used to make the two row frequencies have
the exact rational relation `3 : 2`. -/
noncomputable def concreteStepLog : ℝ := Real.log ((101 : ℝ) / 100)

theorem concreteStepLog_pos : 0 < concreteStepLog := by
  apply Real.log_pos
  norm_num [concreteStepLog]

def concreteZeroRow : ℕ := 201000000
def concretePositiveRow : ℕ := 303010000
def concreteRowShift : ℕ := 6090501
def concreteDyadicBase : ℕ := 200000000

/-- The height family makes the first row's midpoint cosine vanish while
the second row has phases `pi/3` and `pi/9`, modulo full periods. -/
noncomputable def concretePhaseHeight (k : ℕ) : ℝ :=
  ((18 * k + 1 : ℕ) : ℝ) * Real.pi / (9 * concreteStepLog)

theorem concrete_rows_in_same_dyadic_block :
    concreteZeroRow ∈ Finset.Ioc concreteDyadicBase (2 * concreteDyadicBase) ∧
    concreteZeroRow + concreteRowShift ∈
      Finset.Ioc concreteDyadicBase (2 * concreteDyadicBase) ∧
    concretePositiveRow ∈ Finset.Ioc concreteDyadicBase (2 * concreteDyadicBase) ∧
    concretePositiveRow + concreteRowShift ∈
      Finset.Ioc concreteDyadicBase (2 * concreteDyadicBase) := by
  norm_num [concreteZeroRow, concretePositiveRow, concreteRowShift,
    concreteDyadicBase, Finset.mem_Ioc]

theorem concrete_zero_row_log_step :
    Real.log (concreteZeroRow + concreteRowShift) -
        Real.log concreteZeroRow = 3 * concreteStepLog := by
  rw [← Real.log_div (by norm_num [concreteZeroRow, concreteRowShift])
    (by norm_num [concreteZeroRow])]
  have hratio :
      ((concreteZeroRow : ℝ) + concreteRowShift) /
          concreteZeroRow = ((101 : ℝ) / 100) ^ 3 := by
    norm_num [concreteZeroRow, concreteRowShift]
  rw [hratio, Real.log_pow]
  norm_num [concreteStepLog]

theorem concrete_positive_row_log_step :
    Real.log (concretePositiveRow + concreteRowShift) -
        Real.log concretePositiveRow = 2 * concreteStepLog := by
  rw [← Real.log_div (by norm_num [concretePositiveRow, concreteRowShift])
    (by norm_num [concretePositiveRow])]
  have hratio :
      ((concretePositiveRow : ℝ) + concreteRowShift) /
          concretePositiveRow = ((101 : ℝ) / 100) ^ 2 := by
    norm_num [concretePositiveRow, concreteRowShift]
  rw [hratio, Real.log_pow]
  norm_num [concreteStepLog]

theorem concretePhaseHeight_tendsto_atTop :
    Filter.Tendsto concretePhaseHeight Filter.atTop Filter.atTop := by
  have hlinear : Filter.Tendsto
      (fun k : ℕ => (18 : ℝ) * k + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hscale : 0 < Real.pi / (9 * concreteStepLog) := by
    exact div_pos Real.pi_pos (mul_pos (by norm_num) concreteStepLog_pos)
  have hmul := hlinear.atTop_mul_const hscale
  convert hmul using 1
  funext k
  simp only [concretePhaseHeight, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  ring

theorem concretePhaseHeight_pos (k : ℕ) : 0 < concretePhaseHeight k := by
  unfold concretePhaseHeight
  exact div_pos (mul_pos (by positivity) Real.pi_pos)
    (mul_pos (by norm_num) concreteStepLog_pos)

theorem concrete_zero_row_midpoint_cos (k : ℕ) :
    Real.cos
      (3 * (Real.log concreteZeroRow -
        Real.log (concreteZeroRow + concreteRowShift)) *
          concretePhaseHeight k / 2) = 0 := by
  rw [show Real.log concreteZeroRow -
      Real.log (concreteZeroRow + concreteRowShift) =
        -(3 * concreteStepLog) by
    rw [← concrete_zero_row_log_step]
    ring]
  rw [show 3 * -(3 * concreteStepLog) * concretePhaseHeight k / 2 =
      -(Real.pi / 2 + ((9 * k : ℕ) : ℝ) * Real.pi) by
    unfold concretePhaseHeight
    field_simp [concreteStepLog_pos.ne']
    push_cast
    ring]
  rw [Real.cos_neg]
  have hperiod := Real.cos_add_nat_mul_pi (Real.pi / 2) (9 * k)
  rw [Real.cos_pi_div_two, mul_zero] at hperiod
  exact hperiod

theorem concrete_positive_row_midpoint_cos (k : ℕ) :
    Real.cos
      (3 * (Real.log (concretePositiveRow + concreteRowShift) -
        Real.log concretePositiveRow) * concretePhaseHeight k / 2) = 1 / 2 := by
  rw [concrete_positive_row_log_step]
  rw [show 3 * (2 * concreteStepLog) * concretePhaseHeight k / 2 =
      Real.pi / 3 + ((6 * k : ℕ) : ℝ) * Real.pi by
    unfold concretePhaseHeight
    field_simp [concreteStepLog_pos.ne']
    push_cast
    ring]
  have hperiod := Real.cos_add_nat_mul_pi (Real.pi / 3) (6 * k)
  norm_num [Real.cos_pi_div_three] at hperiod ⊢
  exact hperiod

theorem concrete_positive_row_sine_phase (k : ℕ) :
    Real.sin
      ((Real.log (concretePositiveRow + concreteRowShift) -
        Real.log concretePositiveRow) * concretePhaseHeight k / 2) =
      Real.sin (Real.pi / 9) := by
  rw [concrete_positive_row_log_step]
  rw [show (2 * concreteStepLog) * concretePhaseHeight k / 2 =
      Real.pi / 9 + (k : ℝ) * (2 * Real.pi) by
    unfold concretePhaseHeight
    field_simp [concreteStepLog_pos.ne']
    push_cast
    ring]
  exact Real.sin_add_nat_mul_two_pi (Real.pi / 9) k

theorem sin_pi_div_nine_pos : 0 < Real.sin (Real.pi / 9) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

/-- A concrete source parameter choice.  It is the pinned Zeta23 smooth
transition, with the paper's endpoint values `lam = w = 1`. -/
noncomputable def concreteSourceParams : Params :=
  ⟨Taper.smoothstep, 1, 1⟩

theorem concreteSourceParams_valid : concreteSourceParams.Valid := by
  exact ⟨Taper.taperProfile_smoothstep, by norm_num [concreteSourceParams],
    by norm_num [concreteSourceParams], by norm_num [concreteSourceParams]⟩

private noncomputable def concretePositiveCenter : ℝ :=
  (Real.log concretePositiveRow +
    Real.log (concretePositiveRow + concreteRowShift)) / 2

private noncomputable def concreteMainSlope : ℝ :=
  Real.sin (Real.pi / 9) * Real.pi / concreteStepLog

private noncomputable def concreteMomentScale : ℝ :=
  (concreteSourceParams).crho / 4

private theorem concreteMainSlope_pos : 0 < concreteMainSlope := by
  exact div_pos (mul_pos sin_pi_div_nine_pos Real.pi_pos) concreteStepLog_pos

private theorem concreteMomentScale_pos : 0 < concreteMomentScale := by
  have hc : 4 ≤ (concreteSourceParams).crho := by
    exact Taper.four_le_cRho Taper.taperProfile_smoothstep
  unfold concreteMomentScale
  positivity

private theorem concrete_L_tendsto_atTop : Filter.Tendsto
    (fun k => (concreteSourceParams).L (concretePhaseHeight k))
    Filter.atTop Filter.atTop := by
  have hdiv := concretePhaseHeight_tendsto_atTop.atTop_div_const
    (by positivity : 0 < 2 * Real.pi)
  have hl := Real.tendsto_log_atTop.comp hdiv
  simpa [concreteSourceParams, Params.L, Zeta23.l, Function.comp_def] using hl

/-- For all sufficiently large members of the explicit phase family, the
pinned source window is admissible and the second literal kernel row is
strictly positive.  The proof uses the exact Fourier main term, Zeta23's
first-moment estimate, and `log L = o(L)`. -/
theorem eventually_concrete_positive_row :
    ∀ᶠ k in Filter.atTop,
      8 * concreteSourceParams.w ≤
          (concreteSourceParams).L (concretePhaseHeight k) ∧
      0 < dyadicShiftKernel
        ((concreteSourceParams).PhiR (concretePhaseHeight k))
        (concretePhaseHeight k) concretePositiveRow concreteRowShift := by
  let C : ℝ := 2 + |concretePositiveCenter|
  have hloss := concrete_L_tendsto_atTop.eventually
    (eventually_log_loss_lt_linear concreteMainSlope_pos
      concreteMomentScale_pos (C := C))
  have hwL := concrete_L_tendsto_atTop.eventually_ge_atTop
    (8 * concreteSourceParams.w)
  have hLC := concrete_L_tendsto_atTop.eventually_ge_atTop C
  filter_upwards [hloss, hwL, hLC] with k hloss hwL hLC
  refine ⟨hwL, ?_⟩
  apply dyadicShiftKernel_PhiR_pos_of_main concreteSourceParams
    concreteSourceParams_valid (concretePhaseHeight_pos k).le hwL
    (by norm_num [concretePositiveRow]) (by norm_num [concreteRowShift])
  · rw [concrete_positive_row_midpoint_cos]
    norm_num
  · have hmom := Params.integral_PhiR_sq_mul_abs_le
      concreteSourceParams_valid hwL
    have hmoment :
        (∫ x, (concreteSourceParams).PhiR (concretePhaseHeight k) x ^ 2 * |x|) / 2 ≤
          4 + 4 * Real.log
            (concreteMomentScale *
              concreteSourceParams.L (concretePhaseHeight k)) := by
      calc
        (∫ x, concreteSourceParams.PhiR (concretePhaseHeight k) x ^ 2 * |x|) / 2 ≤
            (8 + 8 * Real.log
              ((concreteSourceParams).crho *
                (concreteSourceParams).L (concretePhaseHeight k) /
                  (4 * concreteSourceParams.w))) / 2 :=
          div_le_div_of_nonneg_right hmom (by norm_num)
        _ = 4 + 4 * Real.log
            (concreteMomentScale *
              (concreteSourceParams).L (concretePhaseHeight k)) := by
          simp [concreteMomentScale, concreteSourceParams]
          ring_nf
    have hg := Params.g_ge concreteSourceParams_valid hwL concretePositiveCenter
    have hplateau :
        (concreteSourceParams).L (concretePhaseHeight k) -
            2 * concreteSourceParams.w - |concretePositiveCenter| ≥ 0 := by
      dsimp [C] at hLC
      simp only [concreteSourceParams] at hLC ⊢
      linarith
    rw [max_eq_left hplateau] at hg
    have hcoeff :
        (Real.sin
            ((Real.log (concretePositiveRow + concreteRowShift) -
              Real.log concretePositiveRow) * concretePhaseHeight k / 2) /
            (Real.log (concretePositiveRow + concreteRowShift) -
              Real.log concretePositiveRow)) * (2 * Real.pi) =
          concreteMainSlope := by
      rw [concrete_positive_row_sine_phase,
        concrete_positive_row_log_step]
      unfold concreteMainSlope
      field_simp [concreteStepLog_pos.ne']
    calc
      (∫ x, (concreteSourceParams).PhiR (concretePhaseHeight k) x ^ 2 * |x|) / 2 ≤
          4 + 4 * Real.log
            (concreteMomentScale *
              (concreteSourceParams).L (concretePhaseHeight k)) := hmoment
      _ < concreteMainSlope *
          ((concreteSourceParams).L (concretePhaseHeight k) - C) := hloss
      _ ≤ (Real.sin
            ((Real.log (concretePositiveRow + concreteRowShift) -
              Real.log concretePositiveRow) * concretePhaseHeight k / 2) /
            (Real.log (concretePositiveRow + concreteRowShift) -
              Real.log concretePositiveRow)) *
          (2 * Real.pi * (concreteSourceParams).g (concretePhaseHeight k)
            ((Real.log concretePositiveRow +
              Real.log (concretePositiveRow + concreteRowShift)) / 2)) := by
        rw [show ((Real.log concretePositiveRow +
              Real.log (concretePositiveRow + concreteRowShift)) / 2) =
            concretePositiveCenter by rfl]
        rw [← mul_assoc, hcoeff]
        apply mul_le_mul_of_nonneg_left _ concreteMainSlope_pos.le
        dsimp [C]
        simp only [concreteSourceParams] at hg ⊢
        linarith

/-- Source-specific zero-row criterion for the actual Zeta23 window. -/
theorem dyadicShiftKernel_PhiR_eq_zero_of_midpoint_cos_eq_zero
    (P : Params) (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) {n h : ℕ}
    (hθ : Real.log n - Real.log (n + h) ≠ 0)
    (hcos : Real.cos
      (3 * (Real.log n - Real.log (n + h)) * T / 2) = 0) :
    dyadicShiftKernel (P.PhiR T) T n h = 0 := by
  unfold dyadicShiftKernel
  rw [Aminus_add_swap_eq hθ (P.PhiR T) (Params.PhiR_continuous hP hwL)]
  simp [hcos]

/-- A completely explicit height at which the `(n,h) = (1,1)` row has
vanishing midpoint cosine.  The large integer is used only to put the
concrete Zeta23 window safely inside its `8w ≤ L` range. -/
noncomputable def concreteMidpointZeroHeight : ℝ :=
  200001 * Real.pi / (3 * Real.log 2)

private theorem concreteMidpointZeroHeight_window :
    8 * concreteSourceParams.w ≤
      concreteSourceParams.L concreteMidpointZeroHeight := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hexp1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hexp8 : Real.exp 8 < (6561 : ℝ) := by
    calc
      Real.exp 8 = Real.exp 1 ^ 8 := by
        rw [show (8 : ℝ) = (8 : ℕ) * 1 by norm_num,
          Real.exp_nat_mul]
      _ < 3 ^ 8 := pow_lt_pow_left₀ hexp1 (Real.exp_pos 1).le
        (n := 8) (by norm_num)
      _ = 6561 := by norm_num
  have hratio : (6561 : ℝ) ≤ 200001 / (6 * Real.log 2) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hlog2)]
    nlinarith
  have hquot : concreteMidpointZeroHeight / (2 * Real.pi) =
      200001 / (6 * Real.log 2) := by
    unfold concreteMidpointZeroHeight
    field_simp [Real.pi_ne_zero, hlog2.ne']
    ring
  have hpos : 0 < concreteMidpointZeroHeight / (2 * Real.pi) := by
    rw [hquot]
    positivity
  have hlog : (8 : ℝ) ≤
      Real.log (concreteMidpointZeroHeight / (2 * Real.pi)) := by
    rw [Real.le_log_iff_exp_le hpos]
    rw [hquot]
    exact hexp8.le.trans hratio
  simpa [concreteSourceParams, Params.L, l] using hlog

/-- The literal pinned-source kernel has an actual admissible zero row: no
arbitrary test function and no conditional row-variation witness occurs in
this statement. -/
theorem concrete_dyadicShiftKernel_row_zero :
    dyadicShiftKernel
      (concreteSourceParams.PhiR concreteMidpointZeroHeight)
      concreteMidpointZeroHeight 1 1 = 0 := by
  apply dyadicShiftKernel_PhiR_eq_zero_of_midpoint_cos_eq_zero
    concreteSourceParams concreteSourceParams_valid
    concreteMidpointZeroHeight_window
  · simp only [Nat.cast_one, Real.log_one, zero_sub]
    exact neg_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  · have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
      (Real.log_pos (by norm_num)).ne'
    norm_num only [Nat.cast_one, Real.log_one, zero_sub]
    rw [show 3 * -Real.log 2 * concreteMidpointZeroHeight / 2 =
        -(Real.pi / 2 + (100000 : ℝ) * Real.pi) by
      unfold concreteMidpointZeroHeight
      field_simp [hlog2]
      ring_nf]
    rw [Real.cos_neg]
    have hperiod := Real.cos_add_nat_mul_pi (Real.pi / 2) 100000
    norm_num [Real.cos_pi_div_two] at hperiod
    exact hperiod

end

end PrimeShell
