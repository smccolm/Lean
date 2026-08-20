import RiemannZeta.GuthMaynard.HughesYoungNearDFI
import RiemannZeta.GuthMaynard.HughesYoungEquation65

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

set_option maxHeartbeats 800000

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young equation (65) on the complementary shift range
-/

/-- A scale-free lower bound for logarithmic separation. -/
theorem abs_sub_div_max_le_abs_log_div
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |x - y| / max x y ≤ |Real.log (y / x)| := by
  rcases le_total x y with hxy | hyx
  · rw [max_eq_right hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hratio : 1 ≤ y / x := (le_div_iff₀ hx).2 (by simpa using hxy)
    rw [abs_of_nonneg (Real.log_nonneg hratio)]
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
    rw [inv_div] at hlog
    calc
      -(x - y) / y = 1 - x / y := by field_simp; linarith
      _ ≤ Real.log (y / x) := hlog
  · rw [max_eq_left hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hratio : y / x ≤ 1 := (div_le_one hx).2 hyx
    have hratioPos : 0 < y / x := div_pos hy hx
    rw [abs_of_nonpos (Real.log_nonpos hratioPos.le hratio)]
    rw [← Real.log_inv]
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
    rw [inv_div] at hlog
    calc
      (x - y) / x = 1 - y / x := by field_simp
      _ ≤ Real.log (x / y) := hlog
      _ = Real.log (y / x)⁻¹ := by rw [inv_div]

/-- On a positive dyadic `y` box, either of Hughes--Young's two far-range
conditions forces Fourier frequency at least `P/(5T)`. -/
theorem hughesYoung_far_frequency_of_shift_or_height
    {T P Y x y : ℝ} {r : ℤ}
    (hT : 0 < T) (hP : 0 < P) (hPT : P ≤ T) (hY : 0 < Y)
    (hx : 0 < x) (hy : 0 < y) (hyUpper : y ≤ 2 * Y)
    (hshift : x - y = (r : ℝ))
    (hfar : Y / 2 < |(r : ℝ)| ∨ P < T * (|(r : ℝ)| / Y)) :
    P / (5 * T) ≤ |Real.log (y / x)| := by
  have hbase := abs_sub_div_max_le_abs_log_div hx hy
  have habs : |x - y| = |(r : ℝ)| := by rw [hshift]
  rw [habs] at hbase
  apply le_trans ?_ hbase
  by_cases hlarge : Y / 2 < |(r : ℝ)|
  · have hsmall : P / (5 * T) ≤ (1 : ℝ) / 5 := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hT)
        (by norm_num : (0 : ℝ) < 5)]
      nlinarith
    refine hsmall.trans ?_
    by_cases hr : 0 ≤ r
    · have hrR : 0 ≤ (r : ℝ) := by exact_mod_cast hr
      have habsr : |(r : ℝ)| = (r : ℝ) := abs_of_nonneg hrR
      have hyx : y ≤ x := by linarith [hshift]
      rw [max_eq_left hyx, habsr]
      have hyr : y < 4 * (r : ℝ) := by
        rw [habsr] at hlarge
        nlinarith
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) hx]
      nlinarith [hshift]
    · have hrneg : r < 0 := lt_of_not_ge hr
      have hrR : (r : ℝ) < 0 := by exact_mod_cast hrneg
      have habsr : |(r : ℝ)| = -(r : ℝ) := abs_of_neg hrR
      have hxy : x ≤ y := by linarith [hshift]
      rw [max_eq_right hxy, habsr]
      rw [habsr] at hlarge
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) hy]
      nlinarith
  · have hfreq : P < T * (|(r : ℝ)| / Y) := hfar.resolve_left hlarge
    by_cases hr : 0 ≤ r
    · have hrR : 0 ≤ (r : ℝ) := by exact_mod_cast hr
      have habsr : |(r : ℝ)| = (r : ℝ) := abs_of_nonneg hrR
      have hyx : y ≤ x := by linarith [hshift]
      rw [max_eq_left hyx, habsr]
      rw [habsr] at hlarge hfreq
      have hrUpper : (r : ℝ) ≤ Y / 2 := le_of_not_gt hlarge
      have hxUpper : x ≤ 3 * Y := by nlinarith [hshift]
      have hfreq' : P * Y < T * (r : ℝ) := by
        have heq : T * ((r : ℝ) / Y) = (T * (r : ℝ)) / Y := by ring
        rw [heq] at hfreq
        exact (lt_div_iff₀ hY).mp hfreq
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hT) hx]
      have hmul := mul_le_mul_of_nonneg_left hxUpper hP.le
      nlinarith
    · have hrneg : r < 0 := lt_of_not_ge hr
      have hrR : (r : ℝ) < 0 := by exact_mod_cast hrneg
      have habsr : |(r : ℝ)| = -(r : ℝ) := abs_of_neg hrR
      have hxy : x ≤ y := by linarith [hshift]
      rw [max_eq_right hxy, habsr]
      rw [habsr] at hfreq
      have hfreq' : P * Y < T * (-(r : ℝ)) := by
        have heq : T * (-(r : ℝ) / Y) = (T * (-(r : ℝ))) / Y := by ring
        rw [heq] at hfreq
        exact (lt_div_iff₀ hY).mp hfreq
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hT) hy]
      have hmul := mul_le_mul_of_nonneg_left hyUpper hP.le
      nlinarith

/-- A nonzero reduced static summand lies in its literal dyadic box. -/
theorem hughesYoungReducedLocalizedStaticWeight_mem_dyadicBox
    {T c u X Y : ℝ} {h k : ℕ} {x y : ℝ}
    (hX : 0 < X) (hY : 0 < Y)
    (hne : hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y ≠ 0) :
    x ∈ Set.Icc X (2 * X) ∧ y ∈ Set.Icc Y (2 * Y) := by
  have hcutX : hughesYoungDyadicCutoffAt X x ≠ 0 := by
    intro hz
    apply hne
    unfold hughesYoungReducedLocalizedStaticWeight hughesYoungLocalizedLogKernel
    rw [hz]
    norm_num
  have hcutY : hughesYoungDyadicCutoffAt Y y ≠ 0 := by
    intro hz
    apply hne
    unfold hughesYoungReducedLocalizedStaticWeight hughesYoungLocalizedLogKernel
    rw [hz]
    norm_num
  exact ⟨support_hughesYoungDyadicCutoffAt_subset hX hcutX,
    support_hughesYoungDyadicCutoffAt_subset hY hcutY⟩

/-- The height-free reduced source weight retains the exact physical-scale
decay of both Mellin factors.  This is the pointwise arithmetic majorant
used when equation (65) is summed over the complementary shifts. -/
theorem norm_hughesYoungReducedLocalizedStaticWeight_le_scale
    {T c u X Y x y : ℝ} {h k : ℕ}
    (hX : 0 < X) (hY : 0 < Y) (hx : X ≤ x) (hy : Y ≤ y)
    (hh : 0 < h) (hk : 0 < k) (hc : 0 < c) :
    ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y‖ ≤
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
          ((1 / 2 : ℝ) + c) *
        (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
          ((1 / 2 : ℝ) + c) := by
  let s : ℂ := (1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)
  have hx0 : 0 < x := hX.trans_le hx
  have hy0 : 0 < y := hY.trans_le hy
  have ha0 : (0 : ℝ) < hughesYoungReducedLeft h k := by
    exact_mod_cast hughesYoungReducedLeft_pos hh
  have hb0 : (0 : ℝ) < hughesYoungReducedRight h k := by
    exact_mod_cast hughesYoungReducedRight_pos hh hk
  have hcutX := abs_hughesYoungDyadicCutoffAt_le_one hX hx0.le
  have hcutY := abs_hughesYoungDyadicCutoffAt_le_one hY hy0.le
  have hlogX :=
    abs_pow_mul_norm_iteratedDeriv_hughesYoungLogPower_div s 0 hx0 ha0
  have hlogY :=
    abs_pow_mul_norm_iteratedDeriv_hughesYoungLogPower_div s 0 hy0 hb0
  have hsre : s.re = (1 / 2 : ℝ) + c := by simp [s]
  have hratioX : ((hughesYoungReducedLeft h k : ℕ) / x : ℝ) ^ s.re ≤
      (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^ ((1 / 2 : ℝ) + c) := by
    rw [hsre]
    exact rpow_div_le_rpow_div_of_le ha0 hX hx (by positivity)
  have hratioY : ((hughesYoungReducedRight h k : ℕ) / y : ℝ) ^ s.re ≤
      (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^ ((1 / 2 : ℝ) + c) := by
    rw [hsre]
    exact rpow_div_le_rpow_div_of_le hb0 hY hy (by positivity)
  have hlogX' : ‖hughesYoungLogPower s
      (x / hughesYoungReducedLeft h k)‖ =
      ((hughesYoungReducedLeft h k : ℕ) / x : ℝ) ^ s.re := by
    simpa using hlogX
  have hlogY' : ‖hughesYoungLogPower s
      (y / hughesYoungReducedRight h k)‖ =
      ((hughesYoungReducedRight h k : ℕ) / y : ℝ) ^ s.re := by
    simpa using hlogY
  unfold hughesYoungReducedLocalizedStaticWeight
    hughesYoungLocalizedLogKernel
  change ‖hughesYoungLocalizedStaticScalar T h k *
      ((hughesYoungDyadicCutoffAt X x : ℂ) *
        (hughesYoungDyadicCutoffAt Y y : ℂ) *
        hughesYoungLogPower s (x / hughesYoungReducedLeft h k) *
        hughesYoungLogPower s (y / hughesYoungReducedRight h k))‖ ≤ _
  simp only [norm_mul, norm_real, Real.norm_eq_abs, hlogX', hlogY']
  have hkernel :
      |hughesYoungDyadicCutoffAt X x| *
          |hughesYoungDyadicCutoffAt Y y| *
          ((hughesYoungReducedLeft h k : ℕ) / x : ℝ) ^ s.re *
          ((hughesYoungReducedRight h k : ℕ) / y : ℝ) ^ s.re ≤
        (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
            ((1 / 2 : ℝ) + c) *
          (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
            ((1 / 2 : ℝ) + c) := by
    calc
      |hughesYoungDyadicCutoffAt X x| *
            |hughesYoungDyadicCutoffAt Y y| *
            ((hughesYoungReducedLeft h k : ℕ) / x : ℝ) ^ s.re *
            ((hughesYoungReducedRight h k : ℕ) / y : ℝ) ^ s.re ≤
          1 * 1 * (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
              ((1 / 2 : ℝ) + c) *
            (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
              ((1 / 2 : ℝ) + c) := by
        gcongr
      _ = _ := by ring
  calc
    ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (|hughesYoungDyadicCutoffAt X x| * |hughesYoungDyadicCutoffAt Y y| *
            ((hughesYoungReducedLeft h k : ℕ) / x : ℝ) ^ s.re *
            ((hughesYoungReducedRight h k : ℕ) / y : ℝ) ^ s.re) ≤
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
              ((1 / 2 : ℝ) + c) *
            (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
              ((1 / 2 : ℝ) + c)) :=
      mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
    _ = _ := by ring

/-- Membership in the literal far-shift set, together with a nonzero dyadic
summand, reduces exactly to one of the two analytic far conditions. -/
theorem hughesYoung_farShift_analytic_disjunction
    {T P X Y : ℝ} {a b M N : ℕ} {r : ℤ}
    {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hxUpper : x ≤ 2 * X) (hyUpper : y ≤ 2 * Y)
    (hshift : x - y = (r : ℝ))
    (hr : r ∈ hughesYoungFarShifts T P X Y a b M N) :
    Y / 2 < |(r : ℝ)| ∨ P < T * (|(r : ℝ)| / Y) := by
  obtain ⟨hrInterval, hr0, hrNotNear⟩ := mem_hughesYoungFarShifts_iff.mp hr
  have hrPos : 0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X := by
    intro hrNonneg
    rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast hrNonneg)]
    have : (r : ℝ) < x := by linarith
    exact this.le.trans hxUpper
  have hrNeg : r < 0 → (r.natAbs : ℝ) ≤ 2 * Y := by
    intro hrNegative
    have hrReal : (r : ℝ) < 0 := by exact_mod_cast hrNegative
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg hrReal]
    have : -(r : ℝ) < y := by linarith
    exact this.le.trans hyUpper
  by_cases hrY : |(r : ℝ)| ≤ Y / 2
  · right
    have hnot : ¬ T * (|(r : ℝ)| / Y) ≤ P := by
      intro hrP
      apply hrNotNear
      exact mem_hughesYoungNearShifts_iff.mpr
        ⟨hrInterval, hr0, hrY, hrP, hrPos, hrNeg⟩
    exact lt_of_not_ge hnot
  · left
    exact lt_of_not_ge hrY

/-- Every nonzero summand in the literal far family has Fourier frequency
at least `P/(5T)`. -/
theorem hughesYoung_farShift_frequency
    {T P X Y c u : ℝ} {h k a b M N : ℕ} {r : ℤ}
    {x y : ℝ}
    (hT : 0 < T) (hP : 0 < P) (hPT : P ≤ T)
    (hX : 0 < X) (hY : 0 < Y) (hx : 0 < x) (hy : 0 < y)
    (hshift : x - y = (r : ℝ))
    (hr : r ∈ hughesYoungFarShifts T P X Y a b M N)
    (hne : hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y ≠ 0) :
    P / (5 * T) ≤ |Real.log (y / x)| := by
  obtain ⟨hxBox, hyBox⟩ :=
    hughesYoungReducedLocalizedStaticWeight_mem_dyadicBox hX hY hne
  apply hughesYoung_far_frequency_of_shift_or_height hT hP hPT hY
    hx hy hyBox.2 hshift
  exact hughesYoung_farShift_analytic_disjunction hx hy
    hxBox.2 hyBox.2 hshift hr

/-- The explicit right side of Hughes--Young equation (65). -/
noncomputable def hughesYoungEquation65Bound
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ) (T c u : ℝ) : ℝ :=
  (15 * T / 4) *
    (c⁻¹ * Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 +
        4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
      (25 + 8 * u ^ 2) ^ 4 *
      hughesYoungHeightInputDerivativeConstant Cw j *
      (((T / 16)⁻¹ * (1 + |u|)) ^ j))

/-- Equation (65) applied to one literal far-shift summand.  The inequality
keeps the exact static arithmetic/Mellin amplitude and exposes the complete
`(P/(5T))^j` Fourier saving. -/
theorem exists_farShift_reducedCleaned_equation65 :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N : ℕ}
        {r : ℤ} {x y : ℝ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 0 < X → 0 < Y →
      0 < x → 0 < y → x - y = (r : ℝ) →
      r ∈ hughesYoungFarShifts T P X Y a b M N →
      (P / (5 * T)) ^ j *
          ‖hughesYoungReducedCleanedShiftWeight T c u X Y h k r x y‖ ≤
        (1 / T) *
          ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y‖ *
          hughesYoungEquation65Bound Cγ Cw j T c u := by
  obtain ⟨Cγ, hCγ, Cw, hCw, h65⟩ := hughesYoung_equation65
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N r x y hT hc hc1 hu hP hPT hX hY
    hx hy hshift hr
  have hT0 : 0 < T := by linarith
  by_cases hstatic :
      hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y = 0
  · unfold hughesYoungReducedCleanedShiftWeight
    rw [hstatic]
    norm_num
  · have hfreq := hughesYoung_farShift_frequency hT0 hP hPT hX hY hx hy
      hshift hr hstatic
    have hq0 : 0 ≤ P / (5 * T) := (div_pos hP (mul_pos (by norm_num) hT0)).le
    have hpow : (P / (5 * T)) ^ j ≤ |Real.log (y / x)| ^ j :=
      pow_le_pow_left₀ hq0 hfreq j
    have hraw := h65 j T c u (Real.log (y / x)) hT hc hc1 hu
    have htrans : (P / (5 * T)) ^ j *
        ‖hughesYoungHeightTransform T c u (Real.log (y / x))‖ ≤
          hughesYoungEquation65Bound Cγ Cw j T c u := by
      exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
        (by simpa only [hughesYoungEquation65Bound] using hraw)
    have hnormInv : ‖(1 / (T : ℂ))‖ = 1 / T := by
      rw [norm_div, norm_one, norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    unfold hughesYoungReducedCleanedShiftWeight
    rw [← log_div_eq_neg_log_one_add_shift_div hx hy r hshift]
    rw [norm_mul, norm_mul, hnormInv]
    calc
      (P / (5 * T)) ^ j *
          ((1 / T) *
            ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y‖ *
            ‖hughesYoungHeightTransform T c u (Real.log (y / x))‖) =
        ((1 / T) *
          ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y‖) *
          ((P / (5 * T)) ^ j *
            ‖hughesYoungHeightTransform T c u (Real.log (y / x))‖) := by ring
      _ ≤ ((1 / T) *
          ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y‖) *
          hughesYoungEquation65Bound Cγ Cw j T c u := by
        exact mul_le_mul_of_nonneg_left htrans
          (mul_nonneg (by positivity) (norm_nonneg _))
      _ = _ := by ring

/-- The positive static mass of one shifted-divisor sum after the height
Fourier transform has been removed.  This is the exact finite arithmetic
quantity left by equation (65), not an independently supplied majorant. -/
noncomputable def hughesYoungReducedStaticShiftMass
    (T c u X Y : ℝ) (h k a b M N : ℕ) (r : ℤ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
    if quadraticDivisorShift a b m n = r then
      ‖divisorWeight m‖ * ‖divisorWeight n‖ *
        ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k
          (a * m) (b * n)‖
    else 0

/-- The complete static mass over Hughes--Young's literal complementary
shift family. -/
noncomputable def hughesYoungFarStaticMass
    (T c u P X Y : ℝ) (h k a b M N : ℕ) : ℝ :=
  ∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
    hughesYoungReducedStaticShiftMass T c u X Y h k a b M N r

theorem hughesYoungReducedStaticShiftMass_nonneg
    (T c u X Y : ℝ) (h k a b M N : ℕ) (r : ℤ) :
    0 ≤ hughesYoungReducedStaticShiftMass T c u X Y h k a b M N r := by
  unfold hughesYoungReducedStaticShiftMass
  positivity

theorem hughesYoungFarStaticMass_nonneg
    (T c u P X Y : ℝ) (h k a b M N : ℕ) :
    0 ≤ hughesYoungFarStaticMass T c u P X Y h k a b M N := by
  unfold hughesYoungFarStaticMass
  exact Finset.sum_nonneg fun r _ =>
    hughesYoungReducedStaticShiftMass_nonneg T c u X Y h k a b M N r

/-- The far-shift mass is exactly the original finite divisor-pair mass with
the unique shift tested for membership in the complementary family.  In
particular, summing equation (65) over shifts introduces no cardinality loss. -/
theorem hughesYoungFarStaticMass_eq_pair_sum
    (T c u P X Y : ℝ) (h k a b M N : ℕ) :
    hughesYoungFarStaticMass T c u P X Y h k a b M N =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        if quadraticDivisorShift a b m n ∈
            hughesYoungFarShifts T P X Y a b M N then
          ‖divisorWeight m‖ * ‖divisorWeight n‖ *
            ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k
              (a * m) (b * n)‖
        else 0 := by
  classical
  unfold hughesYoungFarStaticMass hughesYoungReducedStaticShiftMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hs : quadraticDivisorShift a b m n ∈
      hughesYoungFarShifts T P X Y a b M N
  · simp only [hs, if_true]
    rw [Finset.sum_eq_single (quadraticDivisorShift a b m n)]
    · simp
    · intro r hr hrne
      simp [hrne.symm]
    · exact fun hnot => (hnot hs).elim
  · simp only [hs, if_false]
    apply Finset.sum_eq_zero
    intro r hr
    have hne : quadraticDivisorShift a b m n ≠ r := by
      intro heq
      apply hs
      simpa [heq] using hr
    simp [hne]

/-- Source-faithful arithmetic majorant for the entire complementary shift
family.  The shift sum has already been collapsed, so the right side contains
only the two divisor masses and the two physical Mellin scale ratios. -/
theorem hughesYoungFarStaticMass_le_divisor_masses
    {T c u P X Y : ℝ} {h k a b M N : ℕ}
    (hX : 0 < X) (hY : 0 < Y)
    (hh : 0 < h) (hk : 0 < k) (hc : 0 < c) :
    hughesYoungFarStaticMass T c u P X Y h k a b M N ≤
      (∑ m ∈ Finset.Icc 1 M, ‖divisorWeight m‖) *
        (∑ n ∈ Finset.Icc 1 N, ‖divisorWeight n‖) *
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
          ((1 / 2 : ℝ) + c) *
        (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
          ((1 / 2 : ℝ) + c) := by
  rw [hughesYoungFarStaticMass_eq_pair_sum]
  let K : ℝ := ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
        ((1 / 2 : ℝ) + c) *
      (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
        ((1 / 2 : ℝ) + c)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hterm : ∀ m ∈ Finset.Icc 1 M, ∀ n ∈ Finset.Icc 1 N,
      (if quadraticDivisorShift a b m n ∈
          hughesYoungFarShifts T P X Y a b M N then
        ‖divisorWeight m‖ * ‖divisorWeight n‖ *
          ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k
            (a * m) (b * n)‖
       else 0) ≤ ‖divisorWeight m‖ * ‖divisorWeight n‖ * K := by
    intro m _hm n _hn
    by_cases hs : quadraticDivisorShift a b m n ∈
        hughesYoungFarShifts T P X Y a b M N
    · simp only [hs, if_true]
      by_cases hw : hughesYoungReducedLocalizedStaticWeight T c u X Y h k
          (a * m) (b * n) = 0
      · rw [hw, norm_zero]
        simpa only [mul_zero] using
          mul_nonneg
            (mul_nonneg
              (show 0 ≤ ‖divisorWeight m‖ from norm_nonneg _)
              (show 0 ≤ ‖divisorWeight n‖ from norm_nonneg _)) hK
      · obtain ⟨hxm, hyn⟩ :=
          hughesYoungReducedLocalizedStaticWeight_mem_dyadicBox hX hY hw
        exact mul_le_mul_of_nonneg_left
          (norm_hughesYoungReducedLocalizedStaticWeight_le_scale
            hX hY hxm.1 hyn.1 hh hk hc)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    · simp only [hs, if_false]
      positivity
  calc
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        if quadraticDivisorShift a b m n ∈
            hughesYoungFarShifts T P X Y a b M N then
          ‖divisorWeight m‖ * ‖divisorWeight n‖ *
            ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k
              (a * m) (b * n)‖
        else 0) ≤
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        ‖divisorWeight m‖ * ‖divisorWeight n‖ * K := by
      exact Finset.sum_le_sum fun m hm =>
        Finset.sum_le_sum fun n hn => hterm m hm n hn
    _ = (∑ m ∈ Finset.Icc 1 M, ‖divisorWeight m‖) *
        (∑ n ∈ Finset.Icc 1 N, ‖divisorWeight n‖) * K := by
      simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    _ = _ := by
      dsimp only [K]
      ring

/-- Elementary divisor-mass consequence of the native divisor bound.  This
is the precise finite estimate used after collapsing the complementary shift
partition. -/
theorem exists_sum_norm_divisorWeight_le_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ,
      ∑ n ∈ Finset.Icc 1 L, ‖divisorWeight n‖ ≤
        C * (L : ℝ) ^ (1 + ε) := by
  obtain ⟨C, hC, hdiv⟩ := exists_norm_divisorWeight_le_rpow ε hε
  refine ⟨C, hC, ?_⟩
  intro L
  cases L with
  | zero =>
      have hExp : 0 < 1 + ε := by linarith
      simp [Real.zero_rpow hExp.ne']
  | succ K =>
      have hL : (0 : ℝ) < (K + 1 : ℕ) := by positivity
      have hpoint : ∀ n ∈ Finset.Icc 1 (K + 1),
          ‖divisorWeight n‖ ≤ C * ((K + 1 : ℕ) : ℝ) ^ ε := by
        intro n hn
        have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
        have hnle : n ≤ K + 1 := (Finset.mem_Icc.mp hn).2
        calc
          ‖divisorWeight n‖ ≤ C * (n : ℝ) ^ ε := hdiv n hnpos
          _ ≤ C * ((K + 1 : ℕ) : ℝ) ^ ε := by
            gcongr
      calc
        (∑ n ∈ Finset.Icc 1 (K + 1), ‖divisorWeight n‖) ≤
            ∑ _n ∈ Finset.Icc 1 (K + 1),
              C * ((K + 1 : ℕ) : ℝ) ^ ε :=
          Finset.sum_le_sum hpoint
        _ = ((K + 1 : ℕ) : ℝ) *
            (C * ((K + 1 : ℕ) : ℝ) ^ ε) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          push_cast
          ring
        _ = C * ((K + 1 : ℕ) : ℝ) ^ (1 + ε) := by
          have hpow : ((K + 1 : ℕ) : ℝ) ^ (1 + ε) =
              ((K + 1 : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ) ^ ε := by
            rw [Real.rpow_add hL, Real.rpow_one]
          rw [hpow]
          ring

/-- Polynomial form of the complete far-shift static mass.  The constant is
native and uniform in every Hughes--Young and finite-box parameter. -/
theorem exists_hughesYoungFarStaticMass_le_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T c u P X Y : ℝ} {h k a b M N : ℕ},
      0 < X → 0 < Y → 0 < h → 0 < k → 0 < c →
      hughesYoungFarStaticMass T c u P X Y h k a b M N ≤
        C * (M : ℝ) ^ (1 + ε) * (N : ℝ) ^ (1 + ε) *
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
            ((1 / 2 : ℝ) + c) *
          (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
            ((1 / 2 : ℝ) + c) := by
  obtain ⟨D, hD, hmass⟩ := exists_sum_norm_divisorWeight_le_rpow ε hε
  refine ⟨D ^ 2, sq_pos_of_pos hD, ?_⟩
  intro T c u P X Y h k a b M N hX hY hh hk hc
  have hbase := hughesYoungFarStaticMass_le_divisor_masses
    (T := T) (c := c) (u := u) (P := P) (X := X) (Y := Y)
    (h := h) (k := k) (a := a) (b := b) (M := M) (N := N)
    hX hY hh hk hc
  have hM := hmass M
  have hN := hmass N
  have hMN :
      (∑ m ∈ Finset.Icc 1 M, ‖divisorWeight m‖) *
          (∑ n ∈ Finset.Icc 1 N, ‖divisorWeight n‖) ≤
        (D * (M : ℝ) ^ (1 + ε)) *
          (D * (N : ℝ) ^ (1 + ε)) := by
    exact mul_le_mul hM hN (by positivity) (by positivity)
  let K : ℝ := ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
        ((1 / 2 : ℝ) + c) *
      (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
        ((1 / 2 : ℝ) + c)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  calc
    hughesYoungFarStaticMass T c u P X Y h k a b M N ≤
        (∑ m ∈ Finset.Icc 1 M, ‖divisorWeight m‖) *
          (∑ n ∈ Finset.Icc 1 N, ‖divisorWeight n‖) * K := by
      simpa only [K, mul_assoc] using hbase
    _ ≤ (D * (M : ℝ) ^ (1 + ε)) *
          (D * (N : ℝ) ^ (1 + ε)) * K :=
      mul_le_mul_of_nonneg_right hMN hK
    _ = _ := by
      dsimp only [K]
      ring

/-- Gaussian integrability with an arbitrary natural absolute-value moment. -/
theorem integrable_abs_pow_mul_exp_neg_mul_sq
    {b : ℝ} (hb : 0 < b) (j : ℕ) :
    Integrable (fun u : ℝ => |u| ^ j * Real.exp (-b * u ^ 2)) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  have hpos : IntegrableOn
      (fun u : ℝ => |u| ^ j * Real.exp (-b * u ^ 2)) (Set.Ioi 0) := by
    have hraw := integrableOn_rpow_mul_exp_neg_mul_sq hb
      (s := (j : ℝ)) (by
        have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
        linarith)
    apply hraw.congr_fun _ measurableSet_Ioi
    intro u hu
    dsimp only
    rw [Real.rpow_natCast, abs_of_pos (Set.mem_Ioi.mp hu)]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_sq, neg_preimage, neg_Iio, neg_zero]
    using hpos

/-- The polynomial Gaussian envelope occurring after `j` integrations by
parts in Hughes--Young (65) is integrable on the full ordinate line. -/
theorem integrable_exp_neg_84_mul_one_add_abs_pow (j : ℕ) :
    Integrable (fun u : ℝ => Real.exp (-84 * u ^ 2) * (1 + |u|) ^ j) := by
  have hterm : ∀ i ∈ Finset.range (j + 1), Integrable (fun u : ℝ =>
      (j.choose i : ℝ) *
        (1 ^ i * |u| ^ (j - i) * Real.exp (-84 * u ^ 2))) := by
    intro i _hi
    simpa only [one_pow, one_mul] using
      (integrable_abs_pow_mul_exp_neg_mul_sq
        (by norm_num : (0 : ℝ) < 84) (j - i)).const_mul (j.choose i : ℝ)
  have hsum : Integrable (fun u : ℝ =>
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) *
          (1 ^ i * |u| ^ (j - i) * Real.exp (-84 * u ^ 2))) :=
    integrable_finsetSum (Finset.range (j + 1)) hterm
  apply hsum.congr
  filter_upwards with u
  rw [add_pow]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- A positive, finite constant dominating every symmetric truncation of the
order-`j` Gaussian moment in equation (65). -/
theorem exists_intervalIntegral_exp_neg_84_mul_one_add_abs_pow_le (j : ℕ) :
    ∃ L : ℝ, 0 < L ∧ ∀ {H : ℝ}, 0 ≤ H →
      (∫ u in -H..H, Real.exp (-84 * u ^ 2) * (1 + |u|) ^ j) ≤ L := by
  let f : ℝ → ℝ := fun u => Real.exp (-84 * u ^ 2) * (1 + |u|) ^ j
  have hf : Integrable f := integrable_exp_neg_84_mul_one_add_abs_pow j
  let L : ℝ := (∫ u : ℝ, f u) + 1
  have hfullNonneg : 0 ≤ ∫ u : ℝ, f u := integral_nonneg fun u => by
    dsimp only [f]
    positivity
  have hL : 0 < L := by dsimp only [L]; linarith
  refine ⟨L, hL, ?_⟩
  intro H hH
  have horder : -H ≤ H := by linarith
  calc
    (∫ u in -H..H, Real.exp (-84 * u ^ 2) * (1 + |u|) ^ j) =
        ∫ u in -H..H, f u := by rfl
    _ ≤ ∫ u : ℝ, f u := by
      rw [intervalIntegral.integral_of_le horder]
      apply setIntegral_le_integral hf
      filter_upwards with u
      dsimp only [f]
      positivity
    _ ≤ L := by dsimp only [L]; linarith

/-- Uniform pointwise envelope for the explicit right side of equation (65).
When the contour is sufficiently small, its logarithmic Gamma loss costs at
most one additional factor of `T(1+|u|)`. -/
theorem hughesYoungEquation65Bound_le_gaussian
    {Cγ : ℝ} (hCγ : 0 < Cγ) {Cw : ℕ → ℝ}
    (hCw : ∀ i, 0 < Cw i) (j : ℕ)
    {T c u : ℝ} (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hsmall : 4 * Cγ * c ≤ 1) :
    hughesYoungEquation65Bound Cγ Cw j T c u ≤
      ((15 * T / 4) * c⁻¹ * Real.exp 100 * (6 * T) *
        33 ^ 4 *
        hughesYoungHeightInputDerivativeConstant Cw j *
        ((T / 16)⁻¹) ^ j) *
          (Real.exp (-84 * u ^ 2) * (1 + |u|) ^ (j + 9)) := by
  let B : ℝ := 4 * T + |u| + 2
  let a : ℝ := 4 * Cγ * c
  have hB1 : 1 ≤ B := by dsimp only [B]; linarith [abs_nonneg u]
  have hB0 : 0 < B := zero_lt_one.trans_le hB1
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have ha1 : a ≤ 1 := hsmall
  have hcpow : 100 * c ^ 2 ≤ 100 := by nlinarith
  have hBpow : Real.exp (a * Real.log B) ≤ B := by
    have hrpow : B ^ a ≤ B ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hB1 ha1
    rw [Real.rpow_def_of_pos hB0, Real.rpow_one] at hrpow
    simpa [mul_comm] using hrpow
  have hBupper : B ≤ 6 * T * (1 + |u|) := by
    have hTabs : |u| ≤ 6 * T * |u| := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (by linarith : 1 ≤ 6 * T) (abs_nonneg u)
    dsimp only [B]
    nlinarith
  have hExp : Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 + a * Real.log B) ≤
        Real.exp 100 * Real.exp (-84 * u ^ 2) *
          (6 * T * (1 + |u|)) := by
    rw [show 100 * c ^ 2 - 84 * u ^ 2 + a * Real.log B =
        100 * c ^ 2 + (-84 * u ^ 2) + a * Real.log B by ring,
      Real.exp_add, Real.exp_add]
    calc
      Real.exp (100 * c ^ 2) * Real.exp (-84 * u ^ 2) *
          Real.exp (a * Real.log B) ≤
        Real.exp 100 * Real.exp (-84 * u ^ 2) * B := by
          gcongr
      _ ≤ Real.exp 100 * Real.exp (-84 * u ^ 2) *
          (6 * T * (1 + |u|)) := by gcongr
  have hpolyBase : 25 + 8 * u ^ 2 ≤ 33 * (1 + |u|) ^ 2 := by
    rw [show u ^ 2 = |u| ^ 2 by exact (sq_abs u).symm]
    nlinarith [abs_nonneg u]
  have hpoly : (25 + 8 * u ^ 2) ^ 4 ≤
      33 ^ 4 * (1 + |u|) ^ 8 := by
    have hbaseNonneg : 0 ≤ 25 + 8 * u ^ 2 := by positivity
    have hp := pow_le_pow_left₀ hbaseNonneg hpolyBase 4
    rw [mul_pow, ← pow_mul] at hp
    norm_num at hp ⊢
    exact hp
  unfold hughesYoungEquation65Bound
  change (15 * T / 4) *
      (c⁻¹ * Real.exp
        (100 * c ^ 2 - 84 * u ^ 2 + a * Real.log B) *
        (25 + 8 * u ^ 2) ^ 4 *
        hughesYoungHeightInputDerivativeConstant Cw j *
        (((T / 16)⁻¹ * (1 + |u|)) ^ j)) ≤ _
  have hfront : 0 ≤ (15 * T / 4) * c⁻¹ := by positivity
  have hderiv : 0 ≤ hughesYoungHeightInputDerivativeConstant Cw j :=
    (hughesYoungHeightInputDerivativeConstant_pos hCw j).le
  calc
    (15 * T / 4) *
        (c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 + a * Real.log B) *
          (25 + 8 * u ^ 2) ^ 4 *
          hughesYoungHeightInputDerivativeConstant Cw j *
          (((T / 16)⁻¹ * (1 + |u|)) ^ j)) =
      ((15 * T / 4) * c⁻¹) *
        Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 + a * Real.log B) *
        (25 + 8 * u ^ 2) ^ 4 *
        hughesYoungHeightInputDerivativeConstant Cw j *
        (((T / 16)⁻¹ * (1 + |u|)) ^ j) := by ring
    _ ≤ ((15 * T / 4) * c⁻¹) *
        (Real.exp 100 * Real.exp (-84 * u ^ 2) *
          (6 * T * (1 + |u|))) *
        (33 ^ 4 * (1 + |u|) ^ 8) *
        hughesYoungHeightInputDerivativeConstant Cw j *
        (((T / 16)⁻¹ * (1 + |u|)) ^ j) := by
      gcongr
    _ = _ := by
      rw [mul_pow]
      ring

/-- Integrated form of the equation-(65) Gaussian envelope, uniform in the
finite Mellin height. -/
theorem exists_intervalIntegral_hughesYoungEquation65Bound_le
    {Cγ : ℝ} (hCγ : 0 < Cγ) {Cw : ℕ → ℝ}
    (hCw : ∀ i, 0 < Cw i) (j : ℕ) :
    ∃ L : ℝ, 0 < L ∧ ∀ {T c H : ℝ},
      1 ≤ T → 0 < c → c ≤ 1 → 4 * Cγ * c ≤ 1 → 0 ≤ H →
      (∫ u in -H..H, hughesYoungEquation65Bound Cγ Cw j T c u) ≤
        ((15 * T / 4) * c⁻¹ * Real.exp 100 * (6 * T) *
          hughesYoungHeightInputDerivativeConstant Cw j *
          ((T / 16)⁻¹) ^ j) * L := by
  obtain ⟨L, hL, hmoment⟩ :=
    exists_intervalIntegral_exp_neg_84_mul_one_add_abs_pow_le (j + 9)
  refine ⟨33 ^ 4 * L, by positivity, ?_⟩
  intro T c H hT hc hc1 hsmall hH
  let A : ℝ := (15 * T / 4) * c⁻¹ * Real.exp 100 * (6 * T) *
    33 ^ 4 * hughesYoungHeightInputDerivativeConstant Cw j * ((T / 16)⁻¹) ^ j
  let g : ℝ → ℝ := fun u => Real.exp (-84 * u ^ 2) * (1 + |u|) ^ (j + 9)
  have hderiv : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have horder : -H ≤ H := by linarith
  have hleftCont : Continuous
      (fun u => hughesYoungEquation65Bound Cγ Cw j T c u) := by
    have harg : ∀ u : ℝ, 4 * T + |u| + 2 ≠ 0 := by
      intro u
      positivity
    unfold hughesYoungEquation65Bound hughesYoungHeightInputDerivativeConstant
    fun_prop
  have hleftInt : IntervalIntegrable
      (fun u => hughesYoungEquation65Bound Cγ Cw j T c u) volume (-H) H :=
    hleftCont.intervalIntegrable _ _
  have hg : Integrable g := integrable_exp_neg_84_mul_one_add_abs_pow (j + 9)
  have hpoint : ∀ u ∈ Set.Icc (-H) H,
      hughesYoungEquation65Bound Cγ Cw j T c u ≤ A * g u := by
    intro u _hu
    exact hughesYoungEquation65Bound_le_gaussian hCγ hCw j hT hc hc1 hsmall
  calc
    (∫ u in -H..H, hughesYoungEquation65Bound Cγ Cw j T c u) ≤
        ∫ u in -H..H, A * g u := by
      apply intervalIntegral.integral_mono_on horder hleftInt
        (hg.const_mul A).intervalIntegrable
      exact hpoint
    _ = A * ∫ u in -H..H, g u := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ A * L := mul_le_mul_of_nonneg_left (hmoment hH) hA
    _ = _ := by
      dsimp only [A]
      ring

theorem continuous_hughesYoungReducedLocalizedStaticWeight_ordinate
    (T c X Y : ℝ) (h k : ℕ) (x y : ℝ) :
    Continuous (fun u : ℝ =>
      hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y) := by
  unfold hughesYoungReducedLocalizedStaticWeight
    hughesYoungLocalizedLogKernel hughesYoungLogPower
  fun_prop

theorem continuous_hughesYoungReducedStaticShiftMass
    (T c X Y : ℝ) (h k a b M N : ℕ) (r : ℤ) :
    Continuous (fun u : ℝ =>
      hughesYoungReducedStaticShiftMass T c u X Y h k a b M N r) := by
  apply continuous_finsetSum (Finset.Icc 1 M)
  intro m _hm
  apply continuous_finsetSum (Finset.Icc 1 N)
  intro n _hn
  by_cases hs : quadraticDivisorShift a b m n = r
  · simp only [hs, if_true]
    exact (continuous_const.mul continuous_const).mul
      (continuous_hughesYoungReducedLocalizedStaticWeight_ordinate
        T c X Y h k (a * m) (b * n)).norm
  · simp only [hs, if_false]
    exact continuous_const

theorem continuous_hughesYoungFarStaticMass
    (T c P X Y : ℝ) (h k a b M N : ℕ) :
    Continuous (fun u : ℝ =>
      hughesYoungFarStaticMass T c u P X Y h k a b M N) := by
  apply continuous_finsetSum (hughesYoungFarShifts T P X Y a b M N)
  intro r _hr
  exact continuous_hughesYoungReducedStaticShiftMass
    T c X Y h k a b M N r

theorem continuous_hughesYoungEquation65Bound
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ) {T : ℝ} (hT : 0 ≤ T) (c : ℝ) :
    Continuous (fun u : ℝ => hughesYoungEquation65Bound Cγ Cw j T c u) := by
  have harg : ∀ u : ℝ, 4 * T + |u| + 2 ≠ 0 := by
    intro u
    positivity
  unfold hughesYoungEquation65Bound hughesYoungHeightInputDerivativeConstant
  fun_prop

/-- Equation (65), summed over every divisor pair on one literal far shift. -/
theorem exists_farShift_dfiDyadicShiftedDivisorSum_equation65 :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N : ℕ} {r : ℤ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 0 < X → 0 < Y →
      0 < a → 0 < b →
      r ∈ hughesYoungFarShifts T P X Y a b M N →
      (P / (5 * T)) ^ j *
          ‖dfiDyadicShiftedDivisorSum
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
            a b M N r‖ ≤
        (1 / T) * hughesYoungEquation65Bound Cγ Cw j T c u *
          hughesYoungReducedStaticShiftMass T c u X Y h k a b M N r := by
  obtain ⟨Cγ, hCγ, Cw, hCw, h65⟩ :=
    exists_farShift_reducedCleaned_equation65
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N r hT hc hc1 hu hP hPT hX hY ha hb hr
  have hT0 : 0 < T := by linarith
  have hq : 0 ≤ (P / (5 * T)) ^ j := by positivity
  have hnorm :
      ‖dfiDyadicShiftedDivisorSum
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
          a b M N r‖ ≤
        ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ‖if quadraticDivisorShift a b m n = r then
              divisorWeight m * divisorWeight n *
                hughesYoungReducedCleanedShiftWeight T c u X Y h k r
                  (a * m) (b * n)
            else 0‖ := by
    unfold dfiDyadicShiftedDivisorSum
    calc
      ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          if quadraticDivisorShift a b m n = r then
            divisorWeight m * divisorWeight n *
              hughesYoungReducedCleanedShiftWeight T c u X Y h k r
                (a * m) (b * n)
          else 0‖ ≤
          ∑ m ∈ Finset.Icc 1 M,
            ‖∑ n ∈ Finset.Icc 1 N,
              if quadraticDivisorShift a b m n = r then
                divisorWeight m * divisorWeight n *
                  hughesYoungReducedCleanedShiftWeight T c u X Y h k r
                    (a * m) (b * n)
              else 0‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ‖if quadraticDivisorShift a b m n = r then
              divisorWeight m * divisorWeight n *
                hughesYoungReducedCleanedShiftWeight T c u X Y h k r
                  (a * m) (b * n)
            else 0‖ := by
        apply Finset.sum_le_sum
        intro m _hm
        exact norm_sum_le _ _
  calc
    (P / (5 * T)) ^ j *
        ‖dfiDyadicShiftedDivisorSum
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
          a b M N r‖ ≤
      (P / (5 * T)) ^ j *
        (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ‖if quadraticDivisorShift a b m n = r then
              divisorWeight m * divisorWeight n *
                hughesYoungReducedCleanedShiftWeight T c u X Y h k r
                  (a * m) (b * n)
            else 0‖) := mul_le_mul_of_nonneg_left hnorm hq
    _ = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        (P / (5 * T)) ^ j *
          ‖if quadraticDivisorShift a b m n = r then
              divisorWeight m * divisorWeight n *
                hughesYoungReducedCleanedShiftWeight T c u X Y h k r
                  (a * m) (b * n)
            else 0‖ := by
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        (1 / T) * hughesYoungEquation65Bound Cγ Cw j T c u *
          (if quadraticDivisorShift a b m n = r then
            ‖divisorWeight m‖ * ‖divisorWeight n‖ *
              ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k
                (a * m) (b * n)‖
           else 0) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      by_cases hs : quadraticDivisorShift a b m n = r
      · simp only [hs, if_true, norm_mul]
        have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
        have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
        have hxy : (a * m : ℝ) - (b * n : ℝ) = (r : ℝ) := by
          unfold quadraticDivisorShift at hs
          exact_mod_cast hs
        have hterm := h65 j (h := h) (k := k) hT hc hc1 hu hP hPT hX hY
          (by exact_mod_cast Nat.mul_pos ha hmpos)
          (by exact_mod_cast Nat.mul_pos hb hnpos) hxy hr
        calc
          (P / (5 * T)) ^ j *
              (‖divisorWeight m‖ * ‖divisorWeight n‖ *
                ‖hughesYoungReducedCleanedShiftWeight T c u X Y h k r
                  (a * m) (b * n)‖) =
            (‖divisorWeight m‖ * ‖divisorWeight n‖) *
              ((P / (5 * T)) ^ j *
                ‖hughesYoungReducedCleanedShiftWeight T c u X Y h k r
                  (a * m) (b * n)‖) := by ring
          _ ≤ (‖divisorWeight m‖ * ‖divisorWeight n‖) *
              ((1 / T) *
                ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k
                  (a * m) (b * n)‖ *
                hughesYoungEquation65Bound Cγ Cw j T c u) :=
            mul_le_mul_of_nonneg_left hterm (by positivity)
          _ = (1 / T) * hughesYoungEquation65Bound Cγ Cw j T c u *
              (‖divisorWeight m‖ * ‖divisorWeight n‖ *
                ‖hughesYoungReducedLocalizedStaticWeight T c u X Y h k
                  (a * m) (b * n)‖) := by ring
      · simp [hs]
    _ = (1 / T) * hughesYoungEquation65Bound Cγ Cw j T c u *
        hughesYoungReducedStaticShiftMass T c u X Y h k a b M N r := by
      unfold hughesYoungReducedStaticShiftMass
      simp_rw [Finset.mul_sum]

/-- Equation (65) after summing the complete complementary shift family. -/
theorem exists_farShift_sum_equation65 :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 0 < X → 0 < Y →
      0 < a → 0 < b →
      (P / (5 * T)) ^ j *
          ‖∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
            dfiDyadicShiftedDivisorSum
              (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
              a b M N r‖ ≤
        (1 / T) * hughesYoungEquation65Bound Cγ Cw j T c u *
          hughesYoungFarStaticMass T c u P X Y h k a b M N := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hshift⟩ :=
    exists_farShift_dfiDyadicShiftedDivisorSum_equation65
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N hT hc hc1 hu hP hPT hX hY ha hb
  have hT0 : 0 < T := by linarith
  have hq : 0 ≤ (P / (5 * T)) ^ j := by positivity
  calc
    (P / (5 * T)) ^ j *
        ‖∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
          dfiDyadicShiftedDivisorSum
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
            a b M N r‖ ≤
      (P / (5 * T)) ^ j *
        (∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
          ‖dfiDyadicShiftedDivisorSum
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
            a b M N r‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hq
    _ = ∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
        (P / (5 * T)) ^ j *
          ‖dfiDyadicShiftedDivisorSum
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
            a b M N r‖ := by
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
        (1 / T) * hughesYoungEquation65Bound Cγ Cw j T c u *
          hughesYoungReducedStaticShiftMass T c u X Y h k a b M N r := by
      exact Finset.sum_le_sum fun r hr =>
        hshift j hT hc hc1 hu hP hPT hX hY ha hb hr
    _ = (1 / T) * hughesYoungEquation65Bound Cγ Cw j T c u *
        hughesYoungFarStaticMass T c u P X Y h k a b M N := by
      unfold hughesYoungFarStaticMass
      simp_rw [Finset.mul_sum]

/-- The compact Mellin integral of the complete far family.  The factor
`(P/(5T))^j` remains on the left, while the right is the literal integral of
the equation-(65) envelope times the exact static arithmetic mass. -/
theorem exists_integrated_farShift_sum_equation65 :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c H P X Y : ℝ} {h k a b M N : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → 0 ≤ H → H ≤ T / 8 →
      0 < P → P ≤ T → 0 < X → 0 < Y →
      0 < h → 0 < k → 0 < a → 0 < b →
      (P / (5 * T)) ^ j *
          ‖∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
            dfiDyadicShiftedDivisorSum
              (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
              a b M N r‖ ≤
        ∫ u in -H..H,
          hughesYoungEquation65Bound Cγ Cw j T c u *
            hughesYoungFarStaticMass T c u P X Y h k a b M N := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hpoint⟩ := exists_farShift_sum_equation65
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c H P X Y h k a b M N hT hc hc1 hH hHT hP hPT hX hY
    hh hk ha hb
  have hT0 : 0 < T := by linarith
  have hq : 0 ≤ (P / (5 * T)) ^ j := by positivity
  let S : ℝ → ℂ := fun u =>
    ∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
      dfiDyadicShiftedDivisorSum
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
        a b M N r
  let F : ℝ → ℂ := fun u => (T : ℂ) * S u
  let G : ℝ → ℝ := fun u =>
    hughesYoungEquation65Bound Cγ Cw j T c u *
      hughesYoungFarStaticMass T c u P X Y h k a b M N
  have hScont : Continuous S := by
    exact continuous_finsetSum
      (hughesYoungFarShifts T P X Y a b M N) fun r _ =>
        continuous_dfiDyadicShiftedDivisorSum_reducedCleaned_ordinate
          hT0 hc X Y hh hk ha hb r
  have hFcont : Continuous F := continuous_const.mul hScont
  have hGcont : Continuous G :=
    (continuous_hughesYoungEquation65Bound Cγ Cw j hT0.le c).mul
      (continuous_hughesYoungFarStaticMass T c P X Y h k a b M N)
  have hleftCont : Continuous (fun u : ℝ =>
      (P / (5 * T)) ^ j * ‖F u‖) := continuous_const.mul hFcont.norm
  have horder : -H ≤ H := by linarith
  have hbound : ∀ u ∈ Set.Icc (-H) H, (P / (5 * T)) ^ j * ‖F u‖ ≤ G u := by
    intro u hu
    have huAbs : |u| ≤ H := by
      rw [abs_le]
      exact ⟨hu.1, hu.2⟩
    have huT : |u| ≤ T / 8 := huAbs.trans hHT
    have hp := hpoint j (h := h) (k := k) (a := a) (b := b)
      (M := M) (N := N) hT hc hc1 huT hP hPT hX hY ha hb
    dsimp only [F]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    dsimp only [S, G]
    calc
      (P / (5 * T)) ^ j *
          (T * ‖∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
            dfiDyadicShiftedDivisorSum
              (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
              a b M N r‖) =
        T * ((P / (5 * T)) ^ j *
          ‖∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
            dfiDyadicShiftedDivisorSum
              (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
              a b M N r‖) := by ring
      _ ≤ T * ((1 / T) * hughesYoungEquation65Bound Cγ Cw j T c u *
          hughesYoungFarStaticMass T c u P X Y h k a b M N) :=
        mul_le_mul_of_nonneg_left hp hT0.le
      _ = hughesYoungEquation65Bound Cγ Cw j T c u *
          hughesYoungFarStaticMass T c u P X Y h k a b M N := by
        field_simp [hT0.ne']
  rw [sum_dfiDyadicShiftedDivisorSum_gcdReducedIntegratedBox_eq_integral
    hT0 hc H X Y hh hk ha hb
      (hughesYoungFarShifts T P X Y a b M N)]
  change (P / (5 * T)) ^ j * ‖∫ u in -H..H, F u‖ ≤ ∫ u in -H..H, G u
  calc
    (P / (5 * T)) ^ j * ‖∫ u in -H..H, F u‖ ≤
        (P / (5 * T)) ^ j * ∫ u in -H..H, ‖F u‖ :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral.norm_integral_le_integral_norm horder) hq
    _ = ∫ u in -H..H, (P / (5 * T)) ^ j * ‖F u‖ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ u in -H..H, G u := by
      apply intervalIntegral.integral_mono_on horder
        (hleftCont.intervalIntegrable (-H) H)
        (hGcont.intervalIntegrable (-H) H)
      exact hbound

/-- Complete quantitative Hughes--Young consumer for the complementary shift
range.  It combines the exact finite shift partition, equation (65), Fubini,
the native divisor bound, and the Gaussian ordinate integral.  No tail or
arithmetic majorant is supplied as a hypothesis. -/
theorem exists_integrated_farShift_sum_full_bound
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ Cγ D L : ℝ, 0 < Cγ ∧ 0 < D ∧ 0 < L ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ {T c H P X Y : ℝ} {h k a b M N : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → 4 * Cγ * c ≤ 1 →
      0 ≤ H → H ≤ T / 8 →
      0 < P → P ≤ T → 0 < X → 0 < Y →
      0 < h → 0 < k → 0 < a → 0 < b →
      (P / (5 * T)) ^ j *
          ‖∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
            dfiDyadicShiftedDivisorSum
              (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
              a b M N r‖ ≤
        (((15 * T / 4) * c⁻¹ * Real.exp 100 * (6 * T) *
            hughesYoungHeightInputDerivativeConstant Cw j *
            ((T / 16)⁻¹) ^ j) * L) *
          (D * (M : ℝ) ^ (1 + ε) * (N : ℝ) ^ (1 + ε) *
            ‖hughesYoungLocalizedStaticScalar T h k‖ *
            (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
              ((1 / 2 : ℝ) + c) *
            (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
              ((1 / 2 : ℝ) + c)) := by
  obtain ⟨Cγ, hCγ, Cw, hCw, h65⟩ :=
    exists_integrated_farShift_sum_equation65
  obtain ⟨D, hD, hmass⟩ := exists_hughesYoungFarStaticMass_le_rpow ε hε
  obtain ⟨L, hL, heqInt⟩ :=
    exists_intervalIntegral_hughesYoungEquation65Bound_le hCγ hCw j
  refine ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, ?_⟩
  intro T c H P X Y h k a b M N hT hc hc1 hsmall hH hHT hP hPT
    hX hY hh hk ha hb
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hraw := h65 j (T := T) (c := c) (H := H) (P := P)
    (X := X) (Y := Y) (h := h) (k := k) (a := a) (b := b)
    (M := M) (N := N) hT hc hc1 hH hHT hP hPT hX hY hh hk ha hb
  let K : ℝ := D * (M : ℝ) ^ (1 + ε) * (N : ℝ) ^ (1 + ε) *
    ‖hughesYoungLocalizedStaticScalar T h k‖ *
    (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
      ((1 / 2 : ℝ) + c) *
    (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
      ((1 / 2 : ℝ) + c)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hmassPoint : ∀ u : ℝ,
      hughesYoungFarStaticMass T c u P X Y h k a b M N ≤ K := by
    intro u
    exact hmass hX hY hh hk hc
  let E : ℝ → ℝ := fun u => hughesYoungEquation65Bound Cγ Cw j T c u
  let F : ℝ → ℝ := fun u => E u *
    hughesYoungFarStaticMass T c u P X Y h k a b M N
  have hEcont : Continuous E :=
    continuous_hughesYoungEquation65Bound Cγ Cw j hT0.le c
  have hFcont : Continuous F := hEcont.mul
    (continuous_hughesYoungFarStaticMass T c P X Y h k a b M N)
  have hEnonneg : ∀ u, 0 ≤ E u := by
    intro u
    dsimp only [E]
    unfold hughesYoungEquation65Bound
    have hderiv : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
      hughesYoungHeightInputDerivativeConstant_pos hCw j
    positivity
  have horder : -H ≤ H := by linarith
  have hproduct : (∫ u in -H..H, F u) ≤
      K * ∫ u in -H..H, E u := by
    calc
      (∫ u in -H..H, F u) ≤ ∫ u in -H..H, E u * K := by
        apply intervalIntegral.integral_mono_on horder
          (hFcont.intervalIntegrable _ _) ((hEcont.mul_const K).intervalIntegrable _ _)
        intro u _hu
        dsimp only [F]
        exact mul_le_mul_of_nonneg_left (hmassPoint u) (hEnonneg u)
      _ = K * ∫ u in -H..H, E u := by
        rw [intervalIntegral.integral_mul_const]
        ring
  have hEq := heqInt hT1 hc hc1 hsmall hH
  have hfinal : (∫ u in -H..H, F u) ≤
      K * (((15 * T / 4) * c⁻¹ * Real.exp 100 * (6 * T) *
        hughesYoungHeightInputDerivativeConstant Cw j *
        ((T / 16)⁻¹) ^ j) * L) :=
    hproduct.trans (mul_le_mul_of_nonneg_left hEq hK)
  exact hraw.trans (by
    change (∫ u in -H..H, F u) ≤ _ at hfinal
    dsimp only [K] at hfinal ⊢
    nlinarith [hfinal])

end RiemannZeta.GuthMaynard
