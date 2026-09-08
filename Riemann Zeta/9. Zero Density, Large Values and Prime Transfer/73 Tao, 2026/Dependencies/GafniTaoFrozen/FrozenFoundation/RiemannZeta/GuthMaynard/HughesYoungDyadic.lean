import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import RiemannZeta.GuthMaynard.DFIEquation21
import RiemannZeta.GuthMaynard.DFIParametricMellin

open Set
open scoped BigOperators ContDiff

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The smooth dyadic partition used in the Hughes--Young reduction

Hughes--Young split each physical variable into smooth boxes before applying
the quadratic-divisor theorem.  Using ratio `sqrt 2` gives a cutoff supported
on `[1,2]`, exactly matching `DFILocalizedBox`, while consecutive boxes still
overlap.  The construction below is telescoping, so the partition identity is
an equality rather than an inequality or an assumed partition of unity.
-/

/-- The ratio between consecutive Hughes--Young boxes. -/
noncomputable def hughesYoungDyadicRatio : ℝ := Real.sqrt 2

theorem one_lt_hughesYoungDyadicRatio : 1 < hughesYoungDyadicRatio := by
  unfold hughesYoungDyadicRatio
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  nlinarith

theorem hughesYoungDyadicRatio_pos : 0 < hughesYoungDyadicRatio :=
  lt_trans (by norm_num) one_lt_hughesYoungDyadicRatio

theorem hughesYoungDyadicRatio_sq : hughesYoungDyadicRatio ^ 2 = 2 := by
  unfold hughesYoungDyadicRatio
  norm_num

theorem hughesYoungDyadicRatio_lt_two : hughesYoungDyadicRatio < 2 := by
  have hsqrt := hughesYoungDyadicRatio_sq
  have hpos := hughesYoungDyadicRatio_pos
  nlinarith

/-- A decreasing smooth step, equal to one on `(-∞,1]` and zero on
`[sqrt 2,∞)`. -/
noncomputable def hughesYoungDyadicStep (x : ℝ) : ℝ :=
  Real.smoothTransition
    ((hughesYoungDyadicRatio - x) / (hughesYoungDyadicRatio - 1))

theorem contDiff_hughesYoungDyadicStep :
    ContDiff ℝ ∞ hughesYoungDyadicStep := by
  unfold hughesYoungDyadicStep
  fun_prop

theorem hughesYoungDyadicStep_eq_one {x : ℝ} (hx : x ≤ 1) :
    hughesYoungDyadicStep x = 1 := by
  unfold hughesYoungDyadicStep
  apply Real.smoothTransition.one_of_one_le
  rw [one_le_div (sub_pos.mpr one_lt_hughesYoungDyadicRatio)]
  linarith

theorem hughesYoungDyadicStep_eq_zero {x : ℝ}
    (hx : hughesYoungDyadicRatio ≤ x) :
    hughesYoungDyadicStep x = 0 := by
  unfold hughesYoungDyadicStep
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx)
    (sub_nonneg.mpr one_lt_hughesYoungDyadicRatio.le)

/-- The fixed Hughes--Young box cutoff.  It is the difference of two
consecutive smooth steps, hence its scaled copies telescope exactly. -/
noncomputable def hughesYoungDyadicCutoff (x : ℝ) : ℝ :=
  hughesYoungDyadicStep (x / hughesYoungDyadicRatio) -
    hughesYoungDyadicStep x

theorem contDiff_hughesYoungDyadicCutoff :
    ContDiff ℝ ∞ hughesYoungDyadicCutoff := by
  unfold hughesYoungDyadicCutoff
  exact (contDiff_hughesYoungDyadicStep.comp
    (contDiff_id.div_const hughesYoungDyadicRatio)).sub
      contDiff_hughesYoungDyadicStep

theorem hughesYoungDyadicCutoff_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) :
    hughesYoungDyadicCutoff x = 0 := by
  have hratio : x / hughesYoungDyadicRatio ≤ 1 := by
    rw [div_le_one hughesYoungDyadicRatio_pos]
    exact hx.trans one_lt_hughesYoungDyadicRatio.le
  rw [hughesYoungDyadicCutoff, hughesYoungDyadicStep_eq_one hratio,
    hughesYoungDyadicStep_eq_one hx]
  ring

theorem hughesYoungDyadicCutoff_eq_zero_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    hughesYoungDyadicCutoff x = 0 := by
  have hratio : hughesYoungDyadicRatio ≤ x / hughesYoungDyadicRatio := by
    rw [le_div_iff₀ hughesYoungDyadicRatio_pos]
    calc
      hughesYoungDyadicRatio * hughesYoungDyadicRatio =
          hughesYoungDyadicRatio ^ 2 := by ring
      _ = 2 := hughesYoungDyadicRatio_sq
      _ ≤ x := hx
  have hx' : hughesYoungDyadicRatio ≤ x :=
    le_trans hughesYoungDyadicRatio_lt_two.le hx
  rw [hughesYoungDyadicCutoff, hughesYoungDyadicStep_eq_zero hratio,
    hughesYoungDyadicStep_eq_zero hx']
  ring

/-- The fixed Hughes--Young cutoff is nonnegative on the positive axis. -/
theorem hughesYoungDyadicCutoff_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ hughesYoungDyadicCutoff x := by
  unfold hughesYoungDyadicCutoff hughesYoungDyadicStep
  apply sub_nonneg.mpr
  apply Real.smoothTransition.monotone
  apply div_le_div_of_nonneg_right _
    (sub_nonneg.mpr one_lt_hughesYoungDyadicRatio.le)
  have hratio : x / hughesYoungDyadicRatio ≤ x := by
    exact div_le_self hx one_lt_hughesYoungDyadicRatio.le
  linarith

/-- The fixed Hughes--Young cutoff never exceeds one. -/
theorem hughesYoungDyadicCutoff_le_one (x : ℝ) :
    hughesYoungDyadicCutoff x ≤ 1 := by
  unfold hughesYoungDyadicCutoff hughesYoungDyadicStep
  linarith [Real.smoothTransition.le_one
      ((hughesYoungDyadicRatio - x / hughesYoungDyadicRatio) /
        (hughesYoungDyadicRatio - 1)),
    Real.smoothTransition.nonneg
      ((hughesYoungDyadicRatio - x) /
        (hughesYoungDyadicRatio - 1))]

theorem support_hughesYoungDyadicCutoff_subset :
    Function.support hughesYoungDyadicCutoff ⊆ Set.Icc 1 2 := by
  intro x hx
  constructor
  · by_contra h
    exact hx (hughesYoungDyadicCutoff_eq_zero_of_le_one (le_of_not_ge h))
  · by_contra h
    exact hx (hughesYoungDyadicCutoff_eq_zero_of_two_le (le_of_not_ge h))

theorem hasCompactSupport_hughesYoungDyadicCutoff :
    HasCompactSupport hughesYoungDyadicCutoff :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    support_hughesYoungDyadicCutoff_subset

/-- The physical scale of the `j`th box. -/
noncomputable def hughesYoungDyadicScale (j : ℕ) : ℝ :=
  hughesYoungDyadicRatio ^ j

theorem one_le_hughesYoungDyadicScale (j : ℕ) :
    1 ≤ hughesYoungDyadicScale j := by
  unfold hughesYoungDyadicScale
  exact one_le_pow₀ one_lt_hughesYoungDyadicRatio.le

theorem hughesYoungDyadicScale_pos (j : ℕ) :
    0 < hughesYoungDyadicScale j :=
  lt_of_lt_of_le (by norm_num) (one_le_hughesYoungDyadicScale j)

/-- A copy of the fixed cutoff at physical scale `X`. -/
noncomputable def hughesYoungDyadicCutoffAt (X x : ℝ) : ℝ :=
  hughesYoungDyadicCutoff (x / X)

/-- Every positive-scale physical cutoff lies in `[0,1]` on positive input. -/
theorem hughesYoungDyadicCutoffAt_mem_Icc {X x : ℝ}
    (hX : 0 < X) (hx : 0 ≤ x) :
    hughesYoungDyadicCutoffAt X x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold hughesYoungDyadicCutoffAt
  exact ⟨hughesYoungDyadicCutoff_nonneg (div_nonneg hx hX.le),
    hughesYoungDyadicCutoff_le_one _⟩

theorem abs_hughesYoungDyadicCutoffAt_le_one {X x : ℝ}
    (hX : 0 < X) (hx : 0 ≤ x) :
    |hughesYoungDyadicCutoffAt X x| ≤ 1 := by
  have hcut := hughesYoungDyadicCutoffAt_mem_Icc hX hx
  rw [abs_of_nonneg hcut.1]
  exact hcut.2

theorem hughesYoungDyadicCutoff_eq_one_at_ratio :
    hughesYoungDyadicCutoff hughesYoungDyadicRatio = 1 := by
  unfold hughesYoungDyadicCutoff
  rw [div_self hughesYoungDyadicRatio_pos.ne',
    hughesYoungDyadicStep_eq_one (le_refl 1),
    hughesYoungDyadicStep_eq_zero (le_refl hughesYoungDyadicRatio)]
  ring

/-- Centering a physical cutoff at `x / sqrt 2` makes its value at the
positive point `x` exactly one.  This supplies a smooth local chart for the
isolated endpoint terms without changing their value. -/
theorem hughesYoungDyadicCutoffAt_eq_one_centered
    {x : ℝ} (hx : 0 < x) :
    hughesYoungDyadicCutoffAt (x / hughesYoungDyadicRatio) x = 1 := by
  unfold hughesYoungDyadicCutoffAt
  have hcenter : x / (x / hughesYoungDyadicRatio) =
      hughesYoungDyadicRatio := by
    field_simp [hx.ne', hughesYoungDyadicRatio_pos.ne']
  rw [hcenter]
  exact hughesYoungDyadicCutoff_eq_one_at_ratio

theorem contDiff_hughesYoungDyadicCutoffAt (X : ℝ) :
    ContDiff ℝ ∞ (hughesYoungDyadicCutoffAt X) := by
  unfold hughesYoungDyadicCutoffAt
  exact contDiff_hughesYoungDyadicCutoff.comp (contDiff_id.div_const X)

theorem support_hughesYoungDyadicCutoffAt_subset {X : ℝ} (hX : 0 < X) :
    Function.support (hughesYoungDyadicCutoffAt X) ⊆ Set.Icc X (2 * X) := by
  intro x hx
  have hx' : x / X ∈ Set.Icc (1 : ℝ) 2 :=
    support_hughesYoungDyadicCutoff_subset hx
  constructor
  · simpa using (le_div_iff₀ hX).mp hx'.1
  · exact (div_le_iff₀ hX).mp hx'.2

theorem hasCompactSupport_hughesYoungDyadicCutoffAt {X : ℝ} (hX : 0 < X) :
    HasCompactSupport (hughesYoungDyadicCutoffAt X) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_hughesYoungDyadicCutoffAt_subset hX)

/-- A globally smooth weight supported in one positive dyadic box satisfies
DFI equation (2) for every derivative scale `P ≥ 1`.  This is a qualitative
constructor: later Hughes--Young estimates use an explicit uniform profile,
but no separate equation-(2) assumption is needed even at this stage. -/
theorem DFIEquation2.of_smooth_dyadicBox
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ}
    (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hsmooth : ContDiff ℝ ∞ (Function.uncurry f))
    (hbox : DFILocalizedBox f X Y) :
    DFIEquation2 f P X Y := by
  have hcompact : HasCompactSupport (Function.uncurry f) :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc.prod isCompact_Icc) hbox.support_subset
  refine
    { one_le_P := hP
      one_le_X := hX
      one_le_Y := hY
      smooth := hsmooth
      compactSupport := hcompact
      support_pos := ?_
      derivativeBound := ?_ }
  · intro p hp
    have hpBox := hbox.support_subset hp
    exact ⟨lt_of_lt_of_le (by norm_num) (hX.trans hpBox.1.1),
      lt_of_lt_of_le (by norm_num) (hY.trans hpBox.2.1)⟩
  · intro i j
    obtain ⟨K, hK, hBound⟩ :=
      exists_uniform_norm_dfiMixedDeriv_of_support hsmooth
        hbox.support_subset i j
    let C : ℝ :=
      9 * (2 * X) ^ i * (2 * Y) ^ j * (K + 1)
    have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
    have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY
    have hC : 0 < C := by
      dsimp [C]
      positivity
    refine ⟨C, hC, ?_⟩
    intro x y hx hy
    by_cases hd : dfiMixedDeriv i j f x y = 0
    · rw [hd, norm_zero, mul_zero]
      positivity
    · have hmem : (x, y) ∈ Function.support
          (Function.uncurry (dfiMixedDeriv i j f)) := by
        simpa only [Function.mem_support, Function.uncurry_apply_pair] using hd
      have htsupport : tsupport (Function.uncurry f) ⊆
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
        closure_minimal hbox.support_subset
          (isClosed_Icc.prod isClosed_Icc)
      have hxy := htsupport
        (support_dfiMixedDeriv_subset_tsupport hsmooth i j hmem)
      have hxPow : |x| ^ i ≤ (2 * X) ^ i := by
        rw [abs_of_pos hx]
        exact pow_le_pow_left₀ hx.le hxy.1.2 i
      have hyPow : |y| ^ j ≤ (2 * Y) ^ j := by
        rw [abs_of_pos hy]
        exact pow_le_pow_left₀ hy.le hxy.2.2 j
      have hleft :
          |x| ^ i * |y| ^ j * ‖dfiMixedDeriv i j f x y‖ ≤
            (2 * X) ^ i * (2 * Y) ^ j * K := by
        gcongr
        exact hBound x y
      have hxDiv : x / X ≤ 2 := (div_le_iff₀ hXpos).2 hxy.1.2
      have hyDiv : y / Y ≤ 2 := (div_le_iff₀ hYpos).2 hxy.2.2
      have hxDenPos : 0 < 1 + x / X := by positivity
      have hyDenPos : 0 < 1 + y / Y := by positivity
      have hxInv : (3 : ℝ)⁻¹ ≤ (1 + x / X)⁻¹ := by
        simpa only [one_div] using
          one_div_le_one_div_of_le hxDenPos (by linarith : 1 + x / X ≤ 3)
      have hyInv : (3 : ℝ)⁻¹ ≤ (1 + y / Y)⁻¹ := by
        simpa only [one_div] using
          one_div_le_one_div_of_le hyDenPos (by linarith : 1 + y / Y ≤ 3)
      have hPpow : 1 ≤ P ^ (i + j) := one_le_pow₀ hP
      calc
        |x| ^ i * |y| ^ j * ‖dfiMixedDeriv i j f x y‖ ≤
            (2 * X) ^ i * (2 * Y) ^ j * K := hleft
        _ ≤ (2 * X) ^ i * (2 * Y) ^ j * (K + 1) := by
          gcongr
          linarith
        _ = C * (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ * 1 := by
          dsimp [C]
          ring
        _ ≤ C * (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j) := by
          gcongr

/-- Algebraic telescoping of the finite ratio-`sqrt 2` partition. -/
theorem sum_hughesYoungDyadicCutoff_eq (K : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range (K + 1),
      hughesYoungDyadicCutoffAt (hughesYoungDyadicScale j) x) =
      hughesYoungDyadicStep
          (x / hughesYoungDyadicRatio ^ (K + 1)) -
        hughesYoungDyadicStep x := by
  induction K with
  | zero =>
      simp [hughesYoungDyadicCutoffAt, hughesYoungDyadicScale,
        hughesYoungDyadicCutoff]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [hughesYoungDyadicCutoffAt, hughesYoungDyadicScale,
        hughesYoungDyadicCutoff]
      have hscale :
          x / hughesYoungDyadicRatio ^ (K + 1) /
              hughesYoungDyadicRatio =
            x / hughesYoungDyadicRatio ^ (K + 1 + 1) := by
        calc
          x / hughesYoungDyadicRatio ^ (K + 1) /
              hughesYoungDyadicRatio =
              x / (hughesYoungDyadicRatio ^ (K + 1) *
                hughesYoungDyadicRatio) := div_div _ _ _
          _ = x / hughesYoungDyadicRatio ^ (K + 1 + 1) := by
            congr 1
      rw [hscale]
      ring

/-- On the complete positive range, the finite smooth box family sums
exactly to one.  The lower hypothesis excludes only the isolated physical
boundary value `x=1`, which is peeled off separately in the arithmetic sum. -/
theorem sum_hughesYoungDyadicCutoff_eq_one {K : ℕ} {x : ℝ}
    (hxLower : hughesYoungDyadicRatio ≤ x)
    (hxUpper : x ≤ hughesYoungDyadicRatio ^ (K + 1)) :
    (∑ j ∈ Finset.range (K + 1),
      hughesYoungDyadicCutoffAt (hughesYoungDyadicScale j) x) = 1 := by
  rw [sum_hughesYoungDyadicCutoff_eq,
    hughesYoungDyadicStep_eq_zero hxLower]
  have hpow : 0 < hughesYoungDyadicRatio ^ (K + 1) :=
    pow_pos hughesYoungDyadicRatio_pos _
  have hquot : x / hughesYoungDyadicRatio ^ (K + 1) ≤ 1 := by
    exact (div_le_one hpow).mpr hxUpper
  rw [hughesYoungDyadicStep_eq_one hquot]
  ring

end RiemannZeta.GuthMaynard
