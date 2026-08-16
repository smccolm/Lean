import RiemannZeta.GuthMaynard.HughesYoungDFIProfile

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young consumption of the DFI quadratic-divisor theorem

The local DFI profile in `HughesYoungDFIProfile` deliberately gives a
scale-free bound for one box.  The global Hughes--Young argument additionally
needs the exact size of that box, namely
`(h / X)^(1/2+c) (k / Y)^(1/2+c)`.  This file retains that factor through
the derivative estimates, applies the uniform signed DFI theorem, and then
assembles the Mellin, dyadic, arithmetic, and height sums.
-/

theorem rpow_div_le_rpow_div_of_le
    {h X x α : ℝ} (hh : 0 < h) (hX : 0 < X) (hx : X ≤ x)
    (hα : 0 ≤ α) :
    (h / x) ^ α ≤ (h / X) ^ α := by
  have hx0 : 0 < x := hX.trans_le hx
  apply Real.rpow_le_rpow (div_nonneg hh.le hx0.le)
  · exact div_le_div_of_nonneg_left hh.le hX hx
  · exact hα

/-- Scale-retaining version of the exact logarithmic-power derivative
estimate. -/
theorem abs_pow_mul_norm_iteratedDeriv_hughesYoungLogPower_shift_scale_le
    {X x h c u : ℝ} (hX : 0 < X) (hx : X ≤ x)
    (hh : 0 < h) (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    |x| ^ n * ‖iteratedDeriv n
        (fun z : ℝ => hughesYoungLogPower
          ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) (z / h)) x‖ ≤
      (|u| + 2 + n) ^ n * (h / X) ^ ((1 / 2 : ℝ) + c) := by
  let s : ℂ := (1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)
  have hx0 : 0 < x := hX.trans_le hx
  have hsre : s.re = (1 / 2 : ℝ) + c := by simp [s]
  have hsnorm : ‖-s‖ ≤ |u| + 2 := by
    rw [norm_neg]
    have hsEq : s = (((1 / 2 : ℝ) + c : ℝ) : ℂ) + (u : ℂ) * I := by
      dsimp only [s]
      push_cast
      ring
    rw [hsEq]
    calc
      ‖(((1 / 2 : ℝ) + c : ℝ) : ℂ) + (u : ℂ) * I‖ ≤
          ‖(((1 / 2 : ℝ) + c : ℝ) : ℂ)‖ + ‖(u : ℂ) * I‖ :=
        norm_add_le _ _
      _ = |(1 / 2 : ℝ) + c| + |u| := by
        rw [norm_mul, norm_I, mul_one, norm_real, norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |u| + 2 := by
        rw [abs_of_pos (by positivity : 0 < (1 / 2 : ℝ) + c)]
        linarith
  have hcoeff : ‖gmCpowDerivativeCoeff (-s) n‖ ≤
      (|u| + 2 + n) ^ n :=
    (norm_gmCpowDerivativeCoeff_le (-s) n).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) n)
  have hratio : (h / x) ^ s.re ≤
      (h / X) ^ ((1 / 2 : ℝ) + c) := by
    rw [hsre]
    exact rpow_div_le_rpow_div_of_le hh hX hx (by positivity)
  rw [show (fun z : ℝ => hughesYoungLogPower
      ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) (z / h)) =
      fun z : ℝ => hughesYoungLogPower s (z / h) by rfl,
    abs_pow_mul_norm_iteratedDeriv_hughesYoungLogPower_div s n hx0 hh]
  exact mul_le_mul hcoeff hratio
    (Real.rpow_nonneg (div_nonneg hh.le hx0.le) _) (by positivity)

/-- The localized one-variable factor retains its physical box decay. -/
theorem abs_pow_mul_norm_iteratedDeriv_hughesYoungLocalizedOneFactor_scale_le
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (X : ℝ), 0 < X → ∀ x : ℝ,
      |x| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt X) x‖ ≤ Ccut n)
    {X x h c u : ℝ} (hX : 0 < X) (hx : X ≤ x)
    (hh : 0 < h) (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    |x| ^ n * ‖iteratedDeriv n
        (hughesYoungLocalizedOneFactor X h
          ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) x‖ ≤
      hughesYoungOneFactorDerivativeProfile Ccut u n *
        (h / X) ^ ((1 / 2 : ℝ) + c) := by
  let s : ℂ := (1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)
  have hx0 : 0 < x := hX.trans_le hx
  rw [show ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) = s by rfl,
    iteratedDeriv_hughesYoungLocalizedOneFactor hh hx0 s n]
  calc
    |x| ^ n * ‖∑ q ∈ Finset.range (n + 1),
        (n.choose q : ℂ) *
          iteratedDeriv q
            (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x *
          iteratedDeriv (n - q)
            (fun z : ℝ => hughesYoungLogPower s (z / h)) x‖ ≤
        ∑ q ∈ Finset.range (n + 1), |x| ^ n *
          ‖(n.choose q : ℂ) *
            iteratedDeriv q
              (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x *
            iteratedDeriv (n - q)
              (fun z : ℝ => hughesYoungLogPower s (z / h)) x‖ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
        (pow_nonneg (abs_nonneg x) n)
    _ ≤ ∑ q ∈ Finset.range (n + 1),
        ((n.choose q : ℝ) * Ccut q *
          ((|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
            2 ^ (3 / 2 : ℝ))) *
          (h / X) ^ ((1 / 2 : ℝ) + c) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqn : q ≤ n := by
        have : q < n + 1 := Finset.mem_range.mp hq
        omega
      have hcutComplex :
          |x| ^ q * ‖iteratedDeriv q
            (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x‖ ≤
              Ccut q := by
        rw [congrFun (iteratedDeriv_ofReal_comp
          (hughesYoungDyadicCutoffAt X)
          (contDiff_hughesYoungDyadicCutoffAt X) q) x,
          norm_real, Real.norm_eq_abs]
        simpa using (hcut q).2 X hX x
      have hpowBound :=
        abs_pow_mul_norm_iteratedDeriv_hughesYoungLogPower_shift_scale_le
          (u := u) hX hx hh hc hc1 (n - q)
      have hratio0 : 0 ≤ (h / X) ^ ((1 / 2 : ℝ) + c) :=
        Real.rpow_nonneg (div_nonneg hh.le hX.le) _
      have hone : (1 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) :=
        Real.one_le_rpow (by norm_num) (by norm_num)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have hxpow : |x| ^ n = |x| ^ q * |x| ^ (n - q) := by
        rw [← pow_add, Nat.add_sub_of_le hqn]
      rw [hxpow]
      calc
        (|x| ^ q * |x| ^ (n - q)) *
            ((n.choose q : ℝ) *
              ‖iteratedDeriv q
                (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x‖ *
              ‖iteratedDeriv (n - q)
                (fun z : ℝ => hughesYoungLogPower s (z / h)) x‖) =
            (n.choose q : ℝ) *
              (|x| ^ q * ‖iteratedDeriv q
                (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x‖) *
              (|x| ^ (n - q) * ‖iteratedDeriv (n - q)
                (fun z : ℝ => hughesYoungLogPower s (z / h)) x‖) := by ring
        _ ≤ (n.choose q : ℝ) * Ccut q *
            ((|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
              (h / X) ^ ((1 / 2 : ℝ) + c)) := by
          have hprod :
              (|x| ^ q * ‖iteratedDeriv q
                  (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x‖) *
                (|x| ^ (n - q) * ‖iteratedDeriv (n - q)
                  (fun z : ℝ => hughesYoungLogPower s (z / h)) x‖) ≤
              Ccut q *
                ((|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
                  (h / X) ^ ((1 / 2 : ℝ) + c)) := by
            exact mul_le_mul hcutComplex hpowBound
              (by positivity) (hcut q).1.le
          simpa only [mul_assoc] using
            (mul_le_mul_of_nonneg_left hprod
              (Nat.cast_nonneg (n.choose q)))
        _ ≤ ((n.choose q : ℝ) * Ccut q *
            ((|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
              2 ^ (3 / 2 : ℝ))) *
            (h / X) ^ ((1 / 2 : ℝ) + c) := by
          have hbase : 0 ≤
              (n.choose q : ℝ) * Ccut q *
                (|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) := by
            exact mul_nonneg
              (mul_nonneg (by positivity) (hcut q).1.le)
              (pow_nonneg (by positivity) _)
          calc
            (n.choose q : ℝ) * Ccut q *
                  ((|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
                    (h / X) ^ ((1 / 2 : ℝ) + c)) =
                ((n.choose q : ℝ) * Ccut q *
                  (|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q)) *
                    (h / X) ^ ((1 / 2 : ℝ) + c) := by ring
            _ ≤ (((n.choose q : ℝ) * Ccut q *
                  (|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q)) *
                    2 ^ (3 / 2 : ℝ)) *
                    (h / X) ^ ((1 / 2 : ℝ) + c) :=
              mul_le_mul_of_nonneg_right
                (calc
                  (n.choose q : ℝ) * Ccut q *
                        (|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) =
                      ((n.choose q : ℝ) * Ccut q *
                        (|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q)) * 1 := by ring
                  _ ≤ ((n.choose q : ℝ) * Ccut q *
                        (|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q)) *
                      2 ^ (3 / 2 : ℝ) :=
                    mul_le_mul_of_nonneg_left hone hbase)
                hratio0
            _ = _ := by ring
    _ = hughesYoungOneFactorDerivativeProfile Ccut u n *
        (h / X) ^ ((1 / 2 : ℝ) + c) := by
      unfold hughesYoungOneFactorDerivativeProfile
      rw [Finset.sum_mul]

/-- The complete shifted `y` factor retains the exact dyadic decay
`(k / Y)^(1/2+c)` needed when the DFI boxes are summed. -/
theorem abs_pow_mul_norm_iteratedDeriv_hughesYoungDFICoreY_scale_le
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (X : ℝ), 0 < X → ∀ x : ℝ,
      |x| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt X) x‖ ≤ Ccut n)
    {T c u Y y P A : ℝ} {k : ℕ} {r : ℤ} (j : ℕ)
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hY : 0 < Y) (hyLower : Y ≤ y) (hyUpper : y ≤ 2 * Y)
    (hk : 0 < k) (hr : |(r : ℝ)| ≤ Y / 2) (hP : 1 ≤ P)
    (hTR : T * (|(r : ℝ)| / Y) ≤ P) (hA : 0 ≤ A)
    (hheight : ∀ (n : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ n * A)) :
    |y| ^ j * ‖iteratedDeriv j (hughesYoungDFICoreY T c u Y k r) y‖ ≤
      hughesYoungCoreYDerivativeProfile Ccut u j *
        (k / Y) ^ ((1 / 2 : ℝ) + c) * A * P ^ j := by
  have hrStrict : |(r : ℝ)| < Y := by linarith
  rw [iteratedDeriv_hughesYoungDFICoreY
    (lt_of_lt_of_le zero_lt_one hT) hc u hY hk r hrStrict j hyLower]
  calc
    |y| ^ j * ‖∑ q ∈ Finset.range (j + 1),
        (j.choose q : ℂ) *
          iteratedDeriv q
            (hughesYoungLocalizedOneFactor Y k
              ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y *
          ((1 / (T : ℂ)) *
            iteratedDeriv (j - q)
              (fun z : ℝ => hughesYoungHeightTransform T c u
                (-Real.log (1 + (r : ℝ) / z))) y)‖ ≤
        ∑ q ∈ Finset.range (j + 1), |y| ^ j *
          ‖(j.choose q : ℂ) *
            iteratedDeriv q
              (hughesYoungLocalizedOneFactor Y k
                ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y *
            ((1 / (T : ℂ)) *
              iteratedDeriv (j - q)
                (fun z : ℝ => hughesYoungHeightTransform T c u
                  (-Real.log (1 + (r : ℝ) / z))) y)‖ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
        (pow_nonneg (abs_nonneg y) j)
    _ ≤ ∑ q ∈ Finset.range (j + 1),
        ((j.choose q : ℝ) *
          hughesYoungOneFactorDerivativeProfile Ccut u q *
          hughesYoungShiftCompositionConstant (j - q)) *
          (k / Y) ^ ((1 / 2 : ℝ) + c) * A * P ^ j := by
      apply Finset.sum_le_sum
      intro q hq
      have hqj : q ≤ j := by
        have : q < j + 1 := Finset.mem_range.mp hq
        omega
      have hone :=
        abs_pow_mul_norm_iteratedDeriv_hughesYoungLocalizedOneFactor_scale_le
          (u := u) Ccut hcut hY hyLower
            (show 0 < (k : ℝ) by exact_mod_cast hk) hc hc1 q
      have hshift := norm_iteratedDeriv_hughesYoung_height_shift_le
        (n := j - q) hT hc hY hyLower hyUpper hr hP hTR hA hheight
      have hpow : P ^ (j - q) ≤ P ^ j :=
        pow_le_pow_right₀ hP (Nat.sub_le j q)
      have hnormeq :
          ‖(j.choose q : ℂ) *
              iteratedDeriv q
                (hughesYoungLocalizedOneFactor Y k
                  ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y *
              ((1 / (T : ℂ)) *
                iteratedDeriv (j - q)
                  (fun z : ℝ => hughesYoungHeightTransform T c u
                    (-Real.log (1 + (r : ℝ) / z))) y)‖ =
            (j.choose q : ℝ) *
            ‖iteratedDeriv q
              (hughesYoungLocalizedOneFactor Y k
                ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y‖ *
            ‖(1 / (T : ℂ)) *
              iteratedDeriv (j - q)
                (fun z : ℝ => hughesYoungHeightTransform T c u
                  (-Real.log (1 + (r : ℝ) / z))) y‖ := by
        simp only [norm_mul, Complex.norm_natCast]
      rw [hnormeq]
      have hfactorProfileNonneg :
          0 ≤ hughesYoungOneFactorDerivativeProfile Ccut u q :=
        (hughesYoungOneFactorDerivativeProfile_pos Ccut
          (fun n => (hcut n).1) u q).le
      have hshiftProfileNonneg :
          0 ≤ hughesYoungShiftCompositionConstant (j - q) :=
        le_trans (by norm_num)
          (one_le_hughesYoungShiftCompositionConstant (j - q))
      have hscale0 : 0 ≤ (k / Y) ^ ((1 / 2 : ℝ) + c) :=
        Real.rpow_nonneg (div_nonneg (by exact_mod_cast hk.le) hY.le) _
      have hypow : |y| ^ j = |y| ^ q * |y| ^ (j - q) := by
        rw [← pow_add, Nat.add_sub_of_le hqj]
      rw [hypow]
      calc
        (|y| ^ q * |y| ^ (j - q)) *
            ((j.choose q : ℝ) *
              ‖iteratedDeriv q
                (hughesYoungLocalizedOneFactor Y k
                  ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y‖ *
              ‖(1 / (T : ℂ)) *
                iteratedDeriv (j - q)
                  (fun z : ℝ => hughesYoungHeightTransform T c u
                    (-Real.log (1 + (r : ℝ) / z))) y‖) =
            (j.choose q : ℝ) *
              (|y| ^ q * ‖iteratedDeriv q
                (hughesYoungLocalizedOneFactor Y k
                  ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y‖) *
              (|y| ^ (j - q) *
                ‖(1 / (T : ℂ)) *
                  iteratedDeriv (j - q)
                    (fun z : ℝ => hughesYoungHeightTransform T c u
                      (-Real.log (1 + (r : ℝ) / z))) y‖) := by ring
        _ ≤ (j.choose q : ℝ) *
              (hughesYoungOneFactorDerivativeProfile Ccut u q *
                (k / Y) ^ ((1 / 2 : ℝ) + c)) *
              (hughesYoungShiftCompositionConstant (j - q) * A *
                P ^ (j - q)) := by gcongr
        _ = ((j.choose q : ℝ) *
              hughesYoungOneFactorDerivativeProfile Ccut u q *
              hughesYoungShiftCompositionConstant (j - q)) *
                (k / Y) ^ ((1 / 2 : ℝ) + c) * A * P ^ (j - q) := by ring
        _ ≤ ((j.choose q : ℝ) *
              hughesYoungOneFactorDerivativeProfile Ccut u q *
              hughesYoungShiftCompositionConstant (j - q)) *
                (k / Y) ^ ((1 / 2 : ℝ) + c) * A * P ^ j := by
          exact mul_le_mul_of_nonneg_left hpow
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (mul_nonneg (by positivity) hfactorProfileNonneg)
                  hshiftProfileNonneg) hscale0) hA)
    _ = hughesYoungCoreYDerivativeProfile Ccut u j *
        (k / Y) ^ ((1 / 2 : ℝ) + c) * A * P ^ j := by
      unfold hughesYoungCoreYDerivativeProfile
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]

/-- Scale-retaining two-variable derivative estimate for the literal
Hughes--Young fixed-shift DFI core. -/
theorem abs_pow_mul_abs_pow_mul_norm_dfiMixedDeriv_hughesYoungDFICore_scale_le
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (Z : ℝ), 0 < Z → ∀ z : ℝ,
      |z| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt Z) z‖ ≤ Ccut n)
    {T c u X Y x y P A : ℝ} {h k : ℕ} {r : ℤ} (i j : ℕ)
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 0 < X) (hxLower : X ≤ x)
    (hY : 0 < Y) (hyLower : Y ≤ y) (hyUpper : y ≤ 2 * Y)
    (hh : 0 < h) (hk : 0 < k)
    (hr : |(r : ℝ)| ≤ Y / 2) (hP : 1 ≤ P)
    (hTR : T * (|(r : ℝ)| / Y) ≤ P) (hA : 0 ≤ A)
    (hheight : ∀ (n : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ n * A)) :
    |x| ^ i * |y| ^ j *
        ‖dfiMixedDeriv i j (hughesYoungDFICore T c u X Y h k r) x y‖ ≤
      hughesYoungOneFactorDerivativeProfile Ccut u i *
        hughesYoungCoreYDerivativeProfile Ccut u j *
        ((h / X) ^ ((1 / 2 : ℝ) + c) *
          (k / Y) ^ ((1 / 2 : ℝ) + c)) * A * P ^ (i + j) := by
  have hrStrict : |(r : ℝ)| < Y := by linarith
  rw [dfiMixedDeriv_hughesYoungDFICore
    (lt_of_lt_of_le zero_lt_one hT) hc u hX hY hh hk r hrStrict i j x y,
    norm_mul]
  have hxBound :=
    abs_pow_mul_norm_iteratedDeriv_hughesYoungLocalizedOneFactor_scale_le
      (u := u) Ccut hcut hX hxLower
        (show 0 < (h : ℝ) by exact_mod_cast hh) hc hc1 i
  have hyBound := abs_pow_mul_norm_iteratedDeriv_hughesYoungDFICoreY_scale_le
    Ccut hcut j hT hc hc1 hY hyLower hyUpper hk hr hP hTR hA hheight
  have hxProfileNonneg :
      0 ≤ hughesYoungOneFactorDerivativeProfile Ccut u i :=
    (hughesYoungOneFactorDerivativeProfile_pos Ccut
      (fun n => (hcut n).1) u i).le
  have hyProfileNonneg :
      0 ≤ hughesYoungCoreYDerivativeProfile Ccut u j :=
    (hughesYoungCoreYDerivativeProfile_pos Ccut
      (fun n => (hcut n).1) u j).le
  have hxScale0 : 0 ≤ (h / X) ^ ((1 / 2 : ℝ) + c) :=
    Real.rpow_nonneg (div_nonneg (by exact_mod_cast hh.le) hX.le) _
  have hyScale0 : 0 ≤ (k / Y) ^ ((1 / 2 : ℝ) + c) :=
    Real.rpow_nonneg (div_nonneg (by exact_mod_cast hk.le) hY.le) _
  have hpow : P ^ j ≤ P ^ (i + j) :=
    pow_le_pow_right₀ hP (Nat.le_add_left j i)
  calc
    |x| ^ i * |y| ^ j *
          (‖iteratedDeriv i
              (hughesYoungLocalizedOneFactor X h
                ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) x‖ *
            ‖iteratedDeriv j (hughesYoungDFICoreY T c u Y k r) y‖) =
        (|x| ^ i *
            ‖iteratedDeriv i
              (hughesYoungLocalizedOneFactor X h
                ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) x‖) *
          (|y| ^ j *
            ‖iteratedDeriv j (hughesYoungDFICoreY T c u Y k r) y‖) := by ring
    _ ≤ (hughesYoungOneFactorDerivativeProfile Ccut u i *
          (h / X) ^ ((1 / 2 : ℝ) + c)) *
          (hughesYoungCoreYDerivativeProfile Ccut u j *
            (k / Y) ^ ((1 / 2 : ℝ) + c) * A * P ^ j) := by
      exact mul_le_mul hxBound hyBound (by positivity)
        (mul_nonneg hxProfileNonneg hxScale0)
    _ = (hughesYoungOneFactorDerivativeProfile Ccut u i *
          hughesYoungCoreYDerivativeProfile Ccut u j *
          ((h / X) ^ ((1 / 2 : ℝ) + c) *
            (k / Y) ^ ((1 / 2 : ℝ) + c)) * A) * P ^ j := by ring
    _ ≤ (hughesYoungOneFactorDerivativeProfile Ccut u i *
          hughesYoungCoreYDerivativeProfile Ccut u j *
          ((h / X) ^ ((1 / 2 : ℝ) + c) *
            (k / Y) ^ ((1 / 2 : ℝ) + c)) * A) * P ^ (i + j) := by
      exact mul_le_mul_of_nonneg_left hpow
        (mul_nonneg
          (mul_nonneg (mul_nonneg hxProfileNonneg hyProfileNonneg)
            (mul_nonneg hxScale0 hyScale0)) hA)
    _ = hughesYoungOneFactorDerivativeProfile Ccut u i *
        hughesYoungCoreYDerivativeProfile Ccut u j *
        ((h / X) ^ ((1 / 2 : ℝ) + c) *
          (k / Y) ^ ((1 / 2 : ℝ) + c)) * A * P ^ (i + j) := by ring

/-! ## A normalization which preserves the summable box scale -/

noncomputable def hughesYoungScaledDFINormalization
    (c u X Y A : ℝ) (h k : ℕ) : ℝ :=
  A * Real.exp (2 * u ^ 2) *
    ((h : ℝ) / X) ^ ((1 / 2 : ℝ) + c) *
    ((k : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)

theorem hughesYoungScaledDFINormalization_pos
    {c X Y A : ℝ} {h k : ℕ}
    (hX : 0 < X) (hY : 0 < Y)
    (hA : 0 < A) (hh : 0 < h) (hk : 0 < k) (u : ℝ) :
    0 < hughesYoungScaledDFINormalization c u X Y A h k := by
  unfold hughesYoungScaledDFINormalization
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  exact mul_pos
    (mul_pos
      (mul_pos hA (Real.exp_pos _))
      (Real.rpow_pos_of_pos (div_pos hhR hX) _))
    (Real.rpow_pos_of_pos (div_pos hkR hY) _)

noncomputable def hughesYoungScaledNormalizedDFICore
    (T c u X Y A : ℝ) (h k : ℕ) (r : ℤ) : ℝ → ℝ → ℂ :=
  dfiComplexScaleWeight
    (((hughesYoungScaledDFINormalization c u X Y A h k : ℝ) : ℂ)⁻¹)
    (hughesYoungDFICore T c u X Y h k r)

theorem hughesYoungDFICore_eq_scaledNormalization_mul_normalized
    {c X Y A : ℝ} {h k : ℕ}
    (hX : 0 < X) (hY : 0 < Y)
    (hA : 0 < A) (hh : 0 < h) (hk : 0 < k)
    (T u : ℝ) (r : ℤ) :
    hughesYoungDFICore T c u X Y h k r =
      dfiComplexScaleWeight
        ((hughesYoungScaledDFINormalization c u X Y A h k : ℝ) : ℂ)
        (hughesYoungScaledNormalizedDFICore T c u X Y A h k r) := by
  funext x y
  unfold hughesYoungScaledNormalizedDFICore dfiComplexScaleWeight
  have hS : 0 < hughesYoungScaledDFINormalization c u X Y A h k :=
    hughesYoungScaledDFINormalization_pos
      (c := c) hX hY hA hh hk u
  field_simp [hS.ne']

theorem support_uncurry_hughesYoungScaledNormalizedDFICore_subset
    {T c u X Y A : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (r : ℤ) :
    Function.support (Function.uncurry
      (hughesYoungScaledNormalizedDFICore T c u X Y A h k r)) ⊆
        Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
  intro p hp
  apply support_uncurry_hughesYoungDFICore_subset
    (T := T) (c := c) (u := u) hX hY h k r
  intro hz
  change hughesYoungDFICore T c u X Y h k r p.1 p.2 = 0 at hz
  apply hp
  unfold hughesYoungScaledNormalizedDFICore dfiComplexScaleWeight
    Function.uncurry
  simp [hz]

theorem hughesYoungScaledNormalizedDFICore_localizedBox
    {T c u X Y A : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (r : ℤ) :
    DFILocalizedBox
      (hughesYoungScaledNormalizedDFICore T c u X Y A h k r) X Y :=
  ⟨support_uncurry_hughesYoungScaledNormalizedDFICore_subset hX hY h k r⟩

/-- After dividing by both the Gaussian ordinate envelope and the true
dyadic box size, the DFI derivative profile is universal. -/
theorem abs_pow_mul_abs_pow_mul_norm_dfiMixedDeriv_hughesYoungScaledNormalizedDFICore_le
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (Z : ℝ), 0 < Z → ∀ z : ℝ,
      |z| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt Z) z‖ ≤ Ccut n)
    {T c u X Y x y P A : ℝ} {h k : ℕ} {r : ℤ} (i j : ℕ)
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 0 < X) (hxLower : X ≤ x)
    (hY : 0 < Y) (hyLower : Y ≤ y) (hyUpper : y ≤ 2 * Y)
    (hh : 0 < h) (hk : 0 < k)
    (hr : |(r : ℝ)| ≤ Y / 2) (hP : 1 ≤ P)
    (hTR : T * (|(r : ℝ)| / Y) ≤ P) (hA : 0 < A)
    (hheight : ∀ (n : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ n * A)) :
    |x| ^ i * |y| ^ j *
        ‖dfiMixedDeriv i j
          (hughesYoungScaledNormalizedDFICore T c u X Y A h k r) x y‖ ≤
      hughesYoungGaussianOneFactorProfile Ccut i *
        hughesYoungGaussianCoreYProfile Ccut j * P ^ (i + j) := by
  let S : ℝ := hughesYoungScaledDFINormalization c u X Y A h k
  have hS : 0 < S := hughesYoungScaledDFINormalization_pos
    hX hY hA hh hk u
  have hrStrict : |(r : ℝ)| < Y := by linarith
  have hsmooth := contDiff_uncurry_hughesYoungDFICore
    (lt_of_lt_of_le zero_lt_one hT) hc u hX hY hh hk r hrStrict
  have hraw :=
    abs_pow_mul_abs_pow_mul_norm_dfiMixedDeriv_hughesYoungDFICore_scale_le
      Ccut hcut i j hT hc hc1 hX hxLower hY hyLower hyUpper
      hh hk hr hP hTR hA.le hheight
  have hxGauss := hughesYoungOneFactorDerivativeProfile_le_gaussian
    Ccut (fun n => (hcut n).1) u i
  have hyGauss := hughesYoungCoreYDerivativeProfile_le_gaussian
    Ccut (fun n => (hcut n).1) u j
  have hprofiles :
      hughesYoungOneFactorDerivativeProfile Ccut u i *
          hughesYoungCoreYDerivativeProfile Ccut u j ≤
        hughesYoungGaussianOneFactorProfile Ccut i *
          hughesYoungGaussianCoreYProfile Ccut j * Real.exp (2 * u ^ 2) := by
    calc
      hughesYoungOneFactorDerivativeProfile Ccut u i *
          hughesYoungCoreYDerivativeProfile Ccut u j ≤
        (hughesYoungGaussianOneFactorProfile Ccut i * Real.exp (u ^ 2)) *
          (hughesYoungGaussianCoreYProfile Ccut j * Real.exp (u ^ 2)) := by
            exact mul_le_mul hxGauss hyGauss
              (hughesYoungCoreYDerivativeProfile_pos Ccut
                (fun n => (hcut n).1) u j).le
              (mul_nonneg
                (hughesYoungGaussianOneFactorProfile_pos Ccut
                  (fun n => (hcut n).1) i).le
                (Real.exp_pos _).le)
      _ = hughesYoungGaussianOneFactorProfile Ccut i *
          hughesYoungGaussianCoreYProfile Ccut j * Real.exp (2 * u ^ 2) := by
            rw [show 2 * u ^ 2 = u ^ 2 + u ^ 2 by ring, Real.exp_add]
            ring
  change |x| ^ i * |y| ^ j *
      ‖dfiMixedDeriv i j
        (dfiComplexScaleWeight (((S : ℝ) : ℂ)⁻¹)
          (hughesYoungDFICore T c u X Y h k r)) x y‖ ≤ _
  rw [dfiMixedDeriv_scale hsmooth, norm_mul]
  have hnormS : ‖((S : ℂ)⁻¹)‖ = S⁻¹ := by
    rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos hS]
  rw [hnormS]
  calc
    |x| ^ i * |y| ^ j *
        (S⁻¹ * ‖dfiMixedDeriv i j
          (hughesYoungDFICore T c u X Y h k r) x y‖) =
      S⁻¹ * (|x| ^ i * |y| ^ j *
        ‖dfiMixedDeriv i j
          (hughesYoungDFICore T c u X Y h k r) x y‖) := by ring
    _ ≤ S⁻¹ *
        (hughesYoungOneFactorDerivativeProfile Ccut u i *
          hughesYoungCoreYDerivativeProfile Ccut u j *
          (((h : ℝ) / X) ^ ((1 / 2 : ℝ) + c) *
            ((k : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)) * A * P ^ (i + j)) := by
      exact mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hS.le)
    _ ≤ S⁻¹ *
        ((hughesYoungGaussianOneFactorProfile Ccut i *
          hughesYoungGaussianCoreYProfile Ccut j * Real.exp (2 * u ^ 2)) *
          (((h : ℝ) / X) ^ ((1 / 2 : ℝ) + c) *
            ((k : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)) * A * P ^ (i + j)) := by
      gcongr
    _ = hughesYoungGaussianOneFactorProfile Ccut i *
        hughesYoungGaussianCoreYProfile Ccut j * P ^ (i + j) := by
      dsimp only [S, hughesYoungScaledDFINormalization]
      have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
      have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
      have hxScale : 0 < ((h : ℝ) / X) ^ ((1 / 2 : ℝ) + c) :=
        Real.rpow_pos_of_pos (div_pos hhR hX) _
      have hyScale : 0 < ((k : ℝ) / Y) ^ ((1 / 2 : ℝ) + c) :=
        Real.rpow_pos_of_pos (div_pos hkR hY) _
      field_simp [hA.ne', (Real.exp_pos (2 * u ^ 2)).ne',
        hxScale.ne', hyScale.ne']

theorem hughesYoungScaledNormalizedDFICore_equation2
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (Z : ℝ), 0 < Z → ∀ z : ℝ,
      |z| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt Z) z‖ ≤ Ccut n)
    {T c u X Y P A : ℝ} {h k : ℕ} {r : ℤ}
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hh : 0 < h) (hhUpper : (h : ℝ) ≤ 2 * X)
    (hk : 0 < k) (hkUpper : (k : ℝ) ≤ 2 * Y)
    (hr : |(r : ℝ)| ≤ Y / 2) (hP : 1 ≤ P)
    (hTR : T * (|(r : ℝ)| / Y) ≤ P) (hA : 0 < A)
    (hheight : ∀ (n : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ n * A)) :
    DFIEquation2
      (hughesYoungScaledNormalizedDFICore T c u X Y A h k r) P X Y := by
  exact (hughesYoungDFICore_equation2 Ccut hcut hT hc hc1 hX hY
    hh hhUpper hk hkUpper hr hP hTR hA hheight).scale
      (((hughesYoungScaledDFINormalization c u X Y A h k : ℝ) : ℂ)⁻¹)

theorem hughesYoungScaledNormalizedDFICore_equation2Profile
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (Z : ℝ), 0 < Z → ∀ z : ℝ,
      |z| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt Z) z‖ ≤ Ccut n)
    {T c u X Y P A : ℝ} {h k : ℕ} {r : ℤ}
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hh : 0 < h) (hhUpper : (h : ℝ) ≤ 2 * X)
    (hk : 0 < k) (hkUpper : (k : ℝ) ≤ 2 * Y)
    (hr : |(r : ℝ)| ≤ Y / 2) (hP : 1 ≤ P)
    (hTR : T * (|(r : ℝ)| / Y) ≤ P) (hA : 0 < A)
    (hheight : ∀ (n : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ n * A)) :
    DFIEquation2Profile
      (hughesYoungScaledNormalizedDFICore T c u X Y A h k r) P X Y
      (hughesYoungUniformDFIProfile Ccut) := by
  refine ⟨fun i j => hughesYoungUniformDFIProfile_pos Ccut
    (fun n => (hcut n).1) i j, ?_⟩
  intro i j x y hx hy
  by_cases hd : dfiMixedDeriv i j
      (hughesYoungScaledNormalizedDFICore T c u X Y A h k r) x y = 0
  · rw [hd, norm_zero, mul_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (hughesYoungUniformDFIProfile_pos Ccut
            (fun n => (hcut n).1) i j).le
          (inv_nonneg.mpr (le_of_lt
            (show 0 < 1 + x / X by positivity))))
        (inv_nonneg.mpr (le_of_lt
          (show 0 < 1 + y / Y by positivity))))
      (pow_nonneg (zero_le_one.trans hP) _)
  · have heq2 := hughesYoungScaledNormalizedDFICore_equation2 Ccut hcut
      hT hc hc1 hX hY hh hhUpper hk hkUpper hr hP hTR hA hheight
    have hmem : (x, y) ∈ Function.support
        (Function.uncurry (dfiMixedDeriv i j
          (hughesYoungScaledNormalizedDFICore T c u X Y A h k r))) := by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hd
    have htsupport : tsupport (Function.uncurry
        (hughesYoungScaledNormalizedDFICore T c u X Y A h k r)) ⊆
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
      closure_minimal
        (support_uncurry_hughesYoungScaledNormalizedDFICore_subset
          (lt_of_lt_of_le zero_lt_one hX)
          (lt_of_lt_of_le zero_lt_one hY) h k r)
        (isClosed_Icc.prod isClosed_Icc)
    have hxy := htsupport
      (support_dfiMixedDeriv_subset_tsupport heq2.smooth i j hmem)
    have hraw :=
      abs_pow_mul_abs_pow_mul_norm_dfiMixedDeriv_hughesYoungScaledNormalizedDFICore_le
        Ccut hcut i j hT hc hc1
        (lt_of_lt_of_le zero_lt_one hX) hxy.1.1
        (lt_of_lt_of_le zero_lt_one hY) hxy.2.1 hxy.2.2
        hh hk hr hP hTR hA hheight
    have hxDenPos : 0 < 1 + x / X := by positivity
    have hyDenPos : 0 < 1 + y / Y := by positivity
    have hxInv : (3 : ℝ)⁻¹ ≤ (1 + x / X)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hxDenPos
        (by
          have := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hX)).2 hxy.1.2
          linarith : 1 + x / X ≤ 3)
    have hyInv : (3 : ℝ)⁻¹ ≤ (1 + y / Y)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hyDenPos
        (by
          have := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hY)).2 hxy.2.2
          linarith : 1 + y / Y ≤ 3)
    have hprofileNonneg :
        0 ≤ hughesYoungUniformDFIProfile Ccut i j :=
      (hughesYoungUniformDFIProfile_pos Ccut
        (fun n => (hcut n).1) i j).le
    calc
      |x| ^ i * |y| ^ j *
          ‖dfiMixedDeriv i j
            (hughesYoungScaledNormalizedDFICore T c u X Y A h k r) x y‖ ≤
        hughesYoungGaussianOneFactorProfile Ccut i *
          hughesYoungGaussianCoreYProfile Ccut j * P ^ (i + j) := hraw
      _ = hughesYoungUniformDFIProfile Ccut i j *
          (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ * P ^ (i + j) := by
        unfold hughesYoungUniformDFIProfile
        ring
      _ ≤ hughesYoungUniformDFIProfile Ccut i j *
          (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j) := by
        gcongr

/-! ## Uniform DFI error with the dyadic scale retained -/

theorem exists_uniform_norm_hughesYoungScaledNormalizedDFICore_dfiError
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U Q : ℝ} {h k : ℕ} {r : ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y →
      0 < h → (h : ℝ) ≤ 2 * X →
      0 < k → (k : ℝ) ≤ 2 * Y →
      |(r : ℝ)| ≤ Y / 2 → 1 ≤ P →
      T * (|(r : ℝ)| / Y) ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b M N : ℕ), 0 < a → 0 < b → r ≠ 0 → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y →
      (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) →
      (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y) →
      ‖dfiDyadicShiftedDivisorSum
          (hughesYoungScaledNormalizedDFICore T c u X Y A h k r)
          a b M N r -
        dfiSignedCentralSeries a b r
          (hughesYoungScaledNormalizedDFICore T c u X Y A h k r)‖ ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  obtain ⟨Ccut, hCcut⟩ :=
    exists_uniform_hughesYoungDyadicCutoffAt_derivativeProfile
  obtain ⟨Cφ, hCφ⟩ := exists_dfiUniformRedundantCutoff_profile
  obtain ⟨Cw, hCw⟩ := exists_dfiUniformDeltaWeight_profile
  obtain ⟨E, hE⟩ := exists_dfiUniformDeltaWeight_quotient_profile
  obtain ⟨C, hC, hBound⟩ :=
    exists_uniform_norm_dfiDyadicShiftedDivisorSum_sub_signedCentralSeries_le_theorem1ErrorScale
      Cw E (hughesYoungUniformDFIProfile Ccut)
        (fun i j => hughesYoungUniformDFIProfile Ccut j i)
        Cφ Cw ε hε0 hε4
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U Q h k r hT hc hc1 hX hY hh hhX hk hkY
    hr hP hTR hA hheight hscale hQ hU hQsq a b M N ha hb hr0 hab
    hM hN haX hbY hrPos hrNeg
  have hf := hughesYoungScaledNormalizedDFICore_equation2 Ccut hCcut
    hT hc hc1 hX hY hh hhX hk hkY hr hP hTR hA hheight
  have hfC := hughesYoungScaledNormalizedDFICore_equation2Profile Ccut hCcut
    hT hc hc1 hX hY hh hhX hk hkY hr hP hTR hA hheight
  have hbox := hughesYoungScaledNormalizedDFICore_localizedBox
    (T := T) (c := c) (u := u) (A := A) (X := X) (Y := Y)
    (lt_of_lt_of_le zero_lt_one hX)
    (lt_of_lt_of_le zero_lt_one hY) h k r
  have hU0 : 0 < U := by rw [hU]; positivity
  let φ : ℝ → ℂ := dfiUniformRedundantCutoff U
  let hφ : DFIRedundantCutoff φ U := dfiUniformRedundantCutoff_spec U hU0
  let w : DFIDeltaWeight Q := dfiUniformDeltaWeight Q hQ
  exact hBound hf hfC hbox hf.swap (hfC.swap hf) hbox.swap hφ
    (hCφ U hU0) hscale (hCw Q hQ) (hCw Q hQ) (hE Q hQ)
    (by linarith) hU hQsq a b M N r ha hb hr0 hab hM hN haX hbY
    hrPos hrNeg

/-- Literal equation-(70) cleaned weight with the dyadically summable DFI
error. The universal constant is independent of every Hughes--Young
parameter, including the Mellin ordinate and both dyadic scales. -/
theorem exists_uniform_norm_hughesYoungCleanedShiftWeight_scaled_dfiError
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U Q : ℝ} {h k : ℕ} {r : ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y →
      0 < h → (h : ℝ) ≤ 2 * X →
      0 < k → (k : ℝ) ≤ 2 * Y →
      |(r : ℝ)| ≤ Y / 2 → 1 ≤ P →
      T * (|(r : ℝ)| / Y) ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b M N : ℕ), 0 < a → 0 < b → r ≠ 0 → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y →
      (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) →
      (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y) →
      ‖dfiDyadicShiftedDivisorSum
          (hughesYoungCleanedShiftWeight T c u X Y h k r)
          a b M N r -
        dfiSignedCentralSeries a b r
          (hughesYoungCleanedShiftWeight T c u X Y h k r)‖ ≤
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          hughesYoungScaledDFINormalization c u X Y A h k *
          (C * dfiTheorem1ErrorScale P X Y ε) := by
  obtain ⟨C, hC, hBound⟩ :=
    exists_uniform_norm_hughesYoungScaledNormalizedDFICore_dfiError
      ε hε0 hε4
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U Q h k r hT hc hc1 hX hY hh hhX hk hkY
    hr hP hTR hA hheight hscale hQ hU hQsq a b M N ha hb hr0 hab
    hM hN haX hbY hrPos hrNeg
  let S : ℝ := hughesYoungScaledDFINormalization c u X Y A h k
  let z : ℂ := hughesYoungLocalizedStaticScalar T h k * (S : ℂ)
  have hS : 0 < S := hughesYoungScaledDFINormalization_pos
    (c := c) (lt_of_lt_of_le zero_lt_one hX)
    (lt_of_lt_of_le zero_lt_one hY) hA hh hk u
  have hnormalized := hBound hT hc hc1 hX hY hh hhX hk hkY hr hP
    hTR hA hheight hscale hQ hU hQsq a b M N ha hb hr0 hab hM hN
    haX hbY hrPos hrNeg
  have hweight :
      hughesYoungCleanedShiftWeight T c u X Y h k r =
        dfiComplexScaleWeight z
          (hughesYoungScaledNormalizedDFICore T c u X Y A h k r) := by
    funext x y
    rw [hughesYoungCleanedShiftWeight_eq_staticScalar_mul_dfiCore]
    rw [hughesYoungDFICore_eq_scaledNormalization_mul_normalized
      (lt_of_lt_of_le zero_lt_one hX)
      (lt_of_lt_of_le zero_lt_one hY) hA hh hk T u r]
    unfold dfiComplexScaleWeight
    dsimp only [z, S]
    ring
  rw [hweight]
  have hscaled := norm_dfiSignedDiscrepancy_scale_le z
    (hughesYoungScaledNormalizedDFICore T c u X Y A h k r)
    a b M N r hnormalized
  have hnormz : ‖z‖ =
      ‖hughesYoungLocalizedStaticScalar T h k‖ * S := by
    dsimp only [z]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hS]
  rw [hnormz] at hscaled
  exact hscaled

/-! ## Finite near-shift assembly -/

/-- Summing uniformly bounded discrepancies costs exactly the number of
shifts.  This elementary finite lemma is kept explicit because it is the
place where the pointwise DFI error becomes the error for one Hughes--Young
dyadic box. -/
theorem norm_sum_sub_sum_le_card_mul_of_uniform_norm_sub_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (F G : ι → ℂ) {B : ℝ}
    (hbound : ∀ r ∈ s, ‖F r - G r‖ ≤ B) :
    ‖(∑ r ∈ s, F r) - ∑ r ∈ s, G r‖ ≤ (s.card : ℝ) * B := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ r ∈ s, (F r - G r)‖ ≤ ∑ r ∈ s, ‖F r - G r‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _r ∈ s, B := by
      exact Finset.sum_le_sum fun r hr => hbound r hr
    _ = (s.card : ℝ) * B := by simp

/-- Uniform DFI discrepancy for an arbitrary finite family of near shifts
in one literal Hughes--Young dyadic box.  Unlike the pointwise theorem, this
is already in the finite-sum form consumed by the off-diagonal expansion.
All source range conditions remain visible and are checked shift by shift. -/
theorem exists_uniform_norm_sum_hughesYoungCleanedShiftWeight_dfiDiscrepancy
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U Q : ℝ} {h k : ℕ} {s : Finset ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y →
      0 < h → (h : ℝ) ≤ 2 * X →
      0 < k → (k : ℝ) ≤ 2 * Y →
      1 ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b M N : ℕ), 0 < a → 0 < b → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y →
      (∀ r ∈ s,
        r ≠ 0 ∧
        |(r : ℝ)| ≤ Y / 2 ∧
        T * (|(r : ℝ)| / Y) ≤ P ∧
        (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
        (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y)) →
      ‖(∑ r ∈ s,
          dfiDyadicShiftedDivisorSum
            (hughesYoungCleanedShiftWeight T c u X Y h k r)
            a b M N r) -
        ∑ r ∈ s,
          dfiSignedCentralSeries a b r
            (hughesYoungCleanedShiftWeight T c u X Y h k r)‖ ≤
        (s.card : ℝ) *
          (‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization c u X Y A h k *
            (C * dfiTheorem1ErrorScale P X Y ε)) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_uniform_norm_hughesYoungCleanedShiftWeight_scaled_dfiError
      ε hε0 hε4
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U Q h k s hT hc hc1 hX hY hh hhX hk hkY
    hP hA hheight hscale hQ hU hQsq a b M N ha hb hab hM hN haX hbY
    hs
  apply norm_sum_sub_sum_le_card_mul_of_uniform_norm_sub_le
    s
    (fun r => dfiDyadicShiftedDivisorSum
      (hughesYoungCleanedShiftWeight T c u X Y h k r) a b M N r)
    (fun r => dfiSignedCentralSeries a b r
      (hughesYoungCleanedShiftWeight T c u X Y h k r))
  intro r hr
  obtain ⟨hr0, hrY, hrP, hrPos, hrNeg⟩ := hs r hr
  exact hpoint hT hc hc1 hX hY hh hhX hk hkY hrY hP hrP hA
    hheight hscale hQ hU hQsq a b M N ha hb hr0 hab hM hN haX hbY
    hrPos hrNeg

/-! ## The Ramanujan central series in a Hughes--Young box -/

/-- The complete equation-(27) series is bounded by the sum of the norms
of its literal summands. -/
theorem norm_dfiEquation27CentralSeries_le_tsum_norm
    (a b r : ℕ) (f : ℝ → ℝ → ℂ)
    (hs : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r f q)) :
    ‖dfiEquation27CentralSeries a b r f‖ ≤
      ∑' q : ℕ, ‖dfiEquation27CentralSummand a b r f q‖ := by
  exact norm_tsum_le_tsum_norm hs.norm

/-- The explicit arithmetic-logarithmic scale of the complete DFI
equation-(27) central series for one orientation of a box. -/
noncomputable def hughesYoungCentralArithmeticScale
    (X Y : ℝ) (a b r : ℕ) : ℝ :=
  (((a * b : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
    (r.divisors.card : ℝ) *
    (1 + Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 32) *
    (1 + Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 32) *
    min X Y * 5

theorem hughesYoungCentralArithmeticScale_nonneg
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (a b r : ℕ) :
    0 ≤ hughesYoungCentralArithmeticScale X Y a b r := by
  have hlogX : 0 ≤ Real.log (2 * X) :=
    Real.log_nonneg (by nlinarith)
  have hlogY : 0 ≤ Real.log (2 * Y) :=
    Real.log_nonneg (by nlinarith)
  unfold hughesYoungCentralArithmeticScale
  positivity

/-- Source-uniform bound for the entire positive-shift DFI central series.
It is obtained from the interpolated equation-(27) estimate with
`rho=1/2`, `alpha=beta=1/8`, `theta=1/4`, and `K=0`. -/
theorem norm_dfiEquation27CentralSeries_le_hughesYoungCentralArithmeticScale
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y)
    (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ‖dfiEquation27CentralSeries a b r f‖ ≤
      dfiEquation27CentralProfileConstant Cf Cφ *
        hughesYoungCentralArithmeticScale X Y a b r := by
  have hs : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r
        (dfiLocalizedWeight f φ r) q) :=
    summable_dfiEquation27CentralSummand hf hfC hbox hφ hφC hscale
      a b r ha hb hr
  have htail :=
    tsum_norm_dfiEquation27CentralSummand_tail_le_interpolated_of_profiles
      hf hfC hbox hφ hφC hscale
      (1 / 2 : ℝ) (1 / 8 : ℝ) (1 / 4 : ℝ) (1 / 8 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      a b r 0 ha hb hr
  have htotal :
      (∑' q : ℕ, ‖dfiEquation27CentralSummand a b r
        (dfiLocalizedWeight f φ r) q‖) =
      ∑' j : ℕ, ‖dfiEquation27CentralSummand a b r
        (dfiLocalizedWeight f φ r) (j + 1)‖ := by
    have hsplit := hs.norm.sum_add_tsum_nat_add 1
    simpa [dfiEquation27CentralSummand,
      dfiEquation27ArithmeticCoefficient, add_comm] using hsplit.symm
  rw [← dfiEquation27CentralSeries_localizedWeight_eq hφ a b r]
  calc
    ‖dfiEquation27CentralSeries a b r
        (dfiLocalizedWeight f φ r)‖ ≤
      ∑' q : ℕ, ‖dfiEquation27CentralSummand a b r
        (dfiLocalizedWeight f φ r) q‖ :=
      norm_dfiEquation27CentralSeries_le_tsum_norm _ _ _ _ hs
    _ = ∑' j : ℕ, ‖dfiEquation27CentralSummand a b r
        (dfiLocalizedWeight f φ r) (j + 1)‖ := htotal
    _ ≤ dfiEquation27CentralProfileConstant Cf Cφ *
        hughesYoungCentralArithmeticScale X Y a b r := by
      unfold hughesYoungCentralArithmeticScale
      convert htail using 1
      all_goals norm_num
      all_goals ring

set_option maxHeartbeats 4000000 in
/-- Signed-shift central-series bound for the normalized literal
Hughes--Young equation-(70) weight.  The second arithmetic scale is the
exact coordinate-swapped contribution required for a negative shift. -/
theorem exists_uniform_norm_hughesYoungScaledNormalizedDFICore_signedCentralSeries
    : ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U : ℝ} {h k a b : ℕ} {r : ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y →
      0 < h → (h : ℝ) ≤ 2 * X →
      0 < k → (k : ℝ) ≤ 2 * Y →
      r ≠ 0 → |(r : ℝ)| ≤ Y / 2 →
      1 ≤ P → T * (|(r : ℝ)| / Y) ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      0 < U → U ≤ P⁻¹ * min X Y →
      0 < a → 0 < b →
      ‖dfiSignedCentralSeries a b r
          (hughesYoungScaledNormalizedDFICore
            T c u X Y A h k r)‖ ≤
        C * (hughesYoungCentralArithmeticScale X Y a b r.natAbs +
          hughesYoungCentralArithmeticScale Y X b a r.natAbs) := by
  obtain ⟨Ccut, hCcut⟩ :=
    exists_uniform_hughesYoungDyadicCutoffAt_derivativeProfile
  obtain ⟨Cφ, hCφ⟩ := exists_dfiUniformRedundantCutoff_profile
  let C : ℝ := dfiEquation27CentralProfileConstant
    (hughesYoungUniformDFIProfile Ccut) Cφ
  have hC : 0 < C := by
    have hsource : 0 < dfiEquation27SourceDerivativeConstant
        (hughesYoungUniformDFIProfile Ccut) Cφ 0 := by
      simpa [dfiEquation27SourceDerivativeConstant,
        dfiEquation2FiniteConstant, dfiCutoffFiniteConstant] using
        mul_pos
          (hughesYoungUniformDFIProfile_pos Ccut
            (fun n => (hCcut n).1) 0 0)
          ((hCφ 1 zero_lt_one).positive 0)
    dsimp only [C, dfiEquation27CentralProfileConstant]
    exact mul_pos hsource (dfiEquation27LogLeibnizConstant_pos 0)
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U h k a b r hT hc hc1 hX hY hh hhX hk hkY
    hr0 hrY hP hTR hA hheight hU hscale ha hb
  let f : ℝ → ℝ → ℂ :=
    hughesYoungScaledNormalizedDFICore T c u X Y A h k r
  have hf : DFIEquation2 f P X Y := by
    dsimp only [f]
    exact hughesYoungScaledNormalizedDFICore_equation2 Ccut hCcut
      hT hc hc1 hX hY hh hhX hk hkY hrY hP hTR hA hheight
  have hfC : DFIEquation2Profile f P X Y
      (hughesYoungUniformDFIProfile Ccut) := by
    dsimp only [f]
    exact hughesYoungScaledNormalizedDFICore_equation2Profile Ccut hCcut
      hT hc hc1 hX hY hh hhX hk hkY hrY hP hTR hA hheight
  have hbox : DFILocalizedBox f X Y := by
    dsimp only [f]
    exact hughesYoungScaledNormalizedDFICore_localizedBox
      (T := T) (c := c) (u := u) (A := A) (X := X) (Y := Y)
      (lt_of_lt_of_le zero_lt_one hX)
      (lt_of_lt_of_le zero_lt_one hY) h k r
  let φ : ℝ → ℂ := dfiUniformRedundantCutoff U
  let hφ : DFIRedundantCutoff φ U := dfiUniformRedundantCutoff_spec U hU
  have hφC : DFIRedundantCutoffProfile hφ Cφ := hCφ U hU
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        by_contra hn0
        have : n = 0 := Nat.eq_zero_of_not_pos hn0
        exact hr0 (by simp [this])
      change ‖dfiSignedCentralSeries a b (n : ℤ) f‖ ≤
        C * (hughesYoungCentralArithmeticScale X Y a b n +
          hughesYoungCentralArithmeticScale Y X b a n)
      rw [dfiSignedCentralSeries_ofNat]
      have hmain :=
        norm_dfiEquation27CentralSeries_le_hughesYoungCentralArithmeticScale
          hf hfC hbox hφ hφC hscale a b n ha hb hn
      calc
        ‖dfiEquation27CentralSeries a b n f‖ ≤
            C * hughesYoungCentralArithmeticScale X Y a b n := by
          simpa only [C] using hmain
        _ ≤ C * (hughesYoungCentralArithmeticScale X Y a b n +
            hughesYoungCentralArithmeticScale Y X b a n) := by
          exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right
              (hughesYoungCentralArithmeticScale_nonneg hY hX b a n))
            hC.le
  | negSucc n =>
      let q : ℕ := n + 1
      have hq : 0 < q := by dsimp [q]; omega
      have hscaleSwap : U ≤ P⁻¹ * min Y X := by
        simpa [min_comm] using hscale
      have hmain :=
        norm_dfiEquation27CentralSeries_le_hughesYoungCentralArithmeticScale
          hf.swap (hfC.swap hf) hbox.swap hφ hφC hscaleSwap
          b a q hb ha hq
      change ‖dfiEquation27CentralSeries b a q (dfiSwapWeight f)‖ ≤ _
      calc
        ‖dfiEquation27CentralSeries b a q (dfiSwapWeight f)‖ ≤
            C * hughesYoungCentralArithmeticScale Y X b a q := by
          simpa only [C] using hmain
        _ ≤ C * (hughesYoungCentralArithmeticScale X Y a b q +
            hughesYoungCentralArithmeticScale Y X b a q) := by
          exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left
              (hughesYoungCentralArithmeticScale_nonneg hX hY a b q))
            hC.le

/-- Signed DFI central-series bound for the literal Hughes--Young
equation-(70) weight.  This theorem restores both the static localization
factor and the full dyadic normalization, so no physical scale is hidden in
the universal central-series constant. -/
theorem exists_uniform_norm_hughesYoungCleanedShiftWeight_signedCentralSeries
    : ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U : ℝ} {h k a b : ℕ} {r : ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y →
      0 < h → (h : ℝ) ≤ 2 * X →
      0 < k → (k : ℝ) ≤ 2 * Y →
      r ≠ 0 → |(r : ℝ)| ≤ Y / 2 →
      1 ≤ P → T * (|(r : ℝ)| / Y) ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      0 < U → U ≤ P⁻¹ * min X Y →
      0 < a → 0 < b →
      ‖dfiSignedCentralSeries a b r
          (hughesYoungCleanedShiftWeight T c u X Y h k r)‖ ≤
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          hughesYoungScaledDFINormalization c u X Y A h k *
          (C * (hughesYoungCentralArithmeticScale X Y a b r.natAbs +
            hughesYoungCentralArithmeticScale Y X b a r.natAbs)) := by
  obtain ⟨C, hC, hBound⟩ :=
    exists_uniform_norm_hughesYoungScaledNormalizedDFICore_signedCentralSeries
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U h k a b r hT hc hc1 hX hY hh hhX hk hkY
    hr0 hrY hP hTR hA hheight hU hscale ha hb
  let S : ℝ := hughesYoungScaledDFINormalization c u X Y A h k
  let z : ℂ := hughesYoungLocalizedStaticScalar T h k * (S : ℂ)
  have hS : 0 < S := hughesYoungScaledDFINormalization_pos
    (c := c) (lt_of_lt_of_le zero_lt_one hX)
    (lt_of_lt_of_le zero_lt_one hY) hA hh hk u
  have hnormalized := hBound hT hc hc1 hX hY hh hhX hk hkY hr0 hrY
    hP hTR hA hheight hU hscale ha hb
  have hweight :
      hughesYoungCleanedShiftWeight T c u X Y h k r =
        dfiComplexScaleWeight z
          (hughesYoungScaledNormalizedDFICore T c u X Y A h k r) := by
    funext x y
    rw [hughesYoungCleanedShiftWeight_eq_staticScalar_mul_dfiCore]
    rw [hughesYoungDFICore_eq_scaledNormalization_mul_normalized
      (lt_of_lt_of_le zero_lt_one hX)
      (lt_of_lt_of_le zero_lt_one hY) hA hh hk T u r]
    unfold dfiComplexScaleWeight
    dsimp only [z, S]
    ring
  rw [hweight, dfiSignedCentralSeries_scale, norm_mul]
  have hnormz : ‖z‖ =
      ‖hughesYoungLocalizedStaticScalar T h k‖ * S := by
    dsimp only [z]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hS]
  rw [hnormz]
  exact mul_le_mul_of_nonneg_left hnormalized
    (mul_nonneg (norm_nonneg _) hS.le)

/-- Complete one-shift Hughes--Young use of DFI Theorem 1: the literal
shifted-divisor sum is bounded by the published DFI error together with the
entire equation-(27) Ramanujan central series.  This is the first theorem in
the consumer chain whose left side is the actual dyadic arithmetic sum and
whose right side contains no assumed main term. -/
theorem exists_uniform_norm_hughesYoungCleanedShiftWeight_full_dfi
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U Q : ℝ} {h k : ℕ} {r : ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y →
      0 < h → (h : ℝ) ≤ 2 * X →
      0 < k → (k : ℝ) ≤ 2 * Y →
      |(r : ℝ)| ≤ Y / 2 → 1 ≤ P →
      T * (|(r : ℝ)| / Y) ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b M N : ℕ), 0 < a → 0 < b → r ≠ 0 → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y →
      (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) →
      (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y) →
      ‖dfiDyadicShiftedDivisorSum
          (hughesYoungCleanedShiftWeight T c u X Y h k r)
          a b M N r‖ ≤
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          hughesYoungScaledDFINormalization c u X Y A h k *
          (C * (dfiTheorem1ErrorScale P X Y ε +
            hughesYoungCentralArithmeticScale X Y a b r.natAbs +
            hughesYoungCentralArithmeticScale Y X b a r.natAbs)) := by
  obtain ⟨Ce, hCe, hError⟩ :=
    exists_uniform_norm_hughesYoungCleanedShiftWeight_scaled_dfiError
      ε hε0 hε4
  obtain ⟨Cm, hCm, hMain⟩ :=
    exists_uniform_norm_hughesYoungCleanedShiftWeight_signedCentralSeries
  let C : ℝ := Ce + Cm
  have hC : 0 < C := add_pos hCe hCm
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U Q h k r hT hc hc1 hX hY hh hhX hk hkY
    hrY hP hTR hA hheight hscale hQ hU hQsq a b M N ha hb hr0 hab
    hM hN haX hbY hrPos hrNeg
  let D : ℂ := dfiDyadicShiftedDivisorSum
    (hughesYoungCleanedShiftWeight T c u X Y h k r) a b M N r
  let M0 : ℂ := dfiSignedCentralSeries a b r
    (hughesYoungCleanedShiftWeight T c u X Y h k r)
  let S : ℝ := hughesYoungScaledDFINormalization c u X Y A h k
  let E : ℝ := dfiTheorem1ErrorScale P X Y ε
  let R : ℝ := hughesYoungCentralArithmeticScale X Y a b r.natAbs +
    hughesYoungCentralArithmeticScale Y X b a r.natAbs
  have hU0 : 0 < U := by rw [hU]; positivity
  have hDisc : ‖D - M0‖ ≤
      ‖hughesYoungLocalizedStaticScalar T h k‖ * S * (Ce * E) := by
    dsimp only [D, M0, S, E]
    exact hError hT hc hc1 hX hY hh hhX hk hkY hrY hP hTR hA
      hheight hscale hQ hU hQsq a b M N ha hb hr0 hab hM hN haX
      hbY hrPos hrNeg
  have hCentral : ‖M0‖ ≤
      ‖hughesYoungLocalizedStaticScalar T h k‖ * S * (Cm * R) := by
    dsimp only [M0, S, R]
    exact hMain hT hc hc1 hX hY hh hhX hk hkY hr0 hrY hP hTR hA
      hheight hU0 hscale ha hb
  have hE : 0 ≤ E := by
    dsimp only [E, dfiTheorem1ErrorScale]
    positivity
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg
      (hughesYoungCentralArithmeticScale_nonneg hX hY a b r.natAbs)
      (hughesYoungCentralArithmeticScale_nonneg hY hX b a r.natAbs)
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    exact (hughesYoungScaledDFINormalization_pos
      (c := c) (lt_of_lt_of_le zero_lt_one hX)
      (lt_of_lt_of_le zero_lt_one hY) hA hh hk u).le
  have hp : 0 ≤ ‖hughesYoungLocalizedStaticScalar T h k‖ * S :=
    mul_nonneg (norm_nonneg _) hS0
  have hCeC : Ce ≤ C := le_add_of_nonneg_right hCm.le
  have hCmC : Cm ≤ C := le_add_of_nonneg_left hCe.le
  have hNorm : ‖D‖ ≤ ‖D - M0‖ + ‖M0‖ := by
    have h := norm_add_le (D - M0) M0
    simpa only [sub_add_cancel] using h
  calc
    ‖D‖ ≤ ‖D - M0‖ + ‖M0‖ := hNorm
    _ ≤ ‖hughesYoungLocalizedStaticScalar T h k‖ * S * (Ce * E) +
        ‖hughesYoungLocalizedStaticScalar T h k‖ * S * (Cm * R) :=
      add_le_add hDisc hCentral
    _ ≤ ‖hughesYoungLocalizedStaticScalar T h k‖ * S * (C * E) +
        ‖hughesYoungLocalizedStaticScalar T h k‖ * S * (C * R) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hCeC hE) hp)
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hCmC hR) hp)
    _ = ‖hughesYoungLocalizedStaticScalar T h k‖ * S *
        (C * (E + R)) := by ring
    _ = ‖hughesYoungLocalizedStaticScalar T h k‖ *
        hughesYoungScaledDFINormalization c u X Y A h k *
        (C * (dfiTheorem1ErrorScale P X Y ε +
          hughesYoungCentralArithmeticScale X Y a b r.natAbs +
          hughesYoungCentralArithmeticScale Y X b a r.natAbs)) := by
      dsimp only [S, E, R]
      ring

/-- Complete DFI bound summed over an arbitrary finite family of admissible
near shifts in one literal Hughes--Young box.  The shift-dependent divisor
and logarithmic factors are retained inside the finite sum, ready for the
subsequent elementary shift summation rather than absorbed into an implicit
constant. -/
theorem exists_uniform_norm_sum_hughesYoungCleanedShiftWeight_full_dfi
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U Q : ℝ} {h k : ℕ} {s : Finset ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y →
      0 < h → (h : ℝ) ≤ 2 * X →
      0 < k → (k : ℝ) ≤ 2 * Y →
      1 ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b M N : ℕ), 0 < a → 0 < b → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y →
      (∀ r ∈ s,
        r ≠ 0 ∧
        |(r : ℝ)| ≤ Y / 2 ∧
        T * (|(r : ℝ)| / Y) ≤ P ∧
        (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
        (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y)) →
      ‖∑ r ∈ s,
          dfiDyadicShiftedDivisorSum
            (hughesYoungCleanedShiftWeight T c u X Y h k r)
            a b M N r‖ ≤
        ∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization c u X Y A h k *
            (C * (dfiTheorem1ErrorScale P X Y ε +
              hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs)) := by
  obtain ⟨C, hC, hBound⟩ :=
    exists_uniform_norm_hughesYoungCleanedShiftWeight_full_dfi
      ε hε0 hε4
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U Q h k s hT hc hc1 hX hY hh hhX hk hkY
    hP hA hheight hscale hQ hU hQsq a b M N ha hb hab hM hN haX
    hbY hs
  calc
    ‖∑ r ∈ s,
        dfiDyadicShiftedDivisorSum
          (hughesYoungCleanedShiftWeight T c u X Y h k r)
          a b M N r‖ ≤
        ∑ r ∈ s,
          ‖dfiDyadicShiftedDivisorSum
            (hughesYoungCleanedShiftWeight T c u X Y h k r)
            a b M N r‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ r ∈ s,
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          hughesYoungScaledDFINormalization c u X Y A h k *
          (C * (dfiTheorem1ErrorScale P X Y ε +
            hughesYoungCentralArithmeticScale X Y a b r.natAbs +
            hughesYoungCentralArithmeticScale Y X b a r.natAbs)) := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨hr0, hrY, hrP, hrPos, hrNeg⟩ := hs r hr
      exact hBound hT hc hc1 hX hY hh hhX hk hkY hrY hP hrP hA
        hheight hscale hQ hU hQsq a b M N ha hb hr0 hab hM hN haX
        hbY hrPos hrNeg

/-- Uniform bound for the whole positive-shift Ramanujan central series of
the scale-normalized Hughes--Young weight.  This is the `K = 0` instance of
the source-sharp equation-(27) tail estimate; the modulus-zero summand is
identically zero.  The displayed arithmetic and logarithmic factors are
therefore genuine source dependence, not hidden inside the constant. -/
theorem exists_uniform_norm_hughesYoungScaledNormalizedDFICore_centralSeries
    : ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U : ℝ} {h k a b r : ℕ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y →
      0 < h → (h : ℝ) ≤ 2 * X →
      0 < k → (k : ℝ) ≤ 2 * Y →
      0 < r → (r : ℝ) ≤ Y / 2 →
      1 ≤ P → T * ((r : ℝ) / Y) ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      0 < U → U ≤ P⁻¹ * min X Y →
      0 < a → 0 < b →
      ‖dfiEquation27CentralSeries a b r
          (hughesYoungScaledNormalizedDFICore
            T c u X Y A h k (r : ℤ))‖ ≤
        C *
          (((a * b : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
          (r.divisors.card : ℝ) *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 32) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 32) *
          min X Y * 5 := by
  obtain ⟨Ccut, hCcut⟩ :=
    exists_uniform_hughesYoungDyadicCutoffAt_derivativeProfile
  obtain ⟨Cφ, hCφ⟩ := exists_dfiUniformRedundantCutoff_profile
  let C : ℝ := dfiEquation27CentralProfileConstant
    (hughesYoungUniformDFIProfile Ccut) Cφ
  have hC : 0 < C := by
    have hsource : 0 < dfiEquation27SourceDerivativeConstant
        (hughesYoungUniformDFIProfile Ccut) Cφ 0 := by
      simpa [dfiEquation27SourceDerivativeConstant,
        dfiEquation2FiniteConstant, dfiCutoffFiniteConstant] using
        mul_pos
          (hughesYoungUniformDFIProfile_pos Ccut
            (fun n => (hCcut n).1) 0 0)
          ((hCφ 1 zero_lt_one).positive 0)
    dsimp only [C, dfiEquation27CentralProfileConstant]
    exact mul_pos hsource (dfiEquation27LogLeibnizConstant_pos 0)
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U h k a b r hT hc hc1 hX hY hh hhX hk hkY
    hr hrY hP hTR hA hheight hU hscale ha hb
  let f : ℝ → ℝ → ℂ :=
    hughesYoungScaledNormalizedDFICore T c u X Y A h k (r : ℤ)
  have hf : DFIEquation2 f P X Y := by
    dsimp only [f]
    exact hughesYoungScaledNormalizedDFICore_equation2 Ccut hCcut
      hT hc hc1 hX hY hh hhX hk hkY (by simpa using hrY) hP
      (by
        rw [Int.cast_natCast,
          abs_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) by positivity)]
        exact hTR) hA hheight
  have hfC : DFIEquation2Profile f P X Y
      (hughesYoungUniformDFIProfile Ccut) := by
    dsimp only [f]
    exact hughesYoungScaledNormalizedDFICore_equation2Profile Ccut hCcut
      hT hc hc1 hX hY hh hhX hk hkY (by simpa using hrY) hP
      (by
        rw [Int.cast_natCast,
          abs_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) by positivity)]
        exact hTR) hA hheight
  have hbox : DFILocalizedBox f X Y := by
    dsimp only [f]
    exact hughesYoungScaledNormalizedDFICore_localizedBox
      (T := T) (c := c) (u := u) (A := A) (X := X) (Y := Y)
      (lt_of_lt_of_le zero_lt_one hX)
      (lt_of_lt_of_le zero_lt_one hY) h k (r : ℤ)
  let φ : ℝ → ℂ := dfiUniformRedundantCutoff U
  let hφ : DFIRedundantCutoff φ U := dfiUniformRedundantCutoff_spec U hU
  have hφC : DFIRedundantCutoffProfile hφ Cφ := hCφ U hU
  have hs : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r
        (dfiLocalizedWeight f φ r) q) :=
    summable_dfiEquation27CentralSummand hf hfC hbox hφ hφC hscale
      a b r ha hb hr
  have htail :=
    tsum_norm_dfiEquation27CentralSummand_tail_le_interpolated_of_profiles
      hf hfC hbox hφ hφC hscale
      (1 / 2 : ℝ) (1 / 8 : ℝ) (1 / 4 : ℝ) (1 / 8 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      a b r 0 ha hb hr
  have htotal :
      (∑' q : ℕ, ‖dfiEquation27CentralSummand a b r
        (dfiLocalizedWeight f φ r) q‖) =
      ∑' j : ℕ, ‖dfiEquation27CentralSummand a b r
        (dfiLocalizedWeight f φ r) (0 + (j + 1))‖ := by
    have hsplit := hs.norm.sum_add_tsum_nat_add 1
    simpa [dfiEquation27CentralSummand,
      dfiEquation27ArithmeticCoefficient, add_comm] using hsplit.symm
  rw [← dfiEquation27CentralSeries_localizedWeight_eq hφ a b r]
  calc
    ‖dfiEquation27CentralSeries a b r
        (dfiLocalizedWeight f φ r)‖ ≤
      ∑' q : ℕ, ‖dfiEquation27CentralSummand a b r
        (dfiLocalizedWeight f φ r) q‖ :=
      norm_dfiEquation27CentralSeries_le_tsum_norm _ _ _ _ hs
    _ = ∑' j : ℕ, ‖dfiEquation27CentralSummand a b r
        (dfiLocalizedWeight f φ r) (0 + (j + 1))‖ := htotal
    _ ≤ C *
          (((a * b : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
          (r.divisors.card : ℝ) *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 32) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 32) *
          min X Y * 5 := by
      dsimp only [C]
      convert htail using 1
      all_goals norm_num

end RiemannZeta.GuthMaynard
