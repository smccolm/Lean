import RiemannZeta.GuthMaynard.DFIEquation27
import RiemannZeta.GuthMaynard.DFIEquation30
import RiemannZeta.GuthMaynard.HughesYoungLogBeta
import RiemannZeta.GuthMaynard.HughesYoungActiveDyadic
import RiemannZeta.GuthMaynard.HughesYoungGCD
import RiemannZeta.GuthMaynard.HughesYoungInfiniteDyadic

open Complex MeasureTheory Set
open scoped ContDiff

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young equations (81)--(84): the DFI central integral

This module keeps the two logarithmic factors from DFI equation (27) while
performing the positive-shift translation and dilation used in
Hughes--Young equations (81)--(84).
-/

/-! ## The concrete reduced Hughes--Young Mellin amplitude -/

/-- The factor left after extracting the two physical powers from the
gcd-reduced Hughes--Young Mellin weight.  This constant retains the original
mollifier indices in `hughesYoungMellinScalar`, while the two exponential
factors record the coprime DFI coefficients. -/
noncomputable def hughesYoungReducedMellinScaleConstant
    (T t c u : ℝ) (h k : ℕ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let s₁ : ℂ := afeCriticalPoint t + w
  let s₂ : ℂ := afeCriticalPoint (-t) + w
  hughesYoungMellinScalar T t c u h k *
    Complex.exp (s₁ * (Real.log (hughesYoungReducedLeft h k : ℝ) : ℂ)) *
    Complex.exp (s₂ * (Real.log (hughesYoungReducedRight h k : ℝ) : ℂ))

/-- Dividing a positive physical variable by a positive natural scale can
be pulled out of the logarithmic power exactly. -/
theorem hughesYoungLogPower_div_nat
    {x : ℝ} (hx : 0 < x) {a : ℕ} (ha : 0 < a) (s : ℂ) :
    hughesYoungLogPower s (x / a) =
      Complex.exp (s * (Real.log (a : ℝ) : ℂ)) * (x : ℂ) ^ (-s) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  unfold hughesYoungLogPower
  rw [Real.log_div hx.ne' haR.ne']
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact factorization of the actual coprime-coordinate source summand on
the positive quadrant.  Unlike the generic equation-(83) consumer, this
theorem exposes both source dyadic cutoffs; they must be summed by the
partition of unity before the beta integral is applied. -/
theorem hughesYoungReducedLocalizedMellinWeight_eq_scaled_powers
    (T t c u X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hughesYoungReducedLocalizedMellinWeight T t c u X Y h k x y =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        (hughesYoungDyadicCutoffAt X x : ℂ) *
        (hughesYoungDyadicCutoffAt Y y : ℂ) *
        (x : ℂ) ^ (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))) *
        (y : ℂ) ^ (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I))) := by
  have ha : 0 < hughesYoungReducedLeft h k :=
    hughesYoungReducedLeft_pos hh
  have hb : 0 < hughesYoungReducedRight h k :=
    hughesYoungReducedRight_pos hh hk
  unfold hughesYoungReducedLocalizedMellinWeight
    hughesYoungLocalizedLogKernel hughesYoungReducedMellinScaleConstant
  dsimp only
  rw [hughesYoungLogPower_div_nat hx ha,
    hughesYoungLogPower_div_nat hy hb]
  ring

/-- The actual gcd-reduced Mellin weight in one member of the complete
Hughes--Young dyadic partition. -/
noncomputable def hughesYoungFullDyadicReducedMellinWeight
    (T t c u : ℝ) (h k i j : ℕ) (x y : ℝ) : ℂ :=
  hughesYoungReducedLocalizedMellinWeight T t c u
    (hughesYoungFullDyadicScale i) (hughesYoungFullDyadicScale j)
    h k x y

/-- Exact reassembly of all source dyadic Mellin weights on the positive
quadrant.  The two explicit factors are the genuine lower-end correction;
they become one on the physical divisor range `x,y ≥ 1`. -/
theorem tsum_hughesYoungFullDyadicReducedMellinWeight_eq
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∑' i : ℕ, ∑' j : ℕ,
      hughesYoungFullDyadicReducedMellinWeight T t c u h k i j x y) =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        ((1 - hughesYoungDyadicStep
          (x * hughesYoungDyadicRatio) : ℝ) : ℂ) *
        ((1 - hughesYoungDyadicStep
          (y * hughesYoungDyadicRatio) : ℝ) : ℂ) *
        (x : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (y : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) := by
  have hleft :=
    tsum_hughesYoungFullDyadicCutoff_cast_eq_one_sub_step x
  have hright :=
    tsum_hughesYoungFullDyadicCutoff_cast_eq_one_sub_step y
  change (∑' i : ℕ, (hughesYoungDyadicCutoffAt
    (hughesYoungFullDyadicScale i) x : ℂ)) = _ at hleft
  change (∑' j : ℕ, (hughesYoungDyadicCutoffAt
    (hughesYoungFullDyadicScale j) y : ℂ)) = _ at hright
  calc
    (∑' i : ℕ, ∑' j : ℕ,
        hughesYoungFullDyadicReducedMellinWeight
          T t c u h k i j x y) =
        ∑' i : ℕ, ∑' j : ℕ,
          (hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale i) x : ℂ) *
          (hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale j) y : ℂ) *
          (hughesYoungReducedMellinScaleConstant T t c u h k *
            (x : ℂ) ^ (-(afeCriticalPoint t +
              ((c : ℂ) + (u : ℂ) * I))) *
            (y : ℂ) ^ (-(afeCriticalPoint (-t) +
              ((c : ℂ) + (u : ℂ) * I)))) := by
      apply tsum_congr
      intro i
      apply tsum_congr
      intro j
      rw [hughesYoungFullDyadicReducedMellinWeight,
        hughesYoungReducedLocalizedMellinWeight_eq_scaled_powers
          T t c u _ _ hh hk hx hy]
      ring
    _ = (∑' i : ℕ, (hughesYoungDyadicCutoffAt
          (hughesYoungFullDyadicScale i) x : ℂ)) *
        ((∑' j : ℕ, (hughesYoungDyadicCutoffAt
          (hughesYoungFullDyadicScale j) y : ℂ)) *
          (hughesYoungReducedMellinScaleConstant T t c u h k *
            (x : ℂ) ^ (-(afeCriticalPoint t +
              ((c : ℂ) + (u : ℂ) * I))) *
            (y : ℂ) ^ (-(afeCriticalPoint (-t) +
              ((c : ℂ) + (u : ℂ) * I))))) := by
      simp_rw [tsum_mul_right, tsum_mul_left]
      rw [tsum_mul_right]
      rw [mul_assoc]
    _ = _ := by
      rw [hleft, hright]
      ring

/-- On the physical positive-integer range the lower-end corrections vanish,
so the full source partition reassembles to the pure Mellin monomial needed
by Hughes--Young equation (83). -/
theorem tsum_hughesYoungFullDyadicReducedMellinWeight_eq_pure
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (∑' i : ℕ, ∑' j : ℕ,
      hughesYoungFullDyadicReducedMellinWeight T t c u h k i j x y) =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        (x : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (y : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) := by
  rw [tsum_hughesYoungFullDyadicReducedMellinWeight_eq
    T t c u hh hk (zero_lt_one.trans_le hx) (zero_lt_one.trans_le hy)]
  rw [hughesYoungDyadicStep_eq_zero, hughesYoungDyadicStep_eq_zero]
  · norm_num
  · exact le_mul_of_one_le_left hughesYoungDyadicRatio_pos.le hy
  · exact le_mul_of_one_le_left hughesYoungDyadicRatio_pos.le hx

/-- Exact finite-depth reassembly of the concrete reduced Mellin weight.
Both terminal smooth cutoffs and both lower-end corrections remain visible,
so this identity can be integrated and summed without an infinite-series
interchange. -/
theorem sum_range_hughesYoungFullDyadicReducedMellinWeight_eq
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (K : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∑ i ∈ Finset.range (K + 2), ∑ j ∈ Finset.range (K + 2),
      hughesYoungFullDyadicReducedMellinWeight T t c u h k i j x y) =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        ((hughesYoungDyadicStep
            (x / hughesYoungDyadicRatio ^ (K + 1)) -
          hughesYoungDyadicStep
            (x * hughesYoungDyadicRatio) : ℝ) : ℂ) *
        ((hughesYoungDyadicStep
            (y / hughesYoungDyadicRatio ^ (K + 1)) -
          hughesYoungDyadicStep
            (y * hughesYoungDyadicRatio) : ℝ) : ℂ) *
        (x : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (y : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) := by
  have hleft := sum_range_hughesYoungFullDyadicCutoff_cast_eq K x
  have hright := sum_range_hughesYoungFullDyadicCutoff_cast_eq K y
  change (∑ i ∈ Finset.range (K + 2),
    (hughesYoungDyadicCutoffAt
      (hughesYoungFullDyadicScale i) x : ℂ)) = _ at hleft
  change (∑ j ∈ Finset.range (K + 2),
    (hughesYoungDyadicCutoffAt
      (hughesYoungFullDyadicScale j) y : ℂ)) = _ at hright
  calc
    (∑ i ∈ Finset.range (K + 2), ∑ j ∈ Finset.range (K + 2),
        hughesYoungFullDyadicReducedMellinWeight
          T t c u h k i j x y) =
        ∑ i ∈ Finset.range (K + 2), ∑ j ∈ Finset.range (K + 2),
          (hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale i) x : ℂ) *
          (hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale j) y : ℂ) *
          (hughesYoungReducedMellinScaleConstant T t c u h k *
            (x : ℂ) ^ (-(afeCriticalPoint t +
              ((c : ℂ) + (u : ℂ) * I))) *
            (y : ℂ) ^ (-(afeCriticalPoint (-t) +
              ((c : ℂ) + (u : ℂ) * I)))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hughesYoungFullDyadicReducedMellinWeight,
        hughesYoungReducedLocalizedMellinWeight_eq_scaled_powers
          T t c u _ _ hh hk hx hy]
      ring
    _ = (∑ i ∈ Finset.range (K + 2),
          (hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale i) x : ℂ)) *
        ((∑ j ∈ Finset.range (K + 2),
          (hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale j) y : ℂ)) *
          (hughesYoungReducedMellinScaleConstant T t c u h k *
            (x : ℂ) ^ (-(afeCriticalPoint t +
              ((c : ℂ) + (u : ℂ) * I))) *
            (y : ℂ) ^ (-(afeCriticalPoint (-t) +
              ((c : ℂ) + (u : ℂ) * I))))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = _ := by
      rw [hleft, hright]
      ring

/-- On the actual covered physical divisor range, the finite source family
reassembles to the pure Mellin monomial.  This is the finite, integration-safe
replacement for using the infinite partition inside DFI equation (27). -/
theorem sum_range_hughesYoungFullDyadicReducedMellinWeight_eq_pure
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {K : ℕ} {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxUpper : x ≤ hughesYoungDyadicRatio ^ (K + 1))
    (hyUpper : y ≤ hughesYoungDyadicRatio ^ (K + 1)) :
    (∑ i ∈ Finset.range (K + 2), ∑ j ∈ Finset.range (K + 2),
      hughesYoungFullDyadicReducedMellinWeight T t c u h k i j x y) =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        (x : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (y : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  rw [sum_range_hughesYoungFullDyadicReducedMellinWeight_eq
    T t c u hh hk K hx0 hy0]
  rw [hughesYoungDyadicStep_eq_one,
    hughesYoungDyadicStep_eq_zero,
    hughesYoungDyadicStep_eq_one,
    hughesYoungDyadicStep_eq_zero]
  · norm_num
  · exact le_mul_of_one_le_left hughesYoungDyadicRatio_pos.le hy
  · exact (div_le_one (pow_pos hughesYoungDyadicRatio_pos _)).2 hyUpper
  · exact le_mul_of_one_le_left hughesYoungDyadicRatio_pos.le hx
  · exact (div_le_one (pow_pos hughesYoungDyadicRatio_pos _)).2 hxUpper

/-! ## Finite linearity of the literal DFI central integral -/

set_option maxHeartbeats 4000000 in
/-- The equation-(27) coefficient is integrable on every affine central
slice of a genuine reduced Hughes--Young dyadic Mellin weight.  This is the
missing analytic hypothesis needed to move a *finite* dyadic sum through
the Bochner integral; no infinite-series interchange is used here. -/
theorem integrable_dfiEquation27C_reducedLocalizedMellinWeight_centralSlice
    (T t c u : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy : ℕ) (r : ℝ) :
    Integrable (fun x : ℝ =>
      dfiEquation27C a b qx qy
        (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)
        x (x - r)) := by
  let F : ℝ × ℝ → ℂ := Function.uncurry
    (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)
  let cx : ℂ := -Complex.log (a : ℂ) +
    2 * Real.eulerMascheroniConstant - 2 * Complex.log (qx : ℂ)
  let cy : ℂ := -Complex.log (b : ℂ) +
    2 * Real.eulerMascheroniConstant - 2 * Complex.log (qy : ℂ)
  have hFsmooth : ContDiff ℝ ∞ F := by
    exact contDiff_uncurry_hughesYoungReducedLocalizedMellinWeight
      T t c u hX hY hh hk
  have hFsupp : Function.support F ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    exact support_uncurry_hughesYoungReducedLocalizedMellinWeight_subset
      T t c u hX hY h k
  have hFfst : Function.support F ⊆ Set.Ici X ×ˢ Set.univ := by
    intro p hp
    exact ⟨(hFsupp hp).1.1, Set.mem_univ _⟩
  let G : ℝ × ℝ → ℂ := fun p => ((Real.log p.1 : ℂ) + cx) * F p
  have hGsmooth : ContDiff ℝ ∞ G := by
    exact contDiff_log_fst_add_const_mul_of_support_pos
      hX cx hFsmooth hFfst
  have hGsupp : Function.support G ⊆ Set.univ ×ˢ Set.Ici Y := by
    intro p hp
    have hpF : F p ≠ 0 := by
      intro hzero
      exact hp (by simp [G, hzero])
    exact ⟨Set.mem_univ _, (hFsupp hpF).2.1⟩
  have hCsmooth : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation27C a b qx qy
        (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k))) := by
    have hfinal := contDiff_log_snd_add_const_mul_of_support_pos
      hY cy hGsmooth hGsupp
    convert hfinal using 1
    funext p
    simp only [Function.uncurry, dfiEquation27C, dfiEquation27LogFactor,
      F, G, cx, cy]
    ring
  have hsliceSmooth : Continuous (fun x : ℝ =>
      dfiEquation27C a b qx qy
        (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)
        x (x - r)) := by
    exact (hCsmooth.comp (by
      fun_prop : ContDiff ℝ ∞ (fun x : ℝ => (x, x - r)))).continuous
  have hsliceSupport : Function.support (fun x : ℝ =>
      dfiEquation27C a b qx qy
        (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)
        x (x - r)) ⊆ Set.Icc X (2 * X) := by
    intro x hx
    have hweight :
        hughesYoungReducedLocalizedMellinWeight T t c u X Y h k x (x - r) ≠ 0 := by
      intro hzero
      apply hx
      change dfiEquation27LogFactor a qx x *
          dfiEquation27LogFactor b qy (x - r) *
            hughesYoungReducedLocalizedMellinWeight
              T t c u X Y h k x (x - r) = 0
      simp only [hzero, mul_zero]
    have hweightF : F (x, x - r) ≠ 0 := by
      simpa only [F, Function.uncurry_apply_pair] using hweight
    exact (hFsupp hweightF).1
  exact hsliceSmooth.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsliceSupport)

/-- Finite additivity for the literal DFI central integral.  The explicit
integrability premise prevents the false use of Bochner-integral linearity
outside its domain. -/
theorem dfiEquation27CentralIntegral_finsetSum
    {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℂ)
    (a b qx qy : ℕ) (r : ℝ)
    (hF : ∀ i ∈ s, Integrable (fun x : ℝ =>
      dfiEquation27C a b qx qy (F i) x (x - r))) :
    dfiEquation27CentralIntegral a b qx qy
        (fun x y => ∑ i ∈ s, F i x y) r =
      ∑ i ∈ s, dfiEquation27CentralIntegral a b qx qy (F i) r := by
  unfold dfiEquation27CentralIntegral
  rw [show (fun x : ℝ =>
      dfiEquation27C a b qx qy (fun x y => ∑ i ∈ s, F i x y)
        x (x - r)) =
      fun x : ℝ => ∑ i ∈ s,
        dfiEquation27C a b qx qy (F i) x (x - r) by
    funext x
    simp only [dfiEquation27C, Finset.mul_sum]]
  exact MeasureTheory.integral_finsetSum s hF

/-- The finite rectangular Hughes--Young family can be moved through the
literal equation-(27) central integral exactly. -/
theorem dfiEquation27CentralIntegral_fullDyadic_finsetSum
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy : ℕ) (r : ℝ) (K : ℕ) :
    dfiEquation27CentralIntegral a b qx qy
        (fun x y => ∑ i ∈ Finset.range (K + 2),
          ∑ j ∈ Finset.range (K + 2),
            hughesYoungFullDyadicReducedMellinWeight
              T t c u h k i j x y) r =
      ∑ i ∈ Finset.range (K + 2),
        ∑ j ∈ Finset.range (K + 2),
          dfiEquation27CentralIntegral a b qx qy
            (hughesYoungFullDyadicReducedMellinWeight
              T t c u h k i j) r := by
  let S := Finset.range (K + 2)
  have hterm : ∀ i ∈ S, ∀ j ∈ S, Integrable (fun x : ℝ =>
      dfiEquation27C a b qx qy
        (hughesYoungFullDyadicReducedMellinWeight T t c u h k i j)
        x (x - r)) := by
    intro i _hi j _hj
    exact integrable_dfiEquation27C_reducedLocalizedMellinWeight_centralSlice
      T t c u (hughesYoungFullDyadicScale_pos i)
        (hughesYoungFullDyadicScale_pos j) hh hk a b qx qy r
  have hinner (i : ℕ) (hi : i ∈ S) :
      Integrable (fun x : ℝ => ∑ j ∈ S,
        dfiEquation27C a b qx qy
          (hughesYoungFullDyadicReducedMellinWeight T t c u h k i j)
          x (x - r)) :=
    integrable_finsetSum S (fun j hj => hterm i hi j hj)
  rw [dfiEquation27CentralIntegral_finsetSum S
    (fun i x y => ∑ j ∈ S,
      hughesYoungFullDyadicReducedMellinWeight T t c u h k i j x y)
    a b qx qy r]
  · apply Finset.sum_congr rfl
    intro i hi
    exact dfiEquation27CentralIntegral_finsetSum S
      (fun j => hughesYoungFullDyadicReducedMellinWeight
        T t c u h k i j) a b qx qy r (hterm i hi)
  · intro i hi
    simpa only [dfiEquation27C, Finset.mul_sum] using hinner i hi

/-- The source's physically active dyadic boxes can be moved through the
literal equation-(27) central integral.  This is the filtered family used by
the Hughes--Young consumer, rather than the larger rectangular cutoff. -/
theorem dfiEquation27CentralIntegral_activeDyadic_finsetSum
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy : ℕ) (r : ℝ) (R K : ℕ) :
    dfiEquation27CentralIntegral a b qx qy
        (fun x y => ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
          hughesYoungFullDyadicReducedMellinWeight
            T t c u h k ij.1 ij.2 x y) r =
      ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
        dfiEquation27CentralIntegral a b qx qy
          (hughesYoungFullDyadicReducedMellinWeight
            T t c u h k ij.1 ij.2) r := by
  apply dfiEquation27CentralIntegral_finsetSum
  intro ij _hij
  exact integrable_dfiEquation27C_reducedLocalizedMellinWeight_centralSlice
    T t c u (hughesYoungFullDyadicScale_pos ij.1)
      (hughesYoungFullDyadicScale_pos ij.2) hh hk a b qx qy r

/-- Finite additivity for one literal equation-(27) modulus summand. -/
theorem dfiEquation27CentralSummand_finsetSum
    {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℂ)
    (a b h q : ℕ)
    (hF : ∀ i ∈ s, Integrable (fun x : ℝ =>
      dfiEquation27C a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (F i) x (x - h))) :
    dfiEquation27CentralSummand a b h
        (fun x y => ∑ i ∈ s, F i x y) q =
      ∑ i ∈ s, dfiEquation27CentralSummand a b h (F i) q := by
  unfold dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_finsetSum s F a b
    (dfiReducedDenominator a q) (dfiReducedDenominator b q) h hF]
  rw [Finset.mul_sum]

/-- Absolute summability lets a finite family pass through the literal
Ramanujan series without discarding its cancellation. -/
theorem dfiEquation27CentralSeries_finsetSum
    {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℂ)
    (a b h : ℕ)
    (hsum : ∀ i ∈ s, Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b h (F i) q))
    (hF : ∀ q i, i ∈ s → Integrable (fun x : ℝ =>
      dfiEquation27C a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (F i) x (x - h))) :
    dfiEquation27CentralSeries a b h
        (fun x y => ∑ i ∈ s, F i x y) =
      ∑ i ∈ s, dfiEquation27CentralSeries a b h (F i) := by
  unfold dfiEquation27CentralSeries
  rw [show (fun q : ℕ =>
      dfiEquation27CentralSummand a b h
        (fun x y => ∑ i ∈ s, F i x y) q) =
      fun q : ℕ => ∑ i ∈ s,
        dfiEquation27CentralSummand a b h (F i) q by
    funext q
    exact dfiEquation27CentralSummand_finsetSum s F a b h q
      (fun i hi => hF q i hi)]
  exact Summable.tsum_finsetSum hsum

set_option maxHeartbeats 800000 in
/-- Every genuine (positive-index) Hughes--Young dyadic Mellin weight has an
absolutely summable DFI equation-(27) modulus series.  Index zero is
deliberately excluded: its physical scale is below one and belongs to the
separate boundary analysis, not to DFI equation (2). -/
theorem summable_dfiEquation27CentralSummand_fullDyadic
    (T t c u : ℝ) {h k i j a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hi : 0 < i) (hj : 0 < j)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r
        (hughesYoungFullDyadicReducedMellinWeight
          T t c u h k i j) q) := by
  let X : ℝ := hughesYoungFullDyadicScale i
  let Y : ℝ := hughesYoungFullDyadicScale j
  let f : ℝ → ℝ → ℂ :=
    hughesYoungFullDyadicReducedMellinWeight T t c u h k i j
  have hX : 1 ≤ X := by
    obtain ⟨i0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    exact one_le_hughesYoungDyadicScale i0
  have hY : 1 ≤ Y := by
    obtain ⟨j0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    exact one_le_hughesYoungDyadicScale j0
  have hf : DFIEquation2 f 1 X Y := by
    exact hughesYoungReducedLocalizedMellinWeight_equation2
      T t c u (by norm_num) hX hY hh hk
  have hbox : DFILocalizedBox f X Y := by
    exact ⟨support_uncurry_hughesYoungReducedLocalizedMellinWeight_subset
      T t c u (zero_lt_one.trans_le hX) (zero_lt_one.trans_le hY) h k⟩
  obtain ⟨Cf, hCf⟩ := hf.exists_profile
  obtain ⟨Cφ, hCφ⟩ := exists_dfiUniformRedundantCutoff_profile
  let φ : ℝ → ℂ := dfiUniformRedundantCutoff 1
  let hφ : DFIRedundantCutoff φ 1 :=
    dfiUniformRedundantCutoff_spec 1 zero_lt_one
  have hφC : DFIRedundantCutoffProfile hφ Cφ := hCφ 1 zero_lt_one
  have hscale : (1 : ℝ) ≤ (1 : ℝ)⁻¹ * min X Y := by
    simpa only [inv_one, one_mul] using le_min hX hY
  have hs := summable_dfiEquation27CentralSummand
    hf hCf hbox hφ hφC hscale a b r ha hb hr
  have hterm : ∀ q : ℕ,
      dfiEquation27CentralSummand a b r (dfiLocalizedWeight f φ r) q =
        dfiEquation27CentralSummand a b r f q := by
    intro q
    unfold dfiEquation27CentralSummand
    congr 1
    unfold dfiEquation27CentralIntegral
    apply integral_congr_ae
    filter_upwards with x
    unfold dfiEquation27C
    rw [dfiLocalizedWeight_eq_of_sub_eq hφ]
    ring
  simpa only [hterm] using hs

/-- A finite positive-index Hughes--Young family passes through the complete
DFI Ramanujan series exactly.  This is the cancellation-preserving dyadic
reassembly needed before equations (81)--(83). -/
theorem dfiEquation27CentralSeries_positiveDyadic_finsetSum
    (T t c u : ℝ) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (s : Finset (ℕ × ℕ))
    (hs : ∀ ij ∈ s, 0 < ij.1 ∧ 0 < ij.2) :
    dfiEquation27CentralSeries a b r
        (fun x y => ∑ ij ∈ s,
          hughesYoungFullDyadicReducedMellinWeight
            T t c u h k ij.1 ij.2 x y) =
      ∑ ij ∈ s, dfiEquation27CentralSeries a b r
        (hughesYoungFullDyadicReducedMellinWeight
          T t c u h k ij.1 ij.2) := by
  apply dfiEquation27CentralSeries_finsetSum
  · intro ij hij
    exact summable_dfiEquation27CentralSummand_fullDyadic
      T t c u hh hk (hs ij hij).1 (hs ij hij).2 ha hb hr
  · intro q ij hij
    exact integrable_dfiEquation27C_reducedLocalizedMellinWeight_centralSlice
      T t c u (hughesYoungFullDyadicScale_pos ij.1)
        (hughesYoungFullDyadicScale_pos ij.2) hh hk a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q) r

/-- Finite additivity for the complete signed DFI central series.  Both
branches retain the exact coordinate convention of `dfiSignedCentralSeries`;
in particular, the negative-shift branch swaps the weight before applying
equation (27).  This is the linearity theorem needed to reassemble signed
dyadic central terms before taking a norm. -/
theorem dfiSignedCentralSeries_finsetSum
    {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℂ)
    (a b : ℕ) (r : ℤ)
    (hsumPos : ∀ i ∈ s, Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r.toNat (F i) q))
    (hFPos : ∀ q i, i ∈ s → Integrable (fun x : ℝ =>
      dfiEquation27C a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (F i) x (x - r.toNat)))
    (hsumNeg : ∀ i ∈ s, Summable (fun q : ℕ =>
      dfiEquation27CentralSummand b a (-r).toNat (dfiSwapWeight (F i)) q))
    (hFNeg : ∀ q i, i ∈ s → Integrable (fun x : ℝ =>
      dfiEquation27C b a
        (dfiReducedDenominator b q) (dfiReducedDenominator a q)
        (dfiSwapWeight (F i)) x (x - (-r).toNat))) :
    dfiSignedCentralSeries a b r
        (fun x y => ∑ i ∈ s, F i x y) =
      ∑ i ∈ s, dfiSignedCentralSeries a b r (F i) := by
  by_cases hr : 0 ≤ r
  · simp only [dfiSignedCentralSeries, if_pos hr]
    exact dfiEquation27CentralSeries_finsetSum
      s F a b r.toNat hsumPos hFPos
  · simp only [dfiSignedCentralSeries, if_neg hr]
    rw [show dfiSwapWeight (fun x y => ∑ i ∈ s, F i x y) =
        fun x y => ∑ i ∈ s, dfiSwapWeight (F i) x y by
      funext x y
      simp only [dfiSwapWeight]]
    exact dfiEquation27CentralSeries_finsetSum
      s (fun i => dfiSwapWeight (F i)) b a (-r).toNat hsumNeg hFNeg

/-- The part of a DFI equation-(27) logarithmic factor which is independent
of its positive physical variable. -/
noncomputable def dfiEquation27LogConstant (a qred : ℕ) : ℂ :=
  -Complex.log (a : ℂ) + 2 * Real.eulerMascheroniConstant -
    2 * Complex.log (qred : ℂ)

theorem dfiEquation27LogFactor_eq_log_add_constant
    (a qred : ℕ) (x : ℝ) :
    dfiEquation27LogFactor a qred x =
      (Real.log x : ℂ) + dfiEquation27LogConstant a qred := by
  unfold dfiEquation27LogFactor dfiEquation27LogConstant
  ring

/-- Exact form of the two DFI logarithms after the source substitution
`x = r(1+u)`, `y = ru`. -/
theorem dfiEquation27LogFactors_dilate
    (a b qx qy : ℕ) {r u : ℝ} (hr : 0 < r) (hu : 0 < u) :
    dfiEquation27LogFactor a qx (r * (1 + u)) *
        dfiEquation27LogFactor b qy (r * u) =
      ((Real.log r : ℂ) + (Real.log (1 + u) : ℂ) +
          dfiEquation27LogConstant a qx) *
        ((Real.log r : ℂ) + (Real.log u : ℂ) +
          dfiEquation27LogConstant b qy) := by
  rw [dfiEquation27LogFactor_eq_log_add_constant,
    dfiEquation27LogFactor_eq_log_add_constant]
  rw [Real.log_mul hr.ne' (add_pos_of_nonneg_of_pos zero_le_one hu).ne',
    Real.log_mul hr.ne' hu.ne']
  push_cast
  rfl

/-- Hughes--Young equation (83) before evaluating the beta integral.  The
identity is the literal DFI logarithmic central kernel, including the
Jacobian and the exact power of the positive shift. -/
theorem hughesYoung_equation83_dfiLogKernel
    (a b qx qy : ℕ) {A B : ℂ} {r : ℝ} (hr : 0 < r) :
    (∫ y in Set.Ioi (0 : ℝ),
      dfiEquation27LogFactor a qx (y + r) *
        dfiEquation27LogFactor b qy y *
        (((y + r : ℝ) : ℂ) ^ B * (y : ℂ) ^ A)) =
      (r : ℂ) ^ (A + B + 1) *
        ∫ u in Set.Ioi (0 : ℝ),
          ((Real.log r : ℂ) + (Real.log (1 + u) : ℂ) +
              dfiEquation27LogConstant a qx) *
            ((Real.log r : ℂ) + (Real.log u : ℂ) +
              dfiEquation27LogConstant b qy) *
            ((1 + (u : ℂ)) ^ B * (u : ℂ) ^ A) := by
  rw [show (∫ y in Set.Ioi (0 : ℝ),
      dfiEquation27LogFactor a qx (y + r) *
        dfiEquation27LogFactor b qy y *
        (((y + r : ℝ) : ℂ) ^ B * (y : ℂ) ^ A)) =
      ∫ y in Set.Ioi (0 : ℝ),
        ((Real.log y : ℂ) + dfiEquation27LogConstant b qy) *
          ((Real.log (y + r) : ℂ) + dfiEquation27LogConstant a qx) *
          ((y : ℂ) ^ A * ((y + r : ℝ) : ℂ) ^ B) by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y _hy
    dsimp only
    rw [← dfiEquation27LogFactor_eq_log_add_constant,
      ← dfiEquation27LogFactor_eq_log_add_constant]
    ring]
  rw [hughesYoung_scaledLogBetaIntegral hr]
  apply congrArg ((r : ℂ) ^ (A + B + 1) * ·)
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _hu
  ring

/-- Translate the physical DFI central line `x-y=r` to the positive
Hughes--Young variable `y`.  The sole support premise says precisely that
the source weight vanishes when the translated divisor variable is not
positive. -/
theorem dfiEquation27CentralIntegral_eq_Ioi_shift
    (a b qx qy : ℕ) (F : ℝ → ℝ → ℂ) {r : ℝ}
    (hzero : ∀ y ≤ 0, F (y + r) y = 0) :
    dfiEquation27CentralIntegral a b qx qy F r =
      ∫ y in Set.Ioi (0 : ℝ),
        dfiEquation27C a b qx qy F (y + r) y := by
  let G : ℝ → ℂ := fun x => dfiEquation27C a b qx qy F x (x - r)
  have htranslate := MeasureTheory.integral_add_right_eq_self
    (μ := MeasureTheory.volume) G r
  have hpoint : (fun y : ℝ => G (y + r)) =
      fun y => dfiEquation27C a b qx qy F (y + r) y := by
    funext y
    dsimp only [G]
    congr 2
    ring
  rw [hpoint] at htranslate
  unfold dfiEquation27CentralIntegral
  change (∫ x : ℝ, G x) = _
  rw [← htranslate]
  symm
  apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hy0 : y ≤ 0 := le_of_not_gt hy
  unfold dfiEquation27C
  rw [hzero y hy0]
  simp

/-- Once the source amplitude on the positive shifted line is a pure Mellin
monomial, the literal DFI central integral is the logarithmic beta integral
of equation (83).  This is the reusable consumer needed after the dyadic
partition of unity is summed. -/
theorem dfiEquation27CentralIntegral_eq_equation83
    (a b qx qy : ℕ) {A B K : ℂ} {F : ℝ → ℝ → ℂ} {r : ℝ}
    (hr : 0 < r)
    (hzero : ∀ y ≤ 0, F (y + r) y = 0)
    (hpositive : ∀ y, 0 < y →
      F (y + r) y =
        K * (((y + r : ℝ) : ℂ) ^ B * (y : ℂ) ^ A)) :
    dfiEquation27CentralIntegral a b qx qy F r =
      K * (r : ℂ) ^ (A + B + 1) *
        ∫ u in Set.Ioi (0 : ℝ),
          ((Real.log r : ℂ) + (Real.log (1 + u) : ℂ) +
              dfiEquation27LogConstant a qx) *
            ((Real.log r : ℂ) + (Real.log u : ℂ) +
              dfiEquation27LogConstant b qy) *
            ((1 + (u : ℂ)) ^ B * (u : ℂ) ^ A) := by
  rw [dfiEquation27CentralIntegral_eq_Ioi_shift a b qx qy F hzero]
  have hrewrite : (∫ y in Set.Ioi (0 : ℝ),
      dfiEquation27C a b qx qy F (y + r) y) =
      K * ∫ y in Set.Ioi (0 : ℝ),
        dfiEquation27LogFactor a qx (y + r) *
          dfiEquation27LogFactor b qy y *
          (((y + r : ℝ) : ℂ) ^ B * (y : ℂ) ^ A) := by
    calc
      (∫ y in Set.Ioi (0 : ℝ),
          dfiEquation27C a b qx qy F (y + r) y) =
          ∫ y in Set.Ioi (0 : ℝ), K *
            (dfiEquation27LogFactor a qx (y + r) *
              dfiEquation27LogFactor b qy y *
              (((y + r : ℝ) : ℂ) ^ B * (y : ℂ) ^ A)) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        unfold dfiEquation27C
        dsimp only
        rw [hpositive y hy]
        ring
      _ = _ := MeasureTheory.integral_const_mul _ _
  rw [hrewrite]
  rw [hughesYoung_equation83_dfiLogKernel a b qx qy hr]
  ring

/-! ## Source specialization after dyadic reassembly -/

/-- The positive-quadrant Mellin monomial obtained after the Hughes--Young
dyadic partition has been reassembled.  The zero extension is explicit so
that the object is a total Lean function while its physical content remains
exactly the source integrand. -/
noncomputable def hughesYoungPureReducedMellinWeight
    (T t c u : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  if 0 < x ∧ 0 < y then
    hughesYoungReducedMellinScaleConstant T t c u h k *
      (x : ℂ) ^ (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))) *
      (y : ℂ) ^ (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))
  else 0

theorem hughesYoungPureReducedMellinWeight_of_pos
    (T t c u : ℝ) (h k : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hughesYoungPureReducedMellinWeight T t c u h k x y =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        (x : ℂ) ^ (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))) *
        (y : ℂ) ^ (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I))) := by
  simp [hughesYoungPureReducedMellinWeight, hx, hy]

theorem hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_right
    (T t c u : ℝ) (h k : ℕ) {x y : ℝ} (hy : y ≤ 0) :
    hughesYoungPureReducedMellinWeight T t c u h k x y = 0 := by
  simp [hughesYoungPureReducedMellinWeight, not_lt.mpr hy]

theorem hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_left
    (T t c u : ℝ) (h k : ℕ) {x y : ℝ} (hx : x ≤ 0) :
    hughesYoungPureReducedMellinWeight T t c u h k x y = 0 := by
  simp [hughesYoungPureReducedMellinWeight, not_lt.mpr hx]

/-- The exact DFI central integral of the reassembled positive-quadrant
source, in the logarithmic beta-integral form preceding Hughes--Young (84).
No dyadic cutoff or unproved exchange remains in this identity. -/
theorem dfiEquation27CentralIntegral_pureReduced_eq_equation83
    (T t c u : ℝ) {h k : ℕ} (a b qx qy : ℕ) {r : ℝ} (hr : 0 < r) :
    dfiEquation27CentralIntegral a b qx qy
        (hughesYoungPureReducedMellinWeight T t c u h k) r =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        (r : ℂ) ^
          (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) +
            -(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) + 1) *
        ∫ x in Set.Ioi (0 : ℝ),
          ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) +
              dfiEquation27LogConstant a qx) *
            ((Real.log r : ℂ) + (Real.log x : ℂ) +
              dfiEquation27LogConstant b qy) *
            ((1 + (x : ℂ)) ^
                (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))) *
              (x : ℂ) ^
                (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))) := by
  apply dfiEquation27CentralIntegral_eq_equation83 a b qx qy
      (A := -(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))
      (B := -(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)))
      (K := hughesYoungReducedMellinScaleConstant T t c u h k) hr
  · intro y hy
    apply hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_right
    exact hy
  · intro y hy
    rw [hughesYoungPureReducedMellinWeight_of_pos]
    · ring
    · linarith
    · exact hy

/-- Hughes--Young equation (83) for one DFI modulus after the dyadic
partition has been reassembled.  This theorem retains the complete DFI
arithmetic coefficient and both logarithmic factors; no norm or absolute
value has been introduced. -/
theorem dfiEquation27CentralSummand_pureReduced_eq_equation83
    (T t c u : ℝ) {h k : ℕ} (a b : ℕ) {r : ℕ} (hr : 0 < r) (q : ℕ) :
    dfiEquation27CentralSummand a b r
        (hughesYoungPureReducedMellinWeight T t c u h k) q =
      (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b r q) *
        (hughesYoungReducedMellinScaleConstant T t c u h k *
          (r : ℂ) ^
            (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) +
              -(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) + 1) *
          ∫ x in Set.Ioi (0 : ℝ),
            ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) +
                dfiEquation27LogConstant a (dfiReducedDenominator a q)) *
              ((Real.log r : ℂ) + (Real.log x : ℂ) +
                dfiEquation27LogConstant b (dfiReducedDenominator b q)) *
              ((1 + (x : ℂ)) ^
                  (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))) *
                (x : ℂ) ^
                  (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I))))) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  unfold dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_pureReduced_eq_equation83
    T t c u a b (dfiReducedDenominator a q) (dfiReducedDenominator b q) hrR]
  norm_num

/-- The entire positive-shift DFI equation-(27) series in equation-(83)
form.  The modulus sum remains outside the beta integral, exactly as required
before Hughes--Young move the Mellin line into the absolute-convergence
half-plane. -/
theorem dfiEquation27CentralSeries_pureReduced_eq_equation83
    (T t c u : ℝ) {h k : ℕ} (a b : ℕ) {r : ℕ} (hr : 0 < r) :
    dfiEquation27CentralSeries a b r
        (hughesYoungPureReducedMellinWeight T t c u h k) =
      ∑' q : ℕ,
        (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b r q) *
          (hughesYoungReducedMellinScaleConstant T t c u h k *
            (r : ℂ) ^
              (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) +
                -(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) + 1) *
            ∫ x in Set.Ioi (0 : ℝ),
              ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) +
                  dfiEquation27LogConstant a (dfiReducedDenominator a q)) *
                ((Real.log r : ℂ) + (Real.log x : ℂ) +
                  dfiEquation27LogConstant b (dfiReducedDenominator b q)) *
                ((1 + (x : ℂ)) ^
                    (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))) *
                  (x : ℂ) ^
                    (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I))))) := by
  unfold dfiEquation27CentralSeries
  apply tsum_congr
  intro q
  exact dfiEquation27CentralSummand_pureReduced_eq_equation83
    T t c u a b hr q

/-- A named form of the positive-shift equation-(83) kernel.  Naming the
whole signed source expression prevents later consumers from replacing it
with a norm majorant before the Hughes--Young cancellation step. -/
noncomputable def hughesYoungEquation83PositiveCentral
    (T t c u : ℝ) (h k a b r : ℕ) : ℂ :=
  ∑' q : ℕ,
    (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b r q) *
      (hughesYoungReducedMellinScaleConstant T t c u h k *
        (r : ℂ) ^
          (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) +
            -(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) + 1) *
        ∫ x in Set.Ioi (0 : ℝ),
          ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) +
              dfiEquation27LogConstant a (dfiReducedDenominator a q)) *
            ((Real.log r : ℂ) + (Real.log x : ℂ) +
              dfiEquation27LogConstant b (dfiReducedDenominator b q)) *
            ((1 + (x : ℂ)) ^
                (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))) *
              (x : ℂ) ^
                (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))))

/-- The signed positive-shift central object consumed by the pointwise DFI
decomposition is the exact positive equation-(83) kernel. -/
theorem dfiSignedCentralSeries_ofNat_pureReduced_eq_equation83
    (T t c u : ℝ) {h k : ℕ} (a b : ℕ) {r : ℕ} (hr : 0 < r) :
    dfiSignedCentralSeries a b (r : ℤ)
        (hughesYoungPureReducedMellinWeight T t c u h k) =
      hughesYoungEquation83PositiveCentral T t c u h k a b r := by
  rw [dfiSignedCentralSeries_ofNat]
  unfold hughesYoungEquation83PositiveCentral
  exact dfiEquation27CentralSeries_pureReduced_eq_equation83
    T t c u a b hr

/-- The coordinate-swapped equation-(83) integral used for a negative
shift.  The two Mellin exponents and the two DFI logarithmic factors are
swapped together, exactly matching the negative branch of
`dfiSignedCentralSeries`. -/
theorem dfiEquation27CentralIntegral_swappedPureReduced_eq_equation83
    (T t c u : ℝ) {h k : ℕ} (a b qx qy : ℕ) {r : ℝ} (hr : 0 < r) :
    dfiEquation27CentralIntegral b a qy qx
        (dfiSwapWeight (hughesYoungPureReducedMellinWeight T t c u h k)) r =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        (r : ℂ) ^
          (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) +
            -(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) + 1) *
        ∫ x in Set.Ioi (0 : ℝ),
          ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) +
              dfiEquation27LogConstant b qy) *
            ((Real.log r : ℂ) + (Real.log x : ℂ) +
              dfiEquation27LogConstant a qx) *
            ((1 + (x : ℂ)) ^
                (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I))) *
              (x : ℂ) ^
                (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)))) := by
  apply dfiEquation27CentralIntegral_eq_equation83 b a qy qx
      (A := -(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)))
      (B := -(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))
      (K := hughesYoungReducedMellinScaleConstant T t c u h k) hr
  · intro y hy
    unfold dfiSwapWeight
    exact hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_left
      T t c u h k hy
  · intro y hy
    unfold dfiSwapWeight
    rw [hughesYoungPureReducedMellinWeight_of_pos]
    · ring
    · exact hy
    · linarith

/-- The negative-shift equation-(83) expression, retaining the swapped
arithmetic coefficient and logarithmic factors dictated by DFI's signed
shift convention. -/
noncomputable def hughesYoungEquation83NegativeCentral
    (T t c u : ℝ) (h k a b r : ℕ) : ℂ :=
  ∑' q : ℕ,
    (((b : ℂ) * a)⁻¹ * dfiEquation27ArithmeticCoefficient b a r q) *
      (hughesYoungReducedMellinScaleConstant T t c u h k *
        (r : ℂ) ^
          (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) +
            -(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) + 1) *
        ∫ x in Set.Ioi (0 : ℝ),
          ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) +
              dfiEquation27LogConstant b (dfiReducedDenominator b q)) *
            ((Real.log r : ℂ) + (Real.log x : ℂ) +
              dfiEquation27LogConstant a (dfiReducedDenominator a q)) *
            ((1 + (x : ℂ)) ^
                (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I))) *
              (x : ℂ) ^
                (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)))))

/-- One modulus summand in the negative-shift DFI central series is exactly
the coordinate-swapped Hughes--Young equation-(83) kernel. -/
theorem dfiEquation27CentralSummand_swappedPureReduced_eq_equation83
    (T t c u : ℝ) {h k : ℕ} (a b : ℕ) {r : ℕ} (hr : 0 < r) (q : ℕ) :
    dfiEquation27CentralSummand b a r
        (dfiSwapWeight (hughesYoungPureReducedMellinWeight T t c u h k)) q =
      (((b : ℂ) * a)⁻¹ * dfiEquation27ArithmeticCoefficient b a r q) *
        (hughesYoungReducedMellinScaleConstant T t c u h k *
          (r : ℂ) ^
            (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) +
              -(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) + 1) *
          ∫ x in Set.Ioi (0 : ℝ),
            ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) +
                dfiEquation27LogConstant b (dfiReducedDenominator b q)) *
              ((Real.log r : ℂ) + (Real.log x : ℂ) +
                dfiEquation27LogConstant a (dfiReducedDenominator a q)) *
              ((1 + (x : ℂ)) ^
                  (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I))) *
                (x : ℂ) ^
                  (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))))) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  unfold dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_swappedPureReduced_eq_equation83
    T t c u a b (dfiReducedDenominator a q) (dfiReducedDenominator b q) hrR]
  norm_num

/-- The complete negative-shift DFI central series in the exact
Hughes--Young equation-(83) form. -/
theorem dfiEquation27CentralSeries_swappedPureReduced_eq_equation83
    (T t c u : ℝ) {h k : ℕ} (a b : ℕ) {r : ℕ} (hr : 0 < r) :
    dfiEquation27CentralSeries b a r
        (dfiSwapWeight (hughesYoungPureReducedMellinWeight T t c u h k)) =
      hughesYoungEquation83NegativeCentral T t c u h k a b r := by
  unfold dfiEquation27CentralSeries hughesYoungEquation83NegativeCentral
  apply tsum_congr
  intro q
  exact dfiEquation27CentralSummand_swappedPureReduced_eq_equation83
    T t c u a b hr q

/-- The signed negative-shift central object consumed by the pointwise DFI
decomposition is the exact equation-(83) kernel, not an independently
specified main term. -/
theorem dfiSignedCentralSeries_neg_pureReduced_eq_equation83
    (T t c u : ℝ) {h k : ℕ} (a b : ℕ) {r : ℕ} (hr : 0 < r) :
    dfiSignedCentralSeries a b (-(r : ℤ))
        (hughesYoungPureReducedMellinWeight T t c u h k) =
      hughesYoungEquation83NegativeCentral T t c u h k a b r := by
  rw [dfiSignedCentralSeries_neg_ofNat a b r hr]
  exact dfiEquation27CentralSeries_swappedPureReduced_eq_equation83
    T t c u a b hr

/-! ## Equation (83) as the differentiated Gamma quotient -/

/-- The literal logarithmic beta integral occurring in equation (83) is
the affine mixed derivative of the Gamma quotient.  The order of the two
DFI logarithms and of the two power factors in equation (83) differs from
the canonical order in `hughesYoungAffineLogBetaContinuation`; this theorem
records the exact commutative-algebra bridge rather than treating the
continuation as a new definition of the source integral. -/
theorem hughesYoungEquation83LogBetaIntegral_eq_continuation
    {A B : ℂ} (CX COne : ℂ)
    (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    (∫ x in Set.Ioi (0 : ℝ),
      (COne + (Real.log (1 + x) : ℂ)) *
        (CX + (Real.log x : ℂ)) *
        ((1 + (x : ℂ)) ^ B * (x : ℂ) ^ A)) =
      hughesYoungAffineLogBetaContinuation A B CX COne := by
  rw [← hughesYoungAffineLogBetaIntegral_eq_continuation hA hAB]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  ring

/-- The equation-(83) exponents lie in the literal beta-integral
convergence strip on every positive contour with real part below `1/2`.
The statement includes both inequalities because they are used together
for every modulus and shift. -/
theorem hughesYoungEquation83_exponents_in_betaStrip
    (t u : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    0 <
        (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) + 1).re ∧
      ((-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) +
          -(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) + 1).re < 0) := by
  constructor <;> simp [afeCriticalPoint] <;> linarith

/-- The swapped negative-shift equation-(83) exponents satisfy the same
strip conditions. -/
theorem hughesYoungEquation83_swappedExponents_in_betaStrip
    (t u : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    0 <
        (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) + 1).re ∧
      ((-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) +
          -(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) + 1).re < 0) := by
  constructor <;> simp [afeCriticalPoint] <;> linarith

/-- Equation (83), positive-shift branch, after analytic evaluation of the
two-logarithm beta integral.  This is still the complete DFI modulus series;
the arithmetic sum has not been replaced by a norm majorant. -/
noncomputable def hughesYoungEquation83PositiveContinuation
    (T t c u : ℝ) (h k a b r : ℕ) : ℂ :=
  ∑' q : ℕ,
    (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b r q) *
      (hughesYoungReducedMellinScaleConstant T t c u h k *
        (r : ℂ) ^
          (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) +
            -(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) + 1) *
        hughesYoungAffineLogBetaContinuation
          (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))
          (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)))
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q))
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q)))

/-- The positive equation-(83) series is exactly its differentiated-Gamma
continuation throughout the source convergence strip. -/
theorem hughesYoungEquation83PositiveCentral_eq_continuation
    (T t u : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (h k a b r : ℕ) :
    hughesYoungEquation83PositiveCentral T t c u h k a b r =
      hughesYoungEquation83PositiveContinuation T t c u h k a b r := by
  obtain ⟨hA, hAB⟩ :=
    hughesYoungEquation83_exponents_in_betaStrip t u hc hcHalf
  unfold hughesYoungEquation83PositiveCentral
    hughesYoungEquation83PositiveContinuation
  apply tsum_congr
  intro q
  congr 2
  rw [← hughesYoungEquation83LogBetaIntegral_eq_continuation
    ((Real.log r : ℂ) +
      dfiEquation27LogConstant b (dfiReducedDenominator b q))
    ((Real.log r : ℂ) +
      dfiEquation27LogConstant a (dfiReducedDenominator a q)) hA hAB]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  ring

/-- Equation (83), negative-shift branch, after analytic evaluation of its
coordinate-swapped logarithmic beta integral. -/
noncomputable def hughesYoungEquation83NegativeContinuation
    (T t c u : ℝ) (h k a b r : ℕ) : ℂ :=
  ∑' q : ℕ,
    (((b : ℂ) * a)⁻¹ * dfiEquation27ArithmeticCoefficient b a r q) *
      (hughesYoungReducedMellinScaleConstant T t c u h k *
        (r : ℂ) ^
          (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) +
            -(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) + 1) *
        hughesYoungAffineLogBetaContinuation
          (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)))
          (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q))
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q)))

/-- The negative equation-(83) series is exactly its differentiated-Gamma
continuation throughout the source convergence strip. -/
theorem hughesYoungEquation83NegativeCentral_eq_continuation
    (T t u : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (h k a b r : ℕ) :
    hughesYoungEquation83NegativeCentral T t c u h k a b r =
      hughesYoungEquation83NegativeContinuation T t c u h k a b r := by
  obtain ⟨hA, hAB⟩ :=
    hughesYoungEquation83_swappedExponents_in_betaStrip t u hc hcHalf
  unfold hughesYoungEquation83NegativeCentral
    hughesYoungEquation83NegativeContinuation
  apply tsum_congr
  intro q
  congr 2
  rw [← hughesYoungEquation83LogBetaIntegral_eq_continuation
    ((Real.log r : ℂ) +
      dfiEquation27LogConstant a (dfiReducedDenominator a q))
    ((Real.log r : ℂ) +
      dfiEquation27LogConstant b (dfiReducedDenominator b q)) hA hAB]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  ring

/-! ## Equation (84): the specialized unshifted beta kernel -/

/-- The exact archimedean kernel obtained from equation (83) after putting
the two zeta arguments on the critical line.  This definition deliberately
keeps the digamma and trigamma terms: they encode the two logarithmic
factors in DFI equation (27), and discarding them would lose the source
main-term cancellation. -/
noncomputable def hughesYoungEquation84CriticalBetaKernel
    (t : ℝ) (w CX COne : ℂ) : ℂ :=
  (Complex.Gamma (afeCriticalPoint t - w) *
      Complex.Gamma (2 * w) /
      Complex.Gamma (afeCriticalPoint t + w)) *
    ((Complex.digamma (afeCriticalPoint t - w) -
          Complex.digamma (2 * w) + CX) *
        (Complex.digamma (afeCriticalPoint t + w) -
          Complex.digamma (2 * w) + COne) +
      hughesYoungPolygammaSeries 1 (2 * w))

/-- Positive-shift equation (83) in its exact equation-(84) form. -/
noncomputable def hughesYoungEquation84Positive
    (T t c u : ℝ) (h k a b r : ℕ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  ∑' q : ℕ,
    (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b r q) *
      (hughesYoungReducedMellinScaleConstant T t c u h k *
        (r : ℂ) ^ (-(2 * w)) *
        hughesYoungEquation84CriticalBetaKernel t w
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q))
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q)))

/-- Negative-shift equation (83) in the coordinate-swapped equation-(84)
form. -/
noncomputable def hughesYoungEquation84Negative
    (T t c u : ℝ) (h k a b r : ℕ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  ∑' q : ℕ,
    (((b : ℂ) * a)⁻¹ * dfiEquation27ArithmeticCoefficient b a r q) *
      (hughesYoungReducedMellinScaleConstant T t c u h k *
        (r : ℂ) ^ (-(2 * w)) *
        hughesYoungEquation84CriticalBetaKernel (-t) w
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q))
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q)))

/-- The equation-(84) contour kernel with the Hughes--Young auxiliary
factor omitted.  Naming this analytic core makes the prescribed zero of
`G` visible to the later moving-pole cancellation proof. -/
noncomputable def hughesYoungEquation84RegularizedContourKernelCore
    (t : ℝ) (w CX COne : ℂ) : ℂ :=
  let p := afeCriticalPoint t + w
  let q := afeCriticalPoint (-t) + w
  Complex.exp (100 * w ^ 2) *
    (p * (1 - p)) ^ 2 * q ^ 2 *
    Complex.Gammaℝ p ^ 2 * Complex.Gammaℝ q ^ 2 /
    afePoleNormalization t / w / afeGammaNormalization t *
    hughesYoungEquation84RegularizedBetaKernel t w CX COne

/-- One-step expansion of the analytic equation-(84) contour core.  Using
this theorem avoids asking later estimates to unfold the much larger beta
kernel while solving a definitional-equality goal. -/
theorem hughesYoungEquation84RegularizedContourKernelCore_eq_expanded
    (t : ℝ) (w CX COne : ℂ) :
    hughesYoungEquation84RegularizedContourKernelCore t w CX COne =
      Complex.exp (100 * w ^ 2) *
        ((afeCriticalPoint t + w) * (1 - (afeCriticalPoint t + w))) ^ 2 *
        (afeCriticalPoint (-t) + w) ^ 2 *
        Complex.Gammaℝ (afeCriticalPoint t + w) ^ 2 *
        Complex.Gammaℝ (afeCriticalPoint (-t) + w) ^ 2 /
        afePoleNormalization t / w / afeGammaNormalization t *
        hughesYoungEquation84RegularizedBetaKernel t w CX COne := by
  rfl

/-- The complete pole-cancelled archimedean contour factor for the positive
equation-(84) branch.  The factor `q^2` is what remains of
`(q(1-q))^2` after its `(1-q)^2=(s-w)^2` zero has been absorbed into the
regularized beta kernel. -/
noncomputable def hughesYoungEquation84RegularizedContourKernel
    (t : ℝ) (w CX COne : ℂ) : ℂ :=
  hughesYoungAuxiliaryZero w *
    hughesYoungEquation84RegularizedContourKernelCore t w CX COne

theorem hughesYoungEquation84RegularizedContourKernel_eq_auxiliary_mul_core
    (t : ℝ) (w CX COne : ℂ) :
    hughesYoungEquation84RegularizedContourKernel t w CX COne =
      hughesYoungAuxiliaryZero w *
        hughesYoungEquation84RegularizedContourKernelCore t w CX COne := by
  rfl

/-- The auxiliary and archimedean factors in the regularized equation-(84)
kernel that are independent of the two DFI logarithmic constants. -/
noncomputable def hughesYoungEquation84RegularizedContourPrefactor
    (t : ℝ) (w : ℂ) : ℂ :=
  hughesYoungAuxiliaryZero w *
    (Complex.exp (100 * w ^ 2) *
      ((afeCriticalPoint t + w) * (1 - (afeCriticalPoint t + w))) ^ 2 *
      (afeCriticalPoint (-t) + w) ^ 2 *
      Complex.Gammaℝ (afeCriticalPoint t + w) ^ 2 *
      Complex.Gammaℝ (afeCriticalPoint (-t) + w) ^ 2 /
      afePoleNormalization t / w / afeGammaNormalization t)

/-- At a fixed contour point, the complete equation-(84) kernel is a fixed
auxiliary/archimedean prefactor times the logarithmic beta kernel. -/
theorem hughesYoungEquation84RegularizedContourKernel_eq_prefactor_mul_beta
    (t : ℝ) (w CX COne : ℂ) :
    hughesYoungEquation84RegularizedContourKernel t w CX COne =
      hughesYoungEquation84RegularizedContourPrefactor t w *
        hughesYoungEquation84RegularizedBetaKernel t w CX COne := by
  unfold hughesYoungEquation84RegularizedContourPrefactor
  rw [hughesYoungEquation84RegularizedContourKernel_eq_auxiliary_mul_core,
    hughesYoungEquation84RegularizedContourKernelCore_eq_expanded,
    ← mul_assoc]

set_option maxRecDepth 10000 in
/-- On the original small contour the regularized contour kernel is
literally the product of the opened AFE contour weight and the equation-(84)
beta factor. -/
theorem hughesYoungRightContourWeightComplex_mul_equation84_eq_regularized
    {t : ℝ} {w CX COne : ℂ}
    (hz : 0 < (afeCriticalPoint t - w).re) :
    hughesYoungRightContourWeightComplex t w *
        hughesYoungEquation84CriticalBetaKernel t w CX COne =
      hughesYoungEquation84RegularizedContourKernel t w CX COne := by
  have hOne : 1 - (afeCriticalPoint (-t) + w) =
      afeCriticalPoint t - w := by
    calc
      1 - (afeCriticalPoint (-t) + w) =
          (1 - afeCriticalPoint (-t)) - w := by ring
      _ = afeCriticalPoint t - w := by
        rw [show 1 - afeCriticalPoint (-t) = afeCriticalPoint t by
          simpa only [neg_neg] using one_sub_afeCriticalPoint (-t)]
  have hreg :=
    sq_mul_hughesYoungEquation84CriticalBetaKernel_eq_regularized
      (t := t) (w := w) (CX := CX) (COne := COne) hz
  have hregNamed :
      (afeCriticalPoint t - w) ^ 2 *
          hughesYoungEquation84CriticalBetaKernel t w CX COne =
        hughesYoungEquation84RegularizedBetaKernel t w CX COne := by
    simpa only [hughesYoungEquation84CriticalBetaKernel] using hreg
  unfold hughesYoungRightContourWeightComplex
    hughesYoungEquation84RegularizedContourKernel
    hughesYoungEquation84RegularizedContourKernelCore
  dsimp only
  rw [hOne]
  rw [← hregNamed]
  ring

/-- The complete pole-cancelled equation-(84) contour kernel is holomorphic
throughout the rectangle used to move the central line from
`0 < Re w < 1/2` to `Re w = 1`. -/
theorem differentiableAt_hughesYoungEquation84RegularizedContourKernelCore
    (t : ℝ) {w CX COne : ℂ}
    (hw : 0 < w.re) (hwUpper : w.re < 3 / 2) :
    DifferentiableAt ℂ
      (fun z => hughesYoungEquation84RegularizedContourKernelCore
        t z CX COne) w := by
  let pfun : ℂ → ℂ := fun z => afeCriticalPoint t + z
  let qfun : ℂ → ℂ := fun z => afeCriticalPoint (-t) + z
  have hpDiff : DifferentiableAt ℂ pfun w := by
    dsimp only [pfun]
    fun_prop
  have hqDiff : DifferentiableAt ℂ qfun w := by
    dsimp only [qfun]
    fun_prop
  have hp : 0 < (pfun w).re := by
    dsimp only [pfun]
    simp [afeCriticalPoint]
    linarith
  have hq : 0 < (qfun w).re := by
    dsimp only [qfun]
    simp [afeCriticalPoint]
    linarith
  have hGammaP : DifferentiableAt ℂ
      (fun z => Complex.Gammaℝ (pfun z)) w :=
    (differentiableAt_GammaR_of_re_pos hp).comp w hpDiff
  have hGammaQ : DifferentiableAt ℂ
      (fun z => Complex.Gammaℝ (qfun z)) w :=
    (differentiableAt_GammaR_of_re_pos hq).comp w hqDiff
  have hw0 : w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hBeta : DifferentiableAt ℂ
      (fun z => hughesYoungEquation84RegularizedBetaKernel
        t z CX COne) w :=
    differentiableAt_hughesYoungEquation84RegularizedBetaKernel
      t hw hwUpper
  have hArch : DifferentiableAt ℂ
      (fun z =>
        Complex.exp (100 * z ^ 2) *
          (pfun z * (1 - pfun z)) ^ 2 * (qfun z) ^ 2 *
          Complex.Gammaℝ (pfun z) ^ 2 * Complex.Gammaℝ (qfun z) ^ 2 /
          afePoleNormalization t / z / afeGammaNormalization t) w := by
    fun_prop (disch := assumption)
  have hAll := hArch.mul hBeta
  unfold hughesYoungEquation84RegularizedContourKernelCore
  dsimp only [pfun, qfun] at hAll ⊢
  exact hAll

theorem differentiableAt_hughesYoungEquation84RegularizedContourKernel
    (t : ℝ) {w CX COne : ℂ}
    (hw : 0 < w.re) (hwUpper : w.re < 3 / 2) :
    DifferentiableAt ℂ
      (fun z => hughesYoungEquation84RegularizedContourKernel
        t z CX COne) w := by
  unfold hughesYoungEquation84RegularizedContourKernel
  exact differentiable_hughesYoungAuxiliaryZero.differentiableAt.mul
    (differentiableAt_hughesYoungEquation84RegularizedContourKernelCore
      t hw hwUpper)

/-- Exact source transition from the positive equation-(83) continuation
to equation (84), valid on the original small contour. -/
theorem hughesYoungEquation83PositiveContinuation_eq_equation84
    (T t u : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (h k a b r : ℕ) :
    hughesYoungEquation83PositiveContinuation T t c u h k a b r =
      hughesYoungEquation84Positive T t c u h k a b r := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hw : 0 < w.re := by simp [w, hc]
  have hleft : 0 < (afeCriticalPoint t - w).re := by
    simp [w, afeCriticalPoint]
    linarith
  unfold hughesYoungEquation83PositiveContinuation
    hughesYoungEquation84Positive
  dsimp only [w]
  apply tsum_congr
  intro q
  rw [hughesYoungAffineLogBetaContinuation_critical_eq_explicit
    hleft hw]
  rw [show
    -(afeCriticalPoint (-t) + w) +
        -(afeCriticalPoint t + w) + 1 = -(2 * w) by
      unfold afeCriticalPoint
      push_cast
      ring]
  rfl

/-- Exact source transition from the negative equation-(83) continuation
to its coordinate-swapped equation-(84) form. -/
theorem hughesYoungEquation83NegativeContinuation_eq_equation84
    (T t u : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (h k a b r : ℕ) :
    hughesYoungEquation83NegativeContinuation T t c u h k a b r =
      hughesYoungEquation84Negative T t c u h k a b r := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hw : 0 < w.re := by simp [w, hc]
  have hleft : 0 < (afeCriticalPoint (-t) - w).re := by
    simp [w, afeCriticalPoint]
    linarith
  unfold hughesYoungEquation83NegativeContinuation
    hughesYoungEquation84Negative
  dsimp only [w]
  apply tsum_congr
  intro q
  rw [hughesYoungAffineLogBetaContinuation_critical_swapped_eq_explicit
    hleft hw]
  rw [show
    -(afeCriticalPoint t + w) +
        -(afeCriticalPoint (-t) + w) + 1 = -(2 * w) by
      unfold afeCriticalPoint
      push_cast
      ring]
  rfl

/-- The literal positive DFI central series is equation (84), with every
continuation and critical-line substitution composed in one theorem. -/
theorem hughesYoungEquation83PositiveCentral_eq_equation84
    (T t u : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (h k a b r : ℕ) :
    hughesYoungEquation83PositiveCentral T t c u h k a b r =
      hughesYoungEquation84Positive T t c u h k a b r := by
  rw [hughesYoungEquation83PositiveCentral_eq_continuation
    T t u hc hcHalf h k a b r]
  exact hughesYoungEquation83PositiveContinuation_eq_equation84
    T t u hc hcHalf h k a b r

/-- The literal negative DFI central series is the swapped equation (84). -/
theorem hughesYoungEquation83NegativeCentral_eq_equation84
    (T t u : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (h k a b r : ℕ) :
    hughesYoungEquation83NegativeCentral T t c u h k a b r =
      hughesYoungEquation84Negative T t c u h k a b r := by
  rw [hughesYoungEquation83NegativeCentral_eq_continuation
    T t u hc hcHalf h k a b r]
  exact hughesYoungEquation83NegativeContinuation_eq_equation84
    T t u hc hcHalf h k a b r

end RiemannZeta.GuthMaynard
