import Mathlib.MeasureTheory.Integral.Prod
import RiemannZeta.GuthMaynard.HughesYoungShiftWeight

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Exact Hughes--Young Mellin/height interchange

This file proves the finite, source-facing Fubini bridge between the opened
Hughes--Young approximate functional equation and the cleaned fixed-shift
weights consumed by the DFI theorem.  Both variables are integrated only
after joint continuity and compact-rectangle integrability have been proved.
-/

/-- The exact two-variable integrand, with Mellin ordinate first and physical
height second. -/
noncomputable def hughesYoungJointLocalizedIntegrand
    (T c X Y : ℝ) (h k : ℕ) (x y u t : ℝ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungLocalizedMellinWeight T t c u X Y h k x y

theorem continuous_uncurry_hughesYoungJointLocalizedIntegrand
    (T : ℝ) {c : ℝ} (hc : 0 < c) (X Y : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Continuous (Function.uncurry
      (hughesYoungJointLocalizedIntegrand T c X Y h k x y)) := by
  unfold hughesYoungJointLocalizedIntegrand
  exact (Complex.ofRealCLM.continuous.comp
    ((contDiff_hughesYoungHeightWeight T).continuous.comp
      continuous_snd)).mul
    (continuous_uncurry_hughesYoungLocalizedMellinWeight_ordinate_height
      T hc X Y hh hk hx hy)

theorem support_uncurry_hughesYoungJointLocalizedIntegrand_subset
    {T : ℝ} (hT : 0 < T) (c X Y : ℝ) (h k : ℕ) (x y : ℝ) :
    Function.support (Function.uncurry
      (hughesYoungJointLocalizedIntegrand T c X Y h k x y)) ⊆
      Set.univ ×ˢ Set.Icc (T / 4) (4 * T) := by
  exact support_uncurry_heightWeight_mul_hughesYoungLocalizedMellinWeight_subset
    hT c X Y h k x y

/-- Compact support in height and a bounded Mellin interval provide the
precise integrability hypothesis needed by `intervalIntegral_integral_swap`.
-/
theorem integrable_uncurry_hughesYoungJointLocalizedIntegrand
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H X Y : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Integrable (Function.uncurry
      (hughesYoungJointLocalizedIntegrand T c X Y h k x y))
      ((volume.restrict (Set.uIoc (-H) H)).prod volume) := by
  let f : ℝ × ℝ → ℂ := Function.uncurry
    (hughesYoungJointLocalizedIntegrand T c X Y h k x y)
  let K : Set (ℝ × ℝ) :=
    Set.uIcc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)
  have hf : Continuous f := by
    dsimp only [f]
    exact continuous_uncurry_hughesYoungJointLocalizedIntegrand
      T hc X Y hh hk hx hy
  have hK : IsCompact K := isCompact_uIcc.prod isCompact_Icc
  have hsmall : IntegrableOn f K (volume.prod volume) :=
    hf.continuousOn.integrableOn_compact hK
  have hbig : IntegrableOn f
      (Set.uIoc (-H) H ×ˢ Set.univ) (volume.prod volume) := by
    apply hsmall.of_forall_diff_eq_zero
      (measurableSet_uIoc.prod MeasurableSet.univ)
    intro p hp
    have ht : p.2 ∉ Set.Icc (T / 4) (4 * T) := by
      intro hp2
      apply hp.2
      exact ⟨Set.uIoc_subset_uIcc hp.1.1, hp2⟩
    have hnmem : p ∉ Function.support f := by
      intro hmem
      exact ht ((support_uncurry_hughesYoungJointLocalizedIntegrand_subset
        hT c X Y h k x y hmem).2)
    by_contra hne
    exact hnmem hne
  rw [IntegrableOn, ← Measure.prod_restrict] at hbig
  simpa using hbig

/-- Dyadic localization of the finite source weight is exactly the compact
Mellin integral of the literal localized DFI weight. -/
theorem dyadicCutoff_mul_hughesYoungFiniteSourceWeight_eq_integral
    (T t c H X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (hughesYoungDyadicCutoffAt X x : ℂ) *
        (hughesYoungDyadicCutoffAt Y y : ℂ) *
        hughesYoungFiniteSourceWeight T t c H h k x y =
      ∫ u in -H..H,
        hughesYoungLocalizedMellinWeight T t c u X Y h k x y := by
  let C : ℂ :=
    (hughesYoungDyadicCutoffAt X x : ℂ) *
      (hughesYoungDyadicCutoffAt Y y : ℂ) *
      (shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
        shortMobiusSquareCoeff T k *
        (k : ℂ) ^ (-afeCriticalPoint (-t)) *
        (1 / (Real.pi : ℂ)))
  let g : ℝ → ℂ := fun u =>
    let w : ℂ := (c : ℂ) + (u : ℂ) * I
    hughesYoungRightContourWeight t c u *
      ((x / h : ℝ) : ℂ) ^ (-(afeCriticalPoint t + w)) *
      ((y / k : ℝ) : ℂ) ^ (-(afeCriticalPoint (-t) + w))
  calc
    (hughesYoungDyadicCutoffAt X x : ℂ) *
          (hughesYoungDyadicCutoffAt Y y : ℂ) *
          hughesYoungFiniteSourceWeight T t c H h k x y =
        C * (∫ u in -H..H, g u) := by
      unfold hughesYoungFiniteSourceWeight
      dsimp only [C, g]
      ring
    _ = ∫ u in -H..H, C * g u := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ u in -H..H,
        hughesYoungLocalizedMellinWeight T t c u X Y h k x y := by
      apply intervalIntegral.integral_congr
      intro u _hu
      change C * g u =
        hughesYoungLocalizedMellinWeight T t c u X Y h k x y
      rw [hughesYoungLocalizedMellinWeight_eq_source_integrand
        T t c u X Y hh hk hx hy]
      dsimp only [C, g]
      ring

/-- Exact Fubini bridge for one positive physical pair. -/
theorem dyadicCutoff_mul_hughesYoungIntegratedSourceWeight_eq_integral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (H X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (hughesYoungDyadicCutoffAt X x : ℂ) *
        (hughesYoungDyadicCutoffAt Y y : ℂ) *
        hughesYoungIntegratedSourceWeight T c H h k x y =
      ∫ u in -H..H, ∫ t : ℝ,
        hughesYoungJointLocalizedIntegrand T c X Y h k x y u t := by
  let A : ℂ := (hughesYoungDyadicCutoffAt X x : ℂ) *
    (hughesYoungDyadicCutoffAt Y y : ℂ)
  have hpoint : ∀ t : ℝ,
      A * ((hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteSourceWeight T t c H h k x y) =
        ∫ u in -H..H,
          hughesYoungJointLocalizedIntegrand T c X Y h k x y u t := by
    intro t
    rw [show A * ((hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteSourceWeight T t c H h k x y) =
      (hughesYoungHeightWeight T t : ℂ) *
        ((hughesYoungDyadicCutoffAt X x : ℂ) *
          (hughesYoungDyadicCutoffAt Y y : ℂ) *
          hughesYoungFiniteSourceWeight T t c H h k x y) by
      dsimp only [A]
      ring]
    rw [dyadicCutoff_mul_hughesYoungFiniteSourceWeight_eq_integral
      T t c H X Y hh hk hx hy]
    rw [← intervalIntegral.integral_const_mul]
    rfl
  unfold hughesYoungIntegratedSourceWeight
  rw [show (hughesYoungDyadicCutoffAt X x : ℂ) *
      (hughesYoungDyadicCutoffAt Y y : ℂ) *
      (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteSourceWeight T t c H h k x y) =
      A * (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteSourceWeight T t c H h k x y) by
    rfl]
  rw [← integral_const_mul]
  rw [integral_congr_ae (Eventually.of_forall hpoint)]
  exact (intervalIntegral_integral_swap
    (integrable_uncurry_hughesYoungJointLocalizedIntegrand
      hT hc H X Y hh hk hx hy)).symm

/-- On a fixed nonzero shift, the exact localized source box is the Mellin
integral of `T` times Hughes--Young's cleaned equation-(70) weight. -/
theorem dyadicCutoff_mul_hughesYoungIntegratedSourceWeight_eq_cleaned
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (H X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℤ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hshift : x - y = (r : ℝ)) :
    (hughesYoungDyadicCutoffAt X x : ℂ) *
        (hughesYoungDyadicCutoffAt Y y : ℂ) *
        hughesYoungIntegratedSourceWeight T c H h k x y =
      ∫ u in -H..H, (T : ℂ) *
        hughesYoungCleanedShiftWeight T c u X Y h k r x y := by
  rw [dyadicCutoff_mul_hughesYoungIntegratedSourceWeight_eq_integral
    hT hc H X Y hh hk hx hy]
  apply intervalIntegral.integral_congr
  intro u _hu
  change (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungLocalizedMellinWeight T t c u X Y h k x y) =
    (T : ℂ) * hughesYoungCleanedShiftWeight T c u X Y h k r x y
  rw [hughesYoungCleanedShiftWeight_eq_heightIntegral
    T c u X Y hh hk hx hy hshift]
  field_simp [hT.ne']

/-- The exact height integral varies continuously with the Mellin ordinate.
The proof uses the same compact height support as the Fubini bridge, so no
dominating function is postulated. -/
theorem continuous_integral_hughesYoungJointLocalizedIntegrand
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (X Y : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Continuous (fun u : ℝ => ∫ t : ℝ,
      hughesYoungJointLocalizedIntegrand T c X Y h k x y u t) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support
    (s := Set.univ) (k := Set.Icc (T / 4) (4 * T)) isCompact_Icc
  · exact (continuous_uncurry_hughesYoungJointLocalizedIntegrand
      T hc X Y hh hk hx hy).continuousOn
  · intro u t _hu ht
    unfold hughesYoungJointLocalizedIntegrand
    have hzero : hughesYoungHeightWeight T t = 0 := by
      by_contra hne
      exact ht (hughesYoungHeightWeight_support hT hne)
    rw [hzero]
    simp

/-- Continuity, hence interval integrability, of one literal cleaned
fixed-shift weight in the Mellin ordinate. -/
theorem continuous_hughesYoungCleanedShiftWeight_ordinate
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (X Y : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℤ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hshift : x - y = (r : ℝ)) :
    Continuous (fun u : ℝ =>
      hughesYoungCleanedShiftWeight T c u X Y h k r x y) := by
  rw [show (fun u : ℝ =>
      hughesYoungCleanedShiftWeight T c u X Y h k r x y) =
      fun u : ℝ => (1 / (T : ℂ)) *
        (∫ t : ℝ,
          hughesYoungJointLocalizedIntegrand T c X Y h k x y u t) by
    funext u
    unfold hughesYoungJointLocalizedIntegrand
    exact hughesYoungCleanedShiftWeight_eq_heightIntegral
      T c u X Y hh hk hx hy hshift]
  exact continuous_const.mul
    (continuous_integral_hughesYoungJointLocalizedIntegrand
      hT hc X Y hh hk hx hy)

theorem intervalIntegrable_hughesYoungCleanedShiftWeight_ordinate
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H X Y : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℤ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hshift : x - y = (r : ℝ)) :
    IntervalIntegrable (fun u : ℝ =>
      hughesYoungCleanedShiftWeight T c u X Y h k r x y)
      volume (-H) H :=
  (continuous_hughesYoungCleanedShiftWeight_ordinate
    hT hc X Y hh hk hx hy hshift).intervalIntegrable _ _

/-- The exact finite shifted-divisor box obtained from the opened AFE is the
Mellin integral of the literal cleaned DFI shifted sum.  This is the
source-entry consumer missing between the finite Hughes--Young expansion and
the quantitative DFI theorem. -/
theorem dfiDyadicShiftedDivisorSum_integratedSource_eq_integral_cleaned
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (H X Y : ℝ) {h k a b M N : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (r : ℤ) :
    dfiDyadicShiftedDivisorSum
        (fun x y =>
          (hughesYoungDyadicCutoffAt X x : ℂ) *
            (hughesYoungDyadicCutoffAt Y y : ℂ) *
            hughesYoungIntegratedSourceWeight T c H h k x y)
        a b M N r =
      ∫ u in -H..H, (T : ℂ) *
        dfiDyadicShiftedDivisorSum
          (hughesYoungCleanedShiftWeight T c u X Y h k r)
          a b M N r := by
  let q : ℕ → ℕ → ℝ → ℂ := fun m n u =>
    if quadraticDivisorShift a b m n = r then
      divisorWeight m * divisorWeight n *
        ((T : ℂ) * hughesYoungCleanedShiftWeight T c u X Y h k r
          (a * m) (b * n))
    else 0
  have hmpos : ∀ m ∈ Finset.Icc 1 M, 0 < m := by
    intro m hm
    exact (Finset.mem_Icc.mp hm).1
  have hnpos : ∀ n ∈ Finset.Icc 1 N, 0 < n := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).1
  have hphysical : ∀ m ∈ Finset.Icc 1 M, ∀ n ∈ Finset.Icc 1 N,
      quadraticDivisorShift a b m n = r →
      (a * m : ℝ) - (b * n : ℝ) = (r : ℝ) := by
    intro m _hm n _hn hs
    unfold quadraticDivisorShift at hs
    exact_mod_cast hs
  have hq : ∀ m ∈ Finset.Icc 1 M, ∀ n ∈ Finset.Icc 1 N,
      Continuous (q m n) := by
    intro m hm n hn
    by_cases hs : quadraticDivisorShift a b m n = r
    · have hqeq : q m n = (fun u : ℝ =>
          divisorWeight m * divisorWeight n *
            ((T : ℂ) * hughesYoungCleanedShiftWeight T c u X Y h k r
              (a * m) (b * n))) := by
        funext u
        simp [q, hs]
      rw [hqeq]
      have ham : 0 < a * m := Nat.mul_pos ha (hmpos m hm)
      have hbn : 0 < b * n := Nat.mul_pos hb (hnpos n hn)
      exact (continuous_const.mul continuous_const).mul
        (continuous_const.mul
          (continuous_hughesYoungCleanedShiftWeight_ordinate
            hT hc X Y hh hk (by exact_mod_cast ham) (by exact_mod_cast hbn)
            (hphysical m hm n hn hs)))
    · have hqeq : q m n = (fun _u : ℝ => (0 : ℂ)) := by
        funext u
        simp [q, hs]
      rw [hqeq]
      exact continuous_const
  have hterm : ∀ m ∈ Finset.Icc 1 M, ∀ n ∈ Finset.Icc 1 N,
      (if quadraticDivisorShift a b m n = r then
        divisorWeight m * divisorWeight n *
          ((hughesYoungDyadicCutoffAt X (a * m) : ℂ) *
            (hughesYoungDyadicCutoffAt Y (b * n) : ℂ) *
            hughesYoungIntegratedSourceWeight T c H h k (a * m) (b * n))
       else 0) = ∫ u in -H..H, q m n u := by
    intro m hm n hn
    by_cases hs : quadraticDivisorShift a b m n = r
    · simp only [hs, if_true]
      have ham : 0 < a * m := Nat.mul_pos ha (hmpos m hm)
      have hbn : 0 < b * n := Nat.mul_pos hb (hnpos n hn)
      rw [dyadicCutoff_mul_hughesYoungIntegratedSourceWeight_eq_cleaned
        hT hc H X Y hh hk (by exact_mod_cast ham) (by exact_mod_cast hbn)
        (hphysical m hm n hn hs)]
      have hqeq : q m n = (fun u : ℝ =>
          divisorWeight m * divisorWeight n *
            ((T : ℂ) * hughesYoungCleanedShiftWeight T c u X Y h k r
              (a * m) (b * n))) := by
        funext u
        simp [q, hs]
      rw [hqeq]
      simp only [intervalIntegral.integral_const_mul]
    · simp [q, hs]
  have hswap :
      (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        ∫ u in -H..H, q m n u) =
      ∫ u in -H..H, ∑ m ∈ Finset.Icc 1 M,
        ∑ n ∈ Finset.Icc 1 N, q m n u := by
    symm
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [intervalIntegral.integral_finsetSum]
      intro n hn
      exact (hq m hm n hn).intervalIntegrable _ _
    · intro m hm
      exact (continuous_finsetSum _ fun n hn => hq m hm n hn).intervalIntegrable _ _
  unfold dfiDyadicShiftedDivisorSum
  calc
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
      if quadraticDivisorShift a b m n = r then
        divisorWeight m * divisorWeight n *
          ((hughesYoungDyadicCutoffAt X (a * m) : ℂ) *
            (hughesYoungDyadicCutoffAt Y (b * n) : ℂ) *
            hughesYoungIntegratedSourceWeight T c H h k (a * m) (b * n))
      else 0) =
        ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ∫ u in -H..H, q m n u := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact hterm m hm n hn
    _ = ∫ u in -H..H, ∑ m ∈ Finset.Icc 1 M,
        ∑ n ∈ Finset.Icc 1 N, q m n u := hswap
    _ = ∫ u in -H..H, (T : ℂ) *
        (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          if quadraticDivisorShift a b m n = r then
            divisorWeight m * divisorWeight n *
              hughesYoungCleanedShiftWeight T c u X Y h k r
                (a * m) (b * n)
          else 0) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      dsimp only [q]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hs : quadraticDivisorShift a b m n = r
      · simp [hs]
        ring
      · simp [hs]

/-- Continuity in the Mellin ordinate of one literal cleaned DFI shifted
sum.  The result is finite, but each physical summand still uses the exact
shift relation needed by the cleaned Hughes--Young weight. -/
theorem continuous_dfiDyadicShiftedDivisorSum_cleaned_ordinate
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (X Y : ℝ) {h k a b M N : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (r : ℤ) :
    Continuous (fun u : ℝ =>
      dfiDyadicShiftedDivisorSum
        (hughesYoungCleanedShiftWeight T c u X Y h k r)
        a b M N r) := by
  exact continuous_finsetSum (Finset.Icc 1 M) fun m hm =>
    continuous_finsetSum (Finset.Icc 1 N) fun n hn => by
      by_cases hs : quadraticDivisorShift a b m n = r
      · simp only [hs, if_true]
        have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
        have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
        have hshift : (a * m : ℝ) - (b * n : ℝ) = (r : ℝ) := by
          unfold quadraticDivisorShift at hs
          exact_mod_cast hs
        exact (continuous_const.mul continuous_const).mul
          (continuous_hughesYoungCleanedShiftWeight_ordinate
            hT hc X Y hh hk
            (by exact_mod_cast Nat.mul_pos ha hmpos)
            (by exact_mod_cast Nat.mul_pos hb hnpos) hshift)
      · simp only [hs, if_false]
        exact continuous_const

/-- The exact Fubini bridge simultaneously over any finite family of shifts.
This is the form used by the Hughes--Young near-shift decomposition. -/
theorem sum_dfiDyadicShiftedDivisorSum_integratedSource_eq_integral_cleaned
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (H X Y : ℝ) {h k a b M N : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (s : Finset ℤ) :
    (∑ r ∈ s,
      dfiDyadicShiftedDivisorSum
        (fun x y =>
          (hughesYoungDyadicCutoffAt X x : ℂ) *
            (hughesYoungDyadicCutoffAt Y y : ℂ) *
            hughesYoungIntegratedSourceWeight T c H h k x y)
        a b M N r) =
      ∫ u in -H..H, (T : ℂ) *
        (∑ r ∈ s,
          dfiDyadicShiftedDivisorSum
            (hughesYoungCleanedShiftWeight T c u X Y h k r)
            a b M N r) := by
  have hcontinuous : ∀ r : ℤ, Continuous (fun u : ℝ =>
      (T : ℂ) * dfiDyadicShiftedDivisorSum
        (hughesYoungCleanedShiftWeight T c u X Y h k r)
        a b M N r) := by
    intro r
    exact continuous_const.mul
      (continuous_dfiDyadicShiftedDivisorSum_cleaned_ordinate
        hT hc X Y hh hk ha hb r)
  simp_rw [dfiDyadicShiftedDivisorSum_integratedSource_eq_integral_cleaned
    hT hc H X Y hh hk ha hb]
  calc
    (∑ r ∈ s, ∫ u in -H..H, (T : ℂ) *
        dfiDyadicShiftedDivisorSum
          (hughesYoungCleanedShiftWeight T c u X Y h k r)
          a b M N r) =
        ∫ u in -H..H, ∑ r ∈ s, (T : ℂ) *
          dfiDyadicShiftedDivisorSum
            (hughesYoungCleanedShiftWeight T c u X Y h k r)
            a b M N r := by
      symm
      rw [intervalIntegral.integral_finsetSum]
      intro r hr
      exact (hcontinuous r).intervalIntegrable _ _
    _ = ∫ u in -H..H, (T : ℂ) *
        (∑ r ∈ s, dfiDyadicShiftedDivisorSum
          (hughesYoungCleanedShiftWeight T c u X Y h k r)
          a b M N r) := by
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      exact (Finset.mul_sum s (fun r : ℤ =>
        dfiDyadicShiftedDivisorSum
          (hughesYoungCleanedShiftWeight T c u X Y h k r)
          a b M N r) (T : ℂ)).symm

end RiemannZeta.GuthMaynard
