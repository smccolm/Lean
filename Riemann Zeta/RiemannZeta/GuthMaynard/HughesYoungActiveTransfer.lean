import RiemannZeta.GuthMaynard.HughesYoungActiveDyadic

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Finite contour transfer for the active Hughes--Young boxes

The active dyadic family is finite.  The definitions below retain every
dyadic coefficient while moving each positive divisor pair from the opening
line to the small line one term at a time.  This is the source-faithful order
of operations in the Hughes--Young argument: absolute opening first, finite
truncation second, and contour displacement only after that truncation.
-/

noncomputable def hughesYoungActiveIntegratedHigh
    (q a b R K : ℕ) (t H : ℝ) : ℂ :=
  ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
    ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
        (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
          (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
          ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u (m, n)

noncomputable def hughesYoungActiveIntegratedSmall
    (T : ℝ) (a b R K : ℕ) (t H : ℝ) : ℂ :=
  ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
    ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
        (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
          (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
          ∫ u in -H..H,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u (m, n)

noncomputable def hughesYoungActiveWholeSmall
    (T : ℝ) (a b R K : ℕ) (t : ℝ) : ℂ :=
  ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
    ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
        (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
          (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
          ∫ u : ℝ,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u (m, n)

theorem continuous_hughesYoungFullDyadicHighPairTerm
    {q : ℕ} (hq : 0 < q) (a b i j : ℕ) (t : ℝ) (p : ℕ × ℕ) :
    Continuous (fun u : ℝ =>
      hughesYoungFullDyadicHighPairTerm q a b i j t u p) := by
  unfold hughesYoungFullDyadicHighPairTerm
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hc : (1 / 2 : ℝ) < 2 * (q : ℝ) := by linarith
  exact (continuous_const.mul continuous_const).mul
    (continuous_hughesYoungRightPairTerm t hc p)

theorem hughesYoungActiveIntegratedHigh_eq_intervalIntegral
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b) (t H : ℝ) :
    hughesYoungActiveIntegratedHigh q a b R K t H =
      ∫ u in -H..H, hughesYoungActiveHighPairSum q a b R K t u := by
  unfold hughesYoungActiveIntegratedHigh
  simp_rw [hughesYoungActiveHighPairSum_eq_finiteBoxes ha hb]
  symm
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro ij hij
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro n hn
        unfold hughesYoungFullDyadicHighPairTerm
        simp
      · intro n hn
        unfold hughesYoungFullDyadicHighPairTerm
        have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
        have hc : (1 / 2 : ℝ) < 2 * (q : ℝ) := by linarith
        have hcont : Continuous (fun u : ℝ =>
            (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
              (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
              hughesYoungRightPairTerm t (2 * q) u (m, n)) :=
          (continuous_const.mul continuous_const).mul
            (continuous_hughesYoungRightPairTerm t hc (m, n))
        exact hcont.intervalIntegrable (μ := volume) (-H) H
    · intro m hm
      have hcont : Continuous (fun u : ℝ =>
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            hughesYoungFullDyadicHighPairTerm q a b ij.1 ij.2 t u (m, n)) :=
        continuous_finsetSum
          (Finset.Icc 1 (hughesYoungFullDyadicBound ij.2))
          (fun n hn => continuous_hughesYoungFullDyadicHighPairTerm
            hq a b ij.1 ij.2 t (m, n))
      exact hcont.intervalIntegrable (μ := volume) (-H) H
  · intro ij hij
    have hcont : Continuous (fun u : ℝ =>
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            hughesYoungFullDyadicHighPairTerm q a b ij.1 ij.2 t u (m, n)) :=
      continuous_finsetSum
        (Finset.Icc 1 (hughesYoungFullDyadicBound ij.1))
        (fun m hm => continuous_finsetSum
          (Finset.Icc 1 (hughesYoungFullDyadicBound ij.2))
          (fun n hn => continuous_hughesYoungFullDyadicHighPairTerm
            hq a b ij.1 ij.2 t (m, n)))
    exact hcont.intervalIntegrable (μ := volume) (-H) H

noncomputable def hughesYoungActiveIntegratedRemainder
    (q a b R K : ℕ) (t H : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ,
    ((1 - hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℝ) : ℂ) *
      ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p

theorem summable_hughesYoungActiveIntegratedHigh
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (t H : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      (hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℂ) *
        ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) := by
  have hc : (1 / 2 : ℝ) < 2 * q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hfull : Summable (fun p : ℕ × ℕ =>
      ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) :=
    (intervalIntegral.hasSum_intervalIntegral_of_summable_norm
      (summable_hughesYoungRightPair_restrict_norm t H hc)).summable
  apply Summable.of_norm_bounded hfull.norm
  intro p
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hughesYoungActiveDyadicWeight_nonneg a b R K p.1 p.2)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (hughesYoungActiveDyadicWeight_nonneg a b R K p.1 p.2)
    (hughesYoungActiveDyadicWeight_le_one ha hb a b R K p.1 p.2)

theorem summable_hughesYoungActiveIntegratedRemainder
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (t H : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      ((1 - hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℝ) : ℂ) *
        ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) := by
  have hc : (1 / 2 : ℝ) < 2 * q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hfull : Summable (fun p : ℕ × ℕ =>
      ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p) :=
    (intervalIntegral.hasSum_intervalIntegral_of_summable_norm
      (summable_hughesYoungRightPair_restrict_norm t H hc)).summable
  apply Summable.of_norm_bounded hfull.norm
  intro p
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr
      (hughesYoungActiveDyadicWeight_le_one ha hb a b R K p.1 p.2))]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (sub_nonneg.mpr
      (hughesYoungActiveDyadicWeight_le_one ha hb a b R K p.1 p.2))
    (sub_le_one_of_le_zero
      (hughesYoungActiveDyadicWeight_nonneg a b R K p.1 p.2))

theorem hughesYoungActiveIntegratedHigh_eq_tsum
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (t H : ℝ) :
    hughesYoungActiveIntegratedHigh q a b R K t H =
      ∑' p : ℕ × ℕ,
        (hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℂ) *
          ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u p := by
  rw [hughesYoungActiveIntegratedHigh_eq_intervalIntegral hq ha hb]
  have hc : (1 / 2 : ℝ) < 2 * q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  let F : (ℕ × ℕ) → C(ℝ, ℂ) := fun p =>
    (hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℂ) •
      hughesYoungRightPairContinuousMap t (2 * q) hc p
  have hsum : Summable (fun p : ℕ × ℕ =>
      ‖(F p).restrict
        (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
    have hfull := summable_hughesYoungRightPair_restrict_norm t H hc
    apply Summable.of_norm_bounded hfull
    intro p
    unfold F
    rw [ContinuousMap.restrict_smul, norm_smul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hughesYoungActiveDyadicWeight_nonneg a b R K p.1 p.2)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (hughesYoungActiveDyadicWeight_nonneg a b R K p.1 p.2)
      (hughesYoungActiveDyadicWeight_le_one ha hb a b R K p.1 p.2)
  have hinterchange :=
    intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum
  calc
    (∫ u in -H..H, hughesYoungActiveHighPairSum q a b R K t u) =
        ∫ u in -H..H, ∑' p : ℕ × ℕ, F p u := by
      apply intervalIntegral.integral_congr
      intro u hu
      unfold hughesYoungActiveHighPairSum F
      apply tsum_congr
      intro p
      simp [hughesYoungRightPairContinuousMap]
    _ = ∑' p : ℕ × ℕ, ∫ u in -H..H, F p u := hinterchange.symm
    _ = _ := by
      apply tsum_congr
      intro p
      unfold F
      simp only [ContinuousMap.smul_apply, smul_eq_mul,
        hughesYoungRightPairContinuousMap]
      rw [intervalIntegral.integral_const_mul]

/-- Exact active/remainder decomposition of the finite-height opening. -/
theorem hughesYoungFiniteZetaProduct_even_eq_active_add_remainder
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (t H : ℝ) :
    hughesYoungFiniteZetaProduct t (2 * q) H =
      (1 / (Real.pi : ℂ)) *
        (hughesYoungActiveIntegratedHigh q a b R K t H +
          hughesYoungActiveIntegratedRemainder q a b R K t H) := by
  unfold hughesYoungFiniteZetaProduct hughesYoungActiveIntegratedRemainder
  rw [hughesYoungActiveIntegratedHigh_eq_tsum hq ha hb]
  have hactive := summable_hughesYoungActiveIntegratedHigh hq ha hb t H
  have hrem := summable_hughesYoungActiveIntegratedRemainder hq ha hb t H
  congr 1
  rw [← hactive.tsum_add hrem]
  apply tsum_congr
  intro p
  push_cast
  ring

set_option maxHeartbeats 800000 in
theorem tendsto_hughesYoungActiveIntegratedHigh_sub_small_zero
    {q : ℕ} (hq : 0 < q) {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (a b R K : ℕ) :
    Tendsto (fun H : ℝ =>
      hughesYoungActiveIntegratedHigh q a b R K t H -
        hughesYoungActiveIntegratedSmall T a b R K t H)
      atTop (𝓝 0) := by
  unfold hughesYoungActiveIntegratedHigh hughesYoungActiveIntegratedSmall
  let D : ℝ → (ℕ × ℕ) → ℕ → ℕ → ℂ := fun H ij m n =>
    ((hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
      (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ)) *
    ((∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u (m, n)) -
      ∫ u in -H..H,
        hughesYoungRightPairTerm t (hughesYoungSmallContour T) u (m, n))
  have hsum : Tendsto
      (fun H : ℝ => ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2), D H ij m n)
      atTop
      (𝓝 (∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2), (0 : ℂ))) := by
    apply tendsto_finsetSum
    intro ij hij
    apply tendsto_finsetSum
    intro m hm
    apply tendsto_finsetSum
    intro n hn
    dsimp only [D]
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm1
    have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
    have hpair : Tendsto (fun H : ℝ =>
        (∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u (m, n)) -
          ∫ u in -H..H,
            hughesYoungRightPairTerm t
              (hughesYoungSmallContour T) u (m, n)) atTop (𝓝 0) :=
      tendsto_hughesYoungRightPairTerm_vertical_sub_zero
        (p := (m, n)) t hm0 hn0
        (hughesYoungSmallContour_spec hT).1
        (by
        have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
        have hsmallLe := (hughesYoungSmallContour_spec hT).2.1
        linarith)
    let C : ℂ :=
      (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
        (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ)
    have hscaled := hpair.const_mul C
    simpa only [C, mul_zero] using hscaled
  have hsum0 : Tendsto
      (fun H : ℝ => ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2), D H ij m n)
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using hsum
  convert hsum0 using 1
  funext H
  dsimp only [D]
  simp only [mul_sub, Finset.sum_sub_distrib]

theorem tendsto_hughesYoungActiveIntegratedSmall_to_whole
    {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T)) (a b R K : ℕ) :
    Tendsto (fun H : ℝ =>
      hughesYoungActiveIntegratedSmall T a b R K t H)
      atTop (𝓝 (hughesYoungActiveWholeSmall T a b R K t)) := by
  unfold hughesYoungActiveIntegratedSmall hughesYoungActiveWholeSmall
  apply tendsto_finsetSum
  intro ij hij
  apply tendsto_finsetSum
  intro m hm
  apply tendsto_finsetSum
  intro n hn
  apply Filter.Tendsto.const_mul
  let B : ℕ := max m n
  have hm0 : 0 < m := by simpa using (Finset.mem_Icc.mp hm).1
  have hn0 : 0 < n := by simpa using (Finset.mem_Icc.mp hn).1
  have hB : 0 < B := lt_of_lt_of_le hm0 (Nat.le_max_left m n)
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungRightPairTerm_small hT ht hB hm0 hn0
      (Nat.le_max_left m n) (Nat.le_max_right m n))
    tendsto_neg_atTop_atBot tendsto_id

/-- Every finite active family on the absolutely convergent opening line
converges to the exact whole small-line integral of the same family. -/
theorem tendsto_hughesYoungActiveIntegratedHigh_to_wholeSmall
    {q : ℕ} (hq : 0 < q) {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T)) (a b R K : ℕ) :
    Tendsto (fun H : ℝ => hughesYoungActiveIntegratedHigh q a b R K t H)
      atTop (𝓝 (hughesYoungActiveWholeSmall T a b R K t)) := by
  have hsmall := tendsto_hughesYoungActiveIntegratedSmall_to_whole
    hT ht a b R K
  have hdiff := tendsto_hughesYoungActiveIntegratedHigh_sub_small_zero
    hq (t := t) hT a b R K
  have hadd := hsmall.add hdiff
  convert hadd using 1
  · funext H
    ring
  · simp

end RiemannZeta.GuthMaynard
