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

/-- The `hughesYoungActiveIntegratedHigh` definition used by the source-facing construction in `HughesYoungActiveTransfer`. -/
noncomputable def hughesYoungActiveIntegratedHigh
    (q a b R K : ℕ) (t H : ℝ) : ℂ :=
  ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
    ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
        (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
          (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
          ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u (m, n)

/-- The `hughesYoungActiveIntegratedSmall` definition used by the source-facing construction in `HughesYoungActiveTransfer`. -/
noncomputable def hughesYoungActiveIntegratedSmall
    (T : ℝ) (a b R K : ℕ) (t H : ℝ) : ℂ :=
  ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
    ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
        (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
          (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
          ∫ u in -H..H,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u (m, n)

/-- The `hughesYoungActiveWholeSmall` definition used by the source-facing construction in `HughesYoungActiveTransfer`. -/
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

/-- The `hughesYoungActiveIntegratedRemainder` definition used by the source-facing construction in `HughesYoungActiveTransfer`. -/
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
  by_cases hp1 : p.1 = 0
  · simp [hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero t (2 * q) _ hp1]
  by_cases hp2 : p.2 = 0
  · simp [hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero t (2 * q) _ hp2]
  have hp1pos : 0 < p.1 := Nat.pos_of_ne_zero hp1
  have hp2pos : 0 < p.2 := Nat.pos_of_ne_zero hp2
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hughesYoungActiveDyadicWeight_nonneg a b R K p.1 p.2)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (hughesYoungActiveDyadicWeight_le_one ha hb hp1pos hp2pos)

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
  by_cases hp1 : p.1 = 0
  · simp [hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero t (2 * q) _ hp1]
  by_cases hp2 : p.2 = 0
  · simp [hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero t (2 * q) _ hp2]
  have hp1pos : 0 < p.1 := Nat.pos_of_ne_zero hp1
  have hp2pos : 0 < p.2 := Nat.pos_of_ne_zero hp2
  have hwle : hughesYoungActiveDyadicWeight a b R K p.1 p.2 ≤ 1 :=
    hughesYoungActiveDyadicWeight_le_one ha hb hp1pos hp2pos
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hwle)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (by
      have hw0 := hughesYoungActiveDyadicWeight_nonneg a b R K p.1 p.2
      linarith)

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
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hrestrict :
        (ContinuousMap.restrict
            (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)
            ((hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℂ) •
              hughesYoungRightPairContinuousMap t (2 * q) hc p)) =
          (hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℂ) •
            (hughesYoungRightPairContinuousMap t (2 * q) hc p).restrict
              (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) := by
      ext x
      rfl
    rw [hrestrict]
    by_cases hp1 : p.1 = 0
    · have hz :
          (hughesYoungRightPairContinuousMap t (2 * q) hc p).restrict
              (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) = 0 := by
        ext x
        exact hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero t (2 * q) x hp1
      rw [hz]
      simp only [smul_zero, norm_zero]
      exact le_rfl
    by_cases hp2 : p.2 = 0
    · have hz :
          (hughesYoungRightPairContinuousMap t (2 * q) hc p).restrict
              (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) = 0 := by
        ext x
        exact hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero t (2 * q) x hp2
      rw [hz]
      simp only [smul_zero, norm_zero]
      exact le_rfl
    have hp1pos : 0 < p.1 := Nat.pos_of_ne_zero hp1
    have hp2pos : 0 < p.2 := Nat.pos_of_ne_zero hp2
    rw [norm_smul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hughesYoungActiveDyadicWeight_nonneg a b R K p.1 p.2)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (hughesYoungActiveDyadicWeight_le_one ha hb hp1pos hp2pos)
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
      rfl

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
  have hactive := summable_hughesYoungActiveIntegratedHigh
    (R := R) (K := K) hq ha hb t H
  have hrem := summable_hughesYoungActiveIntegratedRemainder
    (R := R) (K := K) hq ha hb t H
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
  have hm0 : 0 < m := by simpa using (Finset.mem_Icc.mp hm).1
  have hn0 : 0 < n := by simpa using (Finset.mem_Icc.mp hn).1
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungRightPairTerm_small hT ht hm0 hn0)
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

/-- The `hughesYoungActiveRemainderContinuousMap` definition used by the source-facing construction in `HughesYoungActiveTransfer`. -/
noncomputable def hughesYoungActiveRemainderContinuousMap
    (q a b R K : ℕ) (t : ℝ) (hc : (1 / 2 : ℝ) < 2 * q)
    (p : ℕ × ℕ) : C(ℝ, ℂ) :=
  ⟨fun u =>
      ((1 - hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℝ) : ℂ) *
        hughesYoungRightPairTerm t (2 * q) u p,
    continuous_const.mul (continuous_hughesYoungRightPairTerm t hc p)⟩

theorem summable_hughesYoungActiveRemainderContinuousMap_restrict_norm
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (t H : ℝ) :
    let hc : (1 / 2 : ℝ) < 2 * q := by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    Summable (fun p : ℕ × ℕ =>
      ‖(hughesYoungActiveRemainderContinuousMap q a b R K t hc p).restrict
        (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
  let hc : (1 / 2 : ℝ) < 2 * q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hfull := summable_hughesYoungRightPair_restrict_norm t H hc
  apply Summable.of_norm_bounded hfull
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hrestrict :
      (hughesYoungActiveRemainderContinuousMap q a b R K t hc p).restrict
          (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) =
        ((1 - hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℝ) : ℂ) •
          (hughesYoungRightPairContinuousMap t (2 * q) hc p).restrict
            (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) := by
    ext x
    rfl
  rw [hrestrict]
  by_cases hp1 : p.1 = 0
  · have hz :
        (hughesYoungRightPairContinuousMap t (2 * q) hc p).restrict
            (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) = 0 := by
      ext x
      exact hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero t (2 * q) x hp1
    rw [hz]
    simp only [smul_zero, norm_zero]
    exact le_rfl
  by_cases hp2 : p.2 = 0
  · have hz :
        (hughesYoungRightPairContinuousMap t (2 * q) hc p).restrict
            (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) = 0 := by
      ext x
      exact hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero t (2 * q) x hp2
    rw [hz]
    simp only [smul_zero, norm_zero]
    exact le_rfl
  have hp1pos : 0 < p.1 := Nat.pos_of_ne_zero hp1
  have hp2pos : 0 < p.2 := Nat.pos_of_ne_zero hp2
  have hwle : hughesYoungActiveDyadicWeight a b R K p.1 p.2 ≤ 1 :=
    hughesYoungActiveDyadicWeight_le_one ha hb hp1pos hp2pos
  rw [norm_smul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hwle)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by
    have hw0 := hughesYoungActiveDyadicWeight_nonneg a b R K p.1 p.2
    linarith)

theorem hughesYoungActiveIntegratedRemainder_eq_intervalIntegral
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (t H : ℝ) :
    hughesYoungActiveIntegratedRemainder q a b R K t H =
      ∫ u in -H..H, hughesYoungActiveHighPairRemainder q a b R K t u := by
  let hc : (1 / 2 : ℝ) < 2 * q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hinterchange :=
    intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (summable_hughesYoungActiveRemainderContinuousMap_restrict_norm
        (R := R) (K := K) hq ha hb t H)
  calc
    hughesYoungActiveIntegratedRemainder q a b R K t H =
        ∑' p : ℕ × ℕ,
          ∫ u in -H..H,
            hughesYoungActiveRemainderContinuousMap q a b R K t hc p u := by
      unfold hughesYoungActiveIntegratedRemainder
      apply tsum_congr
      intro p
      simp only [hughesYoungActiveRemainderContinuousMap,
        ContinuousMap.coe_mk]
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ u in -H..H,
        ∑' p : ℕ × ℕ,
          hughesYoungActiveRemainderContinuousMap q a b R K t hc p u :=
      hinterchange
    _ = ∫ u in -H..H,
        hughesYoungActiveHighPairRemainder q a b R K t u := by
      apply intervalIntegral.integral_congr
      intro u _hu
      unfold hughesYoungActiveHighPairRemainder
      apply tsum_congr
      intro p
      rfl

theorem integrable_hughesYoungActiveHighPairRemainder
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hT : 1 ≤ T) (ht : t ∈ Set.Icc (T / 4) (4 * T)) :
    Integrable (fun u : ℝ =>
      hughesYoungActiveHighPairRemainder q a b R K t u) := by
  let C : ℝ := 256 * Real.exp (400 * (q : ℝ) ^ 2) *
    ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
    (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
    hughesYoungReferenceDivisorPairMass η
  let K₀ : ℝ := 625 * (2 * (q : ℝ) + 1) ^ 8
  let g : ℝ → ℝ := fun u =>
    Real.exp (-84 * u ^ 2) * (1 + |u|) ^ (4 * q + 16)
  have hg : Integrable g :=
    integrable_exp_neg_84_mul_one_add_abs_pow (4 * q + 16)
  have hmeas : AEStronglyMeasurable (fun u : ℝ =>
      hughesYoungActiveHighPairRemainder q a b R K t u) := by
    have hc : (1 / 2 : ℝ) < 2 * q := by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    have hpmeas : ∀ p : ℕ × ℕ, AEMeasurable (fun u : ℝ =>
        ((1 - hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℝ) : ℂ) *
          hughesYoungRightPairTerm t (2 * q) u p) := by
      intro p
      exact (continuous_const.mul
        (continuous_hughesYoungRightPairTerm t hc p)).aemeasurable
    unfold hughesYoungActiveHighPairRemainder
    exact (AEMeasurable.tsum hpmeas).aestronglyMeasurable
  apply (hg.const_mul (C * K₀)).mono' hmeas
  filter_upwards with u
  have hweight :=
    norm_hughesYoungRightContourWeight_even_le_on_height_support hT ht hq u
  have htail := norm_hughesYoungActiveHighPairRemainder_le
    hq ha hb hR hcover t u hη0 hη
  have hexp :
      Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) =
        Real.exp (400 * (q : ℝ) ^ 2) * Real.exp (-84 * u ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbasepow :
      ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8) =
        ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
          (1 + |u|) ^ (4 * q + 8) := by
    rw [mul_pow]
  calc
    ‖hughesYoungActiveHighPairRemainder q a b R K t u‖ ≤
        ‖hughesYoungRightContourWeight t (2 * q) u‖ *
          (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
          hughesYoungReferenceDivisorPairMass η := htail
    _ ≤ (160000 * (2 * (q : ℝ) + 1) ^ 8 *
          Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) *
          ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8) *
          (1 + |u|) ^ 8) *
          (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
          hughesYoungReferenceDivisorPairMass η := by
      gcongr
      exact hughesYoungReferenceDivisorPairMass_nonneg η
    _ = (C * K₀) * g u := by
      rw [hexp, hbasepow]
      unfold C K₀ g
      ring

/-- The `hughesYoungActiveWholeHighRemainder` definition used by the source-facing construction in `HughesYoungActiveTransfer`. -/
noncomputable def hughesYoungActiveWholeHighRemainder
    (q a b R K : ℕ) (t : ℝ) : ℂ :=
  ∫ u : ℝ, hughesYoungActiveHighPairRemainder q a b R K t u

theorem tendsto_hughesYoungActiveIntegratedRemainder
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hT : 1 ≤ T) (ht : t ∈ Set.Icc (T / 4) (4 * T)) :
    Tendsto (fun H : ℝ =>
      hughesYoungActiveIntegratedRemainder q a b R K t H)
      atTop (𝓝 (hughesYoungActiveWholeHighRemainder q a b R K t)) := by
  rw [show (fun H : ℝ =>
      hughesYoungActiveIntegratedRemainder q a b R K t H) =
      (fun H : ℝ => ∫ u in -H..H,
        hughesYoungActiveHighPairRemainder q a b R K t u) by
    funext H
    exact hughesYoungActiveIntegratedRemainder_eq_intervalIntegral
      hq ha hb t H]
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungActiveHighPairRemainder
      hq ha hb hR hcover η hη0 hη hT ht)
    tendsto_neg_atTop_atBot tendsto_id

theorem exists_norm_hughesYoungActiveIntegratedRemainder_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ {a b R K : ℕ} {T t H : ℝ},
      0 < a → 0 < b → 0 < R →
      ((a * b * R : ℕ) : ℝ) ≤ hughesYoungDyadicRatio ^ (K + 1) →
      1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) → 0 ≤ H →
      ‖hughesYoungActiveIntegratedRemainder q a b R K t H‖ ≤
        (256 * Real.exp (400 * (q : ℝ) ^ 2) *
          ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
          (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
          hughesYoungReferenceDivisorPairMass η) * L := by
  obtain ⟨L, hL, hmoment⟩ :=
    exists_intervalIntegral_exp_neg_84_mul_one_add_abs_pow_le (4 * q + 16)
  let K₀ : ℝ := 625 * (2 * (q : ℝ) + 1) ^ 8
  have hK₀ : 0 < K₀ := by dsimp only [K₀]; positivity
  refine ⟨K₀ * L, mul_pos hK₀ hL, ?_⟩
  intro a b R K T t H ha hb hR hcover hT ht hH
  let C : ℝ := 256 * Real.exp (400 * (q : ℝ) ^ 2) *
    ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
    (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
    hughesYoungReferenceDivisorPairMass η
  let g : ℝ → ℝ := fun u =>
    Real.exp (-84 * u ^ 2) * (1 + |u|) ^ (4 * q + 16)
  have hC0 : 0 ≤ C := by
    unfold C
    exact mul_nonneg (by positivity)
      (hughesYoungReferenceDivisorPairMass_nonneg η)
  have hg : IntervalIntegrable g volume (-H) H :=
    (integrable_exp_neg_84_mul_one_add_abs_pow (4 * q + 16)).intervalIntegrable
  have horder : -H ≤ H := by linarith
  rw [hughesYoungActiveIntegratedRemainder_eq_intervalIntegral hq ha hb]
  calc
    ‖∫ u in -H..H,
        hughesYoungActiveHighPairRemainder q a b R K t u‖ ≤
        ∫ u in -H..H, (C * K₀) * g u := by
      apply intervalIntegral.norm_integral_le_of_norm_le horder
      · filter_upwards with u _hu
        have hweight :=
          norm_hughesYoungRightContourWeight_even_le_on_height_support
            hT ht hq u
        have htail := norm_hughesYoungActiveHighPairRemainder_le
          hq ha hb hR hcover t u hη0 hη
        have hexp :
            Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) =
              Real.exp (400 * (q : ℝ) ^ 2) *
                Real.exp (-84 * u ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hbasepow :
            ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8) =
              ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
                (1 + |u|) ^ (4 * q + 8) := by
          rw [mul_pow]
        calc
          ‖hughesYoungActiveHighPairRemainder q a b R K t u‖ ≤
              ‖hughesYoungRightContourWeight t (2 * q) u‖ *
                (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
                hughesYoungReferenceDivisorPairMass η := htail
          _ ≤ (160000 * (2 * (q : ℝ) + 1) ^ 8 *
                Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) *
                ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8) *
                (1 + |u|) ^ 8) *
                (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
                hughesYoungReferenceDivisorPairMass η := by
              gcongr
              exact hughesYoungReferenceDivisorPairMass_nonneg η
          _ = (C * K₀) * g u := by
              rw [hexp, hbasepow]
              unfold C K₀ g
              ring
      · exact hg.const_mul (C * K₀)
    _ = (C * K₀) * (∫ u in -H..H, g u) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (C * K₀) * L :=
      mul_le_mul_of_nonneg_left (hmoment hH)
        (mul_nonneg hC0 hK₀.le)
    _ = C * (K₀ * L) := by ring
    _ = _ := by rfl

theorem exists_norm_hughesYoungActiveWholeHighRemainder_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ {a b R K : ℕ} {T t : ℝ},
      0 < a → 0 < b → 0 < R →
      ((a * b * R : ℕ) : ℝ) ≤ hughesYoungDyadicRatio ^ (K + 1) →
      1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) →
      ‖hughesYoungActiveWholeHighRemainder q a b R K t‖ ≤
        (256 * Real.exp (400 * (q : ℝ) ^ 2) *
          ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
          (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
          hughesYoungReferenceDivisorPairMass η) * L := by
  obtain ⟨L, hL, hfinite⟩ :=
    exists_norm_hughesYoungActiveIntegratedRemainder_le q hq η hη0 hη
  refine ⟨L, hL, ?_⟩
  intro a b R K T t ha hb hR hcover hT ht
  let B : ℝ :=
    (256 * Real.exp (400 * (q : ℝ) ^ 2) *
      ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
      (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
      hughesYoungReferenceDivisorPairMass η) * L
  have hlim := (tendsto_hughesYoungActiveIntegratedRemainder
    hq ha hb hR hcover η hη0 hη hT ht).norm
  have hevent : ∀ᶠ H : ℝ in atTop,
      ‖hughesYoungActiveIntegratedRemainder q a b R K t H‖ ≤ B := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    exact hfinite ha hb hR hcover hT ht hH
  have hclosed : IsClosed (Set.Iic B) := isClosed_Iic
  have hmem : ‖hughesYoungActiveWholeHighRemainder q a b R K t‖ ∈ Set.Iic B :=
    hclosed.mem_of_tendsto hlim hevent
  simpa only [B] using hmem

/-- The exact finite active contour identity after both vertical limits.
The only discarded part is the explicitly named high-product remainder. -/
theorem hughesYoungZetaProduct_eq_activeWholeSmall_add_remainder
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hTexp : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T)) :
    (Real.pi : ℂ) *
        (riemannZeta (afeCriticalPoint t) ^ 2 *
          riemannZeta (afeCriticalPoint (-t)) ^ 2) =
      hughesYoungActiveWholeSmall T a b R K t +
        hughesYoungActiveWholeHighRemainder q a b R K t := by
  have hT : (1 : ℝ) ≤ T := by linarith [Real.exp_one_gt_d9]
  have hfull := (tendsto_hughesYoungFiniteZetaProduct
      (c := 2 * (q : ℝ)) t (by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith)).const_mul (Real.pi : ℂ)
  have hactive := tendsto_hughesYoungActiveIntegratedHigh_to_wholeSmall
    hq hTexp ht a b R K
  have hrem := tendsto_hughesYoungActiveIntegratedRemainder
    hq ha hb hR hcover η hη0 hη hT ht
  have hsum := hactive.add hrem
  have heq : (fun H : ℝ =>
      (Real.pi : ℂ) * hughesYoungFiniteZetaProduct t (2 * q) H) =
      fun H : ℝ =>
        hughesYoungActiveIntegratedHigh q a b R K t H +
          hughesYoungActiveIntegratedRemainder q a b R K t H := by
    funext H
    rw [hughesYoungFiniteZetaProduct_even_eq_active_add_remainder hq ha hb]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hpi]
  rw [heq] at hfull
  exact tendsto_nhds_unique hfull hsum

end RiemannZeta.GuthMaynard
