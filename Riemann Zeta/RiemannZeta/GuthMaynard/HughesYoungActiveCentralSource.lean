import RiemannZeta.GuthMaynard.HughesYoungFiniteCentralSource

open Complex MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Active Hughes--Young central source

This module performs the equation-(83)-to-(85) reassembly on the actual
product-truncated dyadic family.  In particular, it does not first enlarge
the active family to a rectangular family and then estimate the resulting
central complement term by a triangle inequality.
-/

/-- The reduced Mellin weight obtained by summing exactly the active dyadic
boxes used by the finite Hughes--Young source. -/
noncomputable def hughesYoungActiveReassembledReducedMellinWeight
    (T t c u : ℝ) (h k a b R K : ℕ) (x y : ℝ) : ℂ :=
  ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
    hughesYoungFullDyadicReducedMellinWeight T t c u h k ij.1 ij.2 x y

/-- The smooth two-variable cutoff carried by the active dyadic family,
now evaluated on the continuous DFI central variables rather than only on
the original divisor lattice. -/
noncomputable def hughesYoungActiveContinuousDyadicWeight
    (a b R K : ℕ) (x y : ℝ) : ℝ :=
  ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
    hughesYoungFullDyadicCutoff ij.1 x *
      hughesYoungFullDyadicCutoff ij.2 y

/-- Exact factorization of the active reassembled Mellin source into its
common Mellin monomial and the genuine smooth product-truncation cutoff. -/
theorem hughesYoungActiveReassembledReducedMellinWeight_eq_scaled_powers
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b R K : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hughesYoungActiveReassembledReducedMellinWeight
        T t c u h k a b R K x y =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        (hughesYoungActiveContinuousDyadicWeight a b R K x y : ℂ) *
        (x : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (y : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) := by
  classical
  unfold hughesYoungActiveReassembledReducedMellinWeight
    hughesYoungActiveContinuousDyadicWeight
    hughesYoungFullDyadicReducedMellinWeight
  simp_rw [hughesYoungReducedLocalizedMellinWeight_eq_scaled_powers
    T t c u _ _ hh hk hx hy]
  push_cast
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij _hij
  unfold hughesYoungFullDyadicCutoff
  ring

/-- The signed central source formed from the active reassembled Mellin
weight, after all localized shift intervals have been enlarged to the one
common finite interval allowed by the retained dyadic depth. -/
noncomputable def hughesYoungActiveReassembledSignedCentralAtHeight
    (T t c u : ℝ) (h k a b R K : ℕ) : ℂ :=
  let B := hughesYoungFullDyadicBound (K + 1)
  ∑ r ∈ hughesYoungShiftInterval a b B B,
    if r = 0 then 0 else
      dfiSignedCentralSeries a b r
        (hughesYoungActiveReassembledReducedMellinWeight
          T t c u h k a b R K)

/-- At one nonzero shift, summing the cleaned DFI central series over the
actual active dyadic family is exactly the physical-height integral of the
active reassembled Mellin weight.  This is the linear, cancellation-
preserving step underlying Hughes--Young (83)--(85). -/
theorem sum_activeDyadicBoxes_signedCentral_cleaned_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) (R K : ℕ) :
    (∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
      dfiSignedCentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k r)) =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungActiveReassembledReducedMellinWeight
              T t c u h k a b R K) := by
  let S := hughesYoungActiveDyadicBoxes a b R K
  calc
    (∑ ij ∈ S,
        dfiSignedCentralSeries a b r
          (hughesYoungReducedCleanedShiftWeight T c u
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k r)) =
        ∑ ij ∈ S, (1 / (T : ℂ)) * ∫ t : ℝ,
          (hughesYoungHeightWeight T t : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungFullDyadicReducedMellinWeight
                T t c u h k ij.1 ij.2) := by
      apply Finset.sum_congr rfl
      intro ij _hij
      exact dfiSignedCentralSeries_reducedCleaned_eq_heightIntegral_positiveScale
        hT hc u (hughesYoungFullDyadicScale_pos ij.1)
          (hughesYoungFullDyadicScale_pos ij.2) hh hk ha hb hr
    _ = (1 / (T : ℂ)) * ∑ ij ∈ S, ∫ t : ℝ,
          (hughesYoungHeightWeight T t : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungFullDyadicReducedMellinWeight
                T t c u h k ij.1 ij.2) := by
      rw [Finset.mul_sum]
    _ = (1 / (T : ℂ)) * ∫ t : ℝ, ∑ ij ∈ S,
          (hughesYoungHeightWeight T t : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungFullDyadicReducedMellinWeight
                T t c u h k ij.1 ij.2) := by
      congr 1
      symm
      apply MeasureTheory.integral_finsetSum
      intro ij _hij
      exact integrable_heightWeight_mul_dfiSignedCentralSeries_positiveScale
        hT hc u (hughesYoungFullDyadicScale_pos ij.1)
          (hughesYoungFullDyadicScale_pos ij.2) hh hk ha hb hr
    _ = (1 / (T : ℂ)) * ∫ t : ℝ,
          (hughesYoungHeightWeight T t : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungActiveReassembledReducedMellinWeight
                T t c u h k a b R K) := by
      apply congrArg ((1 / (T : ℂ)) * ·)
      apply integral_congr_ae
      filter_upwards with t
      have hreassemble :=
        heightWeight_mul_dfiSignedCentralSeries_fullDyadic_finsetSum
          hT hc u t hh hk ha hb hr S
      rw [← hreassemble]
      congr 2

/-- Every active localized central box may be enlarged to the common shift
interval determined by the retained dyadic depth. -/
theorem hughesYoungFiniteCompleteSignedCentralBox_eq_activeCommonInterval
    (T c u : ℝ) {h k a b R K : ℕ} (ha : 0 < a) (hb : 0 < b)
    {ij : ℕ × ℕ} (hij : ij ∈ hughesYoungActiveDyadicBoxes a b R K) :
    hughesYoungFiniteCompleteSignedCentralBox T c u
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k a b
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2) =
      ∑ r ∈ hughesYoungShiftInterval a b
          (hughesYoungFullDyadicBound (K + 1))
          (hughesYoungFullDyadicBound (K + 1)),
        if r = 0 then 0 else
          dfiSignedCentralSeries a b r
            (hughesYoungReducedCleanedShiftWeight T c u
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k r) := by
  have hij' : ij ∈ (Finset.range (K + 2)).product
      (Finset.range (K + 2)) :=
    (Finset.mem_filter.mp hij).1
  have hi : ij.1 < K + 2 :=
    Finset.mem_range.mp (Finset.mem_product.mp hij').1
  have hj : ij.2 < K + 2 :=
    Finset.mem_range.mp (Finset.mem_product.mp hij').2
  exact hughesYoungFiniteCompleteSignedCentralBox_eq_enlarged
    T c u (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) h k a b
      (hughesYoungFullDyadicBound ij.1)
      (hughesYoungFullDyadicBound ij.2)
      (hughesYoungFullDyadicBound (K + 1))
      (hughesYoungFullDyadicScale_pos ij.1)
      (hughesYoungFullDyadicScale_pos ij.2) ha hb
      (two_mul_hughesYoungFullDyadicScale_le_bound ij.1)
      (two_mul_hughesYoungFullDyadicScale_le_bound ij.2)
      (hughesYoungFullDyadicBound_le_terminal hi)
      (hughesYoungFullDyadicBound_le_terminal hj)

/-- Exact active-family source theorem at a fixed Mellin ordinate: the sum
of literal finite complete DFI central boxes is the physical-height integral
of one signed central source carrying the active reassembled weight. -/
theorem sum_activeDyadicBoxes_finiteCompleteBox_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (R K : ℕ) :
    (∑ ij ∈ hughesYoungActiveDyadicBoxes
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      hughesYoungFiniteCompleteSignedCentralBox T c u
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2)) =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungActiveReassembledSignedCentralAtHeight
            T t c u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K := by
  classical
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let S := hughesYoungActiveDyadicBoxes a b R K
  let B := hughesYoungFullDyadicBound (K + 1)
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hIntReassembled (r : ℤ) (hr : r ≠ 0) :
      Integrable (fun t : ℝ =>
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungActiveReassembledReducedMellinWeight
              T t c u h k a b R K)) := by
    have hsum : Integrable (fun t : ℝ => ∑ ij ∈ S,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungFullDyadicReducedMellinWeight
              T t c u h k ij.1 ij.2)) := by
      exact integrable_finsetSum S (fun ij _hij =>
        integrable_heightWeight_mul_dfiSignedCentralSeries_positiveScale
          hT hc u (hughesYoungFullDyadicScale_pos ij.1)
            (hughesYoungFullDyadicScale_pos ij.2) hh hk ha hb hr)
    refine hsum.congr ?_
    filter_upwards with t
    have hreassemble :=
      heightWeight_mul_dfiSignedCentralSeries_fullDyadic_finsetSum
        hT hc u t hh hk ha hb hr S
    rw [← hreassemble]
    congr 2
  calc
    (∑ ij ∈ S,
        hughesYoungFiniteCompleteSignedCentralBox T c u
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k a b
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)) =
        ∑ ij ∈ S, ∑ r ∈ hughesYoungShiftInterval a b B B,
          if r = 0 then 0 else
            dfiSignedCentralSeries a b r
              (hughesYoungReducedCleanedShiftWeight T c u
                (hughesYoungFullDyadicScale ij.1)
                (hughesYoungFullDyadicScale ij.2) h k r) := by
      apply Finset.sum_congr rfl
      intro ij hij
      exact hughesYoungFiniteCompleteSignedCentralBox_eq_activeCommonInterval
        T c u ha hb hij
    _ = ∑ r ∈ hughesYoungShiftInterval a b B B, ∑ ij ∈ S,
          if r = 0 then 0 else
            dfiSignedCentralSeries a b r
              (hughesYoungReducedCleanedShiftWeight T c u
                (hughesYoungFullDyadicScale ij.1)
                (hughesYoungFullDyadicScale ij.2) h k r) := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ hughesYoungShiftInterval a b B B,
          if r = 0 then 0 else
            (1 / (T : ℂ)) * ∫ t : ℝ,
              (hughesYoungHeightWeight T t : ℂ) *
                dfiSignedCentralSeries a b r
                  (hughesYoungActiveReassembledReducedMellinWeight
                    T t c u h k a b R K) := by
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hr0 : r = 0
      · simp [hr0]
      · simp only [hr0, if_false]
        exact sum_activeDyadicBoxes_signedCentral_cleaned_eq_heightIntegral
          hT hc u hh hk ha hb hr0 R K
    _ = (1 / (T : ℂ)) * ∑ r ∈ hughesYoungShiftInterval a b B B,
          if r = 0 then 0 else ∫ t : ℝ,
            (hughesYoungHeightWeight T t : ℂ) *
              dfiSignedCentralSeries a b r
                (hughesYoungActiveReassembledReducedMellinWeight
                  T t c u h k a b R K) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hr0 : r = 0 <;> simp [hr0]
    _ = (1 / (T : ℂ)) * ∫ t : ℝ,
          ∑ r ∈ hughesYoungShiftInterval a b B B,
            if r = 0 then 0 else
              (hughesYoungHeightWeight T t : ℂ) *
                dfiSignedCentralSeries a b r
                  (hughesYoungActiveReassembledReducedMellinWeight
                    T t c u h k a b R K) := by
      congr 1
      rw [MeasureTheory.integral_finsetSum
        (hughesYoungShiftInterval a b B B)]
      · apply Finset.sum_congr rfl
        intro r _hr
        by_cases hr0 : r = 0 <;> simp [hr0]
      · intro r _hr
        by_cases hr0 : r = 0
        · simp [hr0]
        · simpa only [hr0, if_false] using hIntReassembled r hr0
    _ = (1 / (T : ℂ)) * ∫ t : ℝ,
          (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungActiveReassembledSignedCentralAtHeight
              T t c u h k a b R K := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      unfold hughesYoungActiveReassembledSignedCentralAtHeight
      simp only [B, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hr0 : r = 0 <;> simp [hr0]

/-- Joint continuity of one nonzero shift after reassembling exactly the
active dyadic family. -/
theorem continuousOn_heightWeight_mul_dfiSignedCentralSeries_activeReassembled
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) (R K : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungActiveReassembledReducedMellinWeight
            T p.2 c p.1 h k a b R K))
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
  let S := hughesYoungActiveDyadicBoxes a b R K
  have hsum : ContinuousOn (fun p : ℝ × ℝ =>
      ∑ ij ∈ S, (hughesYoungHeightWeight T p.2 : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungFullDyadicReducedMellinWeight
            T p.2 c p.1 h k ij.1 ij.2))
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
    exact continuousOn_finsetSum S fun ij _hij =>
      continuousOn_heightWeight_mul_dfiSignedCentralSeries_ordinate_height
        hT hc H
          (hughesYoungFullDyadicScale_pos ij.1)
          (hughesYoungFullDyadicScale_pos ij.2)
          hh hk ha hb hr
  refine hsum.congr ?_
  intro p _hp
  have hreassemble :=
    heightWeight_mul_dfiSignedCentralSeries_fullDyadic_finsetSum
      hT hc p.1 p.2 hh hk ha hb hr S
  simpa only [S, hughesYoungActiveReassembledReducedMellinWeight] using
    hreassemble

/-- The complete signed active source is jointly continuous on the compact
Mellin-ordinate/physical-height rectangle. -/
theorem continuousOn_heightWeight_mul_hughesYoungActiveReassembledSignedCentralAtHeight
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (R K : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        hughesYoungActiveReassembledSignedCentralAtHeight
          T p.2 c p.1 h k a b R K)
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
  let B := hughesYoungFullDyadicBound (K + 1)
  have hsum : ContinuousOn (fun p : ℝ × ℝ =>
      ∑ r ∈ hughesYoungShiftInterval a b B B,
        if r = 0 then 0 else
          (hughesYoungHeightWeight T p.2 : ℂ) *
            dfiSignedCentralSeries a b r
              (hughesYoungActiveReassembledReducedMellinWeight
                T p.2 c p.1 h k a b R K))
      (Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)) := by
    apply continuousOn_finsetSum (hughesYoungShiftInterval a b B B)
    intro r _hr
    by_cases hr0 : r = 0
    · subst r
      simp only [if_pos]
      exact continuousOn_const
    · simp only [hr0, if_false]
      exact
        continuousOn_heightWeight_mul_dfiSignedCentralSeries_activeReassembled
          hT hc H hh hk ha hb hr0 R K
  refine hsum.congr ?_
  intro p _hp
  unfold hughesYoungActiveReassembledSignedCentralAtHeight
  simp only [B, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hr0 : r = 0 <;> simp [hr0]

/-- The cancellation-preserving active source is integrable on the bounded
Mellin ordinate and the full physical-height line. -/
theorem integrable_uncurry_heightWeight_mul_hughesYoungActiveReassembledSignedCentralAtHeight
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    {H : ℝ} (hH : 0 ≤ H)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (R K : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        hughesYoungActiveReassembledSignedCentralAtHeight
          T p.2 c p.1 h k
            (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) R K)
      ((volume.restrict (Set.uIoc (-H) H)).prod volume) := by
  let f : ℝ × ℝ → ℂ := fun p =>
    (hughesYoungHeightWeight T p.2 : ℂ) *
      hughesYoungActiveReassembledSignedCentralAtHeight
        T p.2 c p.1 h k
          (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) R K
  let C : Set (ℝ × ℝ) :=
    Set.Icc (-H) H ×ˢ Set.Icc (T / 4) (4 * T)
  have hcontinuous : ContinuousOn f C := by
    dsimp only [f, C]
    exact
      continuousOn_heightWeight_mul_hughesYoungActiveReassembledSignedCentralAtHeight
        hT hc H hh hk (hughesYoungReducedLeft_pos hh)
          (hughesYoungReducedRight_pos hh hk) R K
  have hsmall : IntegrableOn f C (volume.prod volume) :=
    hcontinuous.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hbig : IntegrableOn f
      (Set.uIoc (-H) H ×ˢ Set.univ) (volume.prod volume) := by
    apply hsmall.of_forall_diff_eq_zero
      (measurableSet_uIoc.prod MeasurableSet.univ)
    intro p hp
    have ht : p.2 ∉ Set.Icc (T / 4) (4 * T) := by
      intro hp2
      apply hp.2
      have hp1 : p.1 ∈ Set.Icc (-H) H := by
        have hu := Set.uIoc_subset_uIcc hp.1.1
        simpa only [Set.uIcc_of_le (by linarith : -H ≤ H)] using hu
      exact ⟨hp1, hp2⟩
    have hzero : hughesYoungHeightWeight T p.2 = 0 := by
      by_contra hne
      exact ht (hughesYoungHeightWeight_support hT hne)
    dsimp only [f]
    simp [hzero]
  rw [IntegrableOn, ← Measure.prod_restrict] at hbig
  simpa [f] using hbig

/-- Fubini for the active cancellation-preserving source. -/
theorem intervalIntegral_integral_hughesYoungActiveReassembledSignedCentralAtHeight_swap
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    {H : ℝ} (hH : 0 ≤ H)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (R K : ℕ) :
    (∫ u in -H..H, ∫ t : ℝ,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungActiveReassembledSignedCentralAtHeight
          T t c u h k
            (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) R K) =
      ∫ t : ℝ, ∫ u in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungActiveReassembledSignedCentralAtHeight
            T t c u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K := by
  exact intervalIntegral_integral_swap
    (integrable_uncurry_heightWeight_mul_hughesYoungActiveReassembledSignedCentralAtHeight
      hT hc hH hh hk R K)

/-- The active complete-box family is the compact Mellin integral of the
corresponding finite cleaned central boxes. -/
theorem sum_activeDyadicBoxes_integratedCompleteCentral_eq_intervalIntegral_sum
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    {H : ℝ} (hH : 0 ≤ H)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (R K : ℕ) :
    (∑ ij ∈ hughesYoungActiveDyadicBoxes
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      hughesYoungIntegratedFiniteCompleteSignedCentralBox T c H
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2)) =
      ∫ u in -H..H,
        ∑ ij ∈ hughesYoungActiveDyadicBoxes
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          (T : ℂ) * hughesYoungFiniteCompleteSignedCentralBox T c u
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2) := by
  classical
  unfold hughesYoungIntegratedFiniteCompleteSignedCentralBox
  symm
  rw [intervalIntegral.integral_finsetSum]
  intro ij _hij
  exact
    intervalIntegrable_mul_hughesYoungFiniteCompleteSignedCentralBox_positiveScale
      hT hc hH
        (hughesYoungFullDyadicScale_pos ij.1)
        (hughesYoungFullDyadicScale_pos ij.2)
        hh hk (hughesYoungReducedLeft_pos hh)
          (hughesYoungReducedRight_pos hh hk)

/-- Active-family Hughes--Young equation (85): after the compact Mellin
integration, the actual product-truncated dyadic central family is exactly
one cancellation-preserving height/Mellin source. -/
theorem sum_activeDyadicBoxes_integratedCompleteCentral_eq_source
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    {H : ℝ} (hH : 0 ≤ H)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (R K : ℕ) :
    (∑ ij ∈ hughesYoungActiveDyadicBoxes
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      hughesYoungIntegratedFiniteCompleteSignedCentralBox T c H
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2)) =
      ∫ t : ℝ, ∫ u in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungActiveReassembledSignedCentralAtHeight
            T t c u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K := by
  let S := hughesYoungActiveDyadicBoxes
    (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K
  rw [sum_activeDyadicBoxes_integratedCompleteCentral_eq_intervalIntegral_sum
    hT hc hH hh hk R K]
  calc
    (∫ u in -H..H,
        ∑ ij ∈ S,
          (T : ℂ) * hughesYoungFiniteCompleteSignedCentralBox T c u
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2)) =
        ∫ u in -H..H, (T : ℂ) *
          (∑ ij ∈ S,
            hughesYoungFiniteCompleteSignedCentralBox T c u
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      exact (Finset.mul_sum _ _ _).symm
    _ = (T : ℂ) * (∫ u in -H..H,
          ∑ ij ∈ S,
            hughesYoungFiniteCompleteSignedCentralBox T c u
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (T : ℂ) * (∫ u in -H..H,
          (1 / (T : ℂ)) * ∫ t : ℝ,
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungActiveReassembledSignedCentralAtHeight
                T t c u h k
                  (hughesYoungReducedLeft h k)
                  (hughesYoungReducedRight h k) R K) := by
      apply congrArg ((T : ℂ) * ·)
      apply intervalIntegral.integral_congr
      intro u _hu
      exact sum_activeDyadicBoxes_finiteCompleteBox_eq_heightIntegral
        hT hc u hh hk R K
    _ = (T : ℂ) * ((1 / (T : ℂ)) *
          ∫ u in -H..H, ∫ t : ℝ,
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungActiveReassembledSignedCentralAtHeight
                T t c u h k
                  (hughesYoungReducedLeft h k)
                  (hughesYoungReducedRight h k) R K) := by
      congr 1
      rw [intervalIntegral.integral_const_mul]
    _ = (T : ℂ) * ((1 / (T : ℂ)) *
          ∫ t : ℝ, ∫ u in -H..H,
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungActiveReassembledSignedCentralAtHeight
                T t c u h k
                  (hughesYoungReducedLeft h k)
                  (hughesYoungReducedRight h k) R K) := by
      rw [intervalIntegral_integral_hughesYoungActiveReassembledSignedCentralAtHeight_swap
        hT hc hH hh hk R K]
    _ = _ := by
      have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
      field_simp

/-- Global active-family equation (85) for the mollifier variables used in
the native Hughes--Young chain. -/
theorem hughesYoungActiveIntegratedCompleteCentral_eq_activeSource
    {T : ℝ} (hT : Real.exp 1 ≤ T) (R K : ℕ) :
    hughesYoungActiveIntegratedCompleteCentral T R K =
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∫ t : ℝ, ∫ u in -(T / 8)..T / 8,
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungActiveReassembledSignedCentralAtHeight
                T t (hughesYoungSmallContour T) u h k
                  (hughesYoungReducedLeft h k)
                  (hughesYoungReducedRight h k) R K := by
  classical
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hH : 0 ≤ T / 8 := div_nonneg hTpos.le (by norm_num)
  have hc : 0 < hughesYoungSmallContour T :=
    (hughesYoungSmallContour_spec hT).1
  unfold hughesYoungActiveIntegratedCompleteCentral
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  have hhpos : 0 < h := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hh).1
  have hkpos : 0 < k := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hk).1
  exact sum_activeDyadicBoxes_integratedCompleteCentral_eq_source
    hTpos hc hH hhpos hkpos R K

end RiemannZeta.GuthMaynard
