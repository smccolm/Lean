import RiemannZeta.GuthMaynard.LargeValuesEnergy

/-!
# Guth--Maynard Section 11: final gcd summation

This file completes the passage from the exact gcd slices in
`LargeValuesEnergy` to Lemma 11.9 and Propositions 11.1--11.2.  The one-point
enlargement below is the exact correction forced by replacing the real scale
`N / d` by the natural scale `N / d`.
-/

open scoped BigOperators Real
open MeasureTheory

namespace RiemannZeta.GuthMaynard

/-- The `gmDyadicIntervalPlus` definition used by the source-facing construction in `LargeValuesEnergyFinal`. -/
def gmDyadicIntervalPlus (M : ℕ) : Finset ℕ :=
  Finset.Ioc M (2 * M + 1)

theorem gmDyadicIntervalPlus_eq_insert (M : ℕ) :
    gmDyadicIntervalPlus M = insert (2 * M + 1) (dyadicInterval M) := by
  ext n
  simp only [gmDyadicIntervalPlus, dyadicInterval, Finset.mem_Ioc,
    Finset.mem_insert]
  omega

/-- The `gmDyadicPlusRatioMoment` definition used by the source-facing construction in `LargeValuesEnergyFinal`. -/
noncomputable def gmDyadicPlusRatioMoment
    (k M : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ nm ∈ gmDyadicIntervalPlus M ×ˢ gmDyadicIntervalPlus M,
    ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ k

theorem gmDyadicInterval_card (M : ℕ) : (dyadicInterval M).card = M := by
  rw [dyadicInterval, Nat.card_Ioc]
  omega

theorem gmR_ratio_pow_le_card_pow
    (k : ℕ) (W : Finset ℝ) (n m : ℕ) :
    ‖gmR W ((n : ℝ) / m)‖ ^ k ≤ (W.card : ℝ) ^ k := by
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gmR_le_card_all W _) k

/-- Adding the possible endpoint `2M+1` costs only two rows and the corner,
not a full extra dyadic square. -/
theorem gmDyadicPlusRatioMoment_le
    (k M : ℕ) (W : Finset ℝ) :
    gmDyadicPlusRatioMoment k M W ≤
      gmDiscreteRatioMoment k M W +
        (2 * (M : ℝ) + 1) * (W.card : ℝ) ^ k := by
  classical
  let e := 2 * M + 1
  let S := dyadicInterval M
  have he : e ∉ S := by
    dsimp only [e, S, dyadicInterval]
    simp
  have hrow :
      (∑ m ∈ S, ‖gmR W ((e : ℝ) / m)‖ ^ k) ≤
        (M : ℝ) * (W.card : ℝ) ^ k := by
    calc
      (∑ m ∈ S, ‖gmR W ((e : ℝ) / m)‖ ^ k) ≤
          ∑ _m ∈ S, (W.card : ℝ) ^ k := by
        exact Finset.sum_le_sum fun m hm => gmR_ratio_pow_le_card_pow k W e m
      _ = (M : ℝ) * (W.card : ℝ) ^ k := by
        simp [S, gmDyadicInterval_card]
  have hcol :
      (∑ n ∈ S, ‖gmR W ((n : ℝ) / e)‖ ^ k) ≤
        (M : ℝ) * (W.card : ℝ) ^ k := by
    calc
      (∑ n ∈ S, ‖gmR W ((n : ℝ) / e)‖ ^ k) ≤
          ∑ _n ∈ S, (W.card : ℝ) ^ k := by
        exact Finset.sum_le_sum fun n hn => gmR_ratio_pow_le_card_pow k W n e
      _ = (M : ℝ) * (W.card : ℝ) ^ k := by
        simp [S, gmDyadicInterval_card]
  have hcorner : ‖gmR W ((e : ℝ) / e)‖ ^ k ≤ (W.card : ℝ) ^ k :=
    gmR_ratio_pow_le_card_pow k W e e
  rw [gmDyadicPlusRatioMoment, gmDyadicIntervalPlus_eq_insert,
    Finset.sum_product]
  change
    (∑ n ∈ insert e S, ∑ m ∈ insert e S,
      ‖gmR W ((n : ℝ) / m)‖ ^ k) ≤ _
  rw [Finset.sum_insert he]
  simp_rw [Finset.sum_insert he]
  change
    (‖gmR W ((e : ℝ) / e)‖ ^ k +
        ∑ m ∈ S, ‖gmR W ((e : ℝ) / m)‖ ^ k) +
      (∑ n ∈ S, (‖gmR W ((n : ℝ) / e)‖ ^ k +
        ∑ m ∈ S, ‖gmR W ((n : ℝ) / m)‖ ^ k)) ≤ _
  rw [Finset.sum_add_distrib]
  have hmain :
      (∑ n ∈ S, ∑ m ∈ S, ‖gmR W ((n : ℝ) / m)‖ ^ k) =
        gmDiscreteRatioMoment k M W := by
    rw [gmDiscreteRatioMoment_eq_iterated]
  rw [hmain]
  nlinarith

theorem gmReducedRatioPair_mem_plus
    {N d : ℕ} (hd : 0 < d)
    {p : ℕ × ℕ} (hp : p ∈ gmReducedRatioPairs N d) :
    p.1 ∈ gmDyadicIntervalPlus (N / d) ∧
      p.2 ∈ gmDyadicIntervalPlus (N / d) := by
  have hpCond := (Finset.mem_filter.mp hp).2
  have hmod : N % d < d := Nat.mod_lt N hd
  have hdecomp : N % d + d * (N / d) = N := Nat.mod_add_div N d
  have htwomod : 2 * (N % d) < 2 * d :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hmod
  have hupper : 2 * N / d ≤ 2 * (N / d) + 1 := by
    apply Nat.lt_succ_iff.mp
    apply (Nat.div_lt_iff_lt_mul hd).2
    calc
      2 * N = 2 * (N % d + d * (N / d)) := by rw [hdecomp]
      _ = 2 * (N % d) + 2 * (d * (N / d)) := by ring
      _ < 2 * d + 2 * (d * (N / d)) := Nat.add_lt_add_right htwomod _
      _ = (2 * (N / d) + 1 + 1) * d := by ring
  constructor <;> rw [gmDyadicIntervalPlus, Finset.mem_Ioc]
  · constructor
    · exact (Nat.div_lt_iff_lt_mul hd).2 (by simpa [Nat.mul_comm] using hpCond.1)
    · have ha : p.1 ≤ 2 * N / d :=
        (Nat.le_div_iff_mul_le hd).2 (by simpa [Nat.mul_comm] using hpCond.2.1)
      exact ha.trans hupper
  · constructor
    · exact (Nat.div_lt_iff_lt_mul hd).2
        (by simpa [Nat.mul_comm] using hpCond.2.2.1)
    · have ha : p.2 ≤ 2 * N / d :=
        (Nat.le_div_iff_mul_le hd).2
          (by simpa [Nat.mul_comm] using hpCond.2.2.2.1)
      exact ha.trans hupper

theorem gmReducedRatioMoment_le_plus
    (k N d : ℕ) (W : Finset ℝ) (hd : 0 < d) :
    gmReducedRatioMoment k N d W ≤
      gmDyadicPlusRatioMoment k (N / d) W := by
  classical
  unfold gmReducedRatioMoment gmDyadicPlusRatioMoment
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Finset.mem_product]
    exact gmReducedRatioPair_mem_plus hd hp
  · intro p hp hnot
    positivity

/-- The `gmSecondMomentShape` definition used by the source-facing construction in `LargeValuesEnergyFinal`. -/
noncomputable def gmSecondMomentShape
    (M : ℕ) (T : ℝ) (W : Finset ℝ) : ℝ :=
  (W.card : ℝ) ^ 2 * M +
    (W.card : ℝ) * M ^ 2 +
    (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * M

/-- The `gmFourthMomentShape` definition used by the source-facing construction in `LargeValuesEnergyFinal`. -/
noncomputable def gmFourthMomentShape
    (M : ℕ) (T : ℝ) (W : Finset ℝ) : ℝ :=
  (W.card : ℝ) ^ 4 * M +
    (ApproxAddEnergy 1 W : ℝ) * M ^ 2 +
    (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
      (W.card : ℝ) * T ^ (1 / 2 : ℝ) * M

theorem gmSecondMomentShape_nonneg
    {M : ℕ} {T : ℝ} {W : Finset ℝ} (hT : 0 ≤ T) :
    0 ≤ gmSecondMomentShape M T W := by
  unfold gmSecondMomentShape
  positivity

theorem gmFourthMomentShape_nonneg
    {M : ℕ} {T : ℝ} {W : Finset ℝ} (hT : 0 ≤ T) :
    0 ≤ gmFourthMomentShape M T W := by
  unfold gmFourthMomentShape
  positivity

theorem gmDyadicPlusSecondMoment_native
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → IsSeparated 1 W → InBaseInterval T W →
        gmDyadicPlusRatioMoment 2 M W ≤
          C * T ^ ε * gmSecondMomentShape M T W := by
  obtain ⟨C₀, T₀, hC₀, hT₀, hbase⟩ :=
    gmDiscreteRatioSecondMoment_native ε hε
  let C := C₀ + 3
  refine ⟨C, T₀, by dsimp only [C]; positivity, hT₀, ?_⟩
  intro M T W hM hT hSep hBase
  have hTOne : 1 ≤ T := hT₀.trans hT
  have hPowOne : 1 ≤ T ^ ε := Real.one_le_rpow hTOne hε.le
  have hMOne : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hEnd :
      (2 * (M : ℝ) + 1) * (W.card : ℝ) ^ 2 ≤
        3 * gmSecondMomentShape M T W := by
    have hFirst : (M : ℝ) * (W.card : ℝ) ^ 2 ≤
        gmSecondMomentShape M T W := by
      unfold gmSecondMomentShape
      have h₂ : 0 ≤ (W.card : ℝ) * (M : ℝ) ^ 2 := by positivity
      have h₃ : 0 ≤ (W.card : ℝ) ^ (5 / 4 : ℝ) *
          T ^ (1 / 2 : ℝ) * (M : ℝ) := by positivity
      nlinarith
    have hcoef : 2 * (M : ℝ) + 1 ≤ 3 * M := by linarith
    calc
      (2 * (M : ℝ) + 1) * (W.card : ℝ) ^ 2 ≤
          (3 * (M : ℝ)) * (W.card : ℝ) ^ 2 := by gcongr
      _ ≤ 3 * gmSecondMomentShape M T W := by nlinarith
  have hRaw := gmDyadicPlusRatioMoment_le 2 M W
  have hBaseAt : gmDiscreteRatioMoment 2 M W ≤
      C₀ * T ^ ε * gmSecondMomentShape M T W := by
    simpa only [gmSecondMomentShape] using hbase M T W hM hT hSep hBase
  have hShape0 := gmSecondMomentShape_nonneg (M := M) (W := W)
    (zero_le_one.trans hTOne)
  calc
    gmDyadicPlusRatioMoment 2 M W ≤
        gmDiscreteRatioMoment 2 M W +
          (2 * (M : ℝ) + 1) * (W.card : ℝ) ^ 2 := hRaw
    _ ≤ C₀ * T ^ ε * gmSecondMomentShape M T W +
          3 * gmSecondMomentShape M T W := add_le_add hBaseAt hEnd
    _ ≤ (C₀ + 3) * T ^ ε * gmSecondMomentShape M T W := by
      nlinarith [mul_nonneg hC₀.le
        (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hTOne) ε) hShape0)]
    _ = C * T ^ ε * gmSecondMomentShape M T W := rfl

theorem gmDyadicPlusFourthMoment_native
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        gmDyadicPlusRatioMoment 4 M W ≤
          C * T ^ ε * gmFourthMomentShape M T W := by
  obtain ⟨C₀, T₀, hC₀, hT₀, hbase⟩ :=
    gmDiscreteFourthMoment_native ε hε
  let C := C₀ + 3
  refine ⟨C, T₀, by dsimp only [C]; positivity, hT₀, ?_⟩
  intro M T W hM hT hMT hSep hBase
  have hTOne : 1 ≤ T := hT₀.trans hT
  have hPowOne : 1 ≤ T ^ ε := Real.one_le_rpow hTOne hε.le
  have hMOne : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hEnd :
      (2 * (M : ℝ) + 1) * (W.card : ℝ) ^ 4 ≤
        3 * gmFourthMomentShape M T W := by
    have hFirst : (M : ℝ) * (W.card : ℝ) ^ 4 ≤
        gmFourthMomentShape M T W := by
      unfold gmFourthMomentShape
      have h₂ : 0 ≤ (ApproxAddEnergy 1 W : ℝ) * (M : ℝ) ^ 2 := by positivity
      have h₃ : 0 ≤ (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
          (W.card : ℝ) * T ^ (1 / 2 : ℝ) * (M : ℝ) := by positivity
      nlinarith
    have hcoef : 2 * (M : ℝ) + 1 ≤ 3 * M := by linarith
    calc
      (2 * (M : ℝ) + 1) * (W.card : ℝ) ^ 4 ≤
          (3 * (M : ℝ)) * (W.card : ℝ) ^ 4 := by gcongr
      _ ≤ 3 * gmFourthMomentShape M T W := by nlinarith
  have hRaw := gmDyadicPlusRatioMoment_le 4 M W
  have hBaseAt : gmDiscreteRatioMoment 4 M W ≤
      C₀ * T ^ ε * gmFourthMomentShape M T W := by
    simpa only [gmFourthMomentShape] using hbase M T W hM hT hMT hSep hBase
  have hShape0 := gmFourthMomentShape_nonneg (M := M) (W := W)
    (zero_le_one.trans hTOne)
  calc
    gmDyadicPlusRatioMoment 4 M W ≤
        gmDiscreteRatioMoment 4 M W +
          (2 * (M : ℝ) + 1) * (W.card : ℝ) ^ 4 := hRaw
    _ ≤ C₀ * T ^ ε * gmFourthMomentShape M T W +
          3 * gmFourthMomentShape M T W := add_le_add hBaseAt hEnd
    _ ≤ (C₀ + 3) * T ^ ε * gmFourthMomentShape M T W := by
      nlinarith [mul_nonneg hC₀.le
        (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hTOne) ε) hShape0)]
    _ = C * T ^ ε * gmFourthMomentShape M T W := rfl

/-! ### Reciprocal-scale summation for Lemma 11.9 -/

/-- The exact finite telescoping identity behind the large-gcd square sum. -/
theorem sum_Icc_inv_sub_inv_succ
    {D U : ℕ} (hDU : D ≤ U) :
    (∑ d ∈ Finset.Icc D U,
        ((1 : ℝ) / (d : ℝ) - 1 / ((d + 1 : ℕ) : ℝ))) =
      1 / (D : ℝ) - 1 / ((U + 1 : ℕ) : ℝ) := by
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have hLen : D + (U + 1 - D) = U + 1 := by omega
  have htel := Finset.sum_range_sub'
    (fun i : ℕ => (1 : ℝ) / ((D + i : ℕ) : ℝ)) (U + 1 - D)
  change
    (∑ i ∈ Finset.range (U + 1 - D),
        ((1 : ℝ) / ((D + i : ℕ) : ℝ) -
          1 / ((D + i + 1 : ℕ) : ℝ))) =
      1 / (D : ℝ) - 1 / ((U + 1 : ℕ) : ℝ)
  simpa only [Nat.add_assoc, hLen] using htel

/-- The reciprocal-square mass of a finite tail is bounded by twice its
first reciprocal.  This is the finite form of the integral test used in
the `d ≥ D` summation in Guth--Maynard Lemma 11.9. -/
theorem sum_Icc_one_div_sq_tail_le
    {D U : ℕ} (hD : 0 < D) :
    (∑ d ∈ Finset.Icc D U, (1 : ℝ) / (d : ℝ) ^ 2) ≤
      2 / (D : ℝ) := by
  by_cases hDU : D ≤ U
  · have hpoint : ∀ d ∈ Finset.Icc D U,
        (1 : ℝ) / (d : ℝ) ^ 2 ≤
          2 * ((1 : ℝ) / (d : ℝ) - 1 / ((d + 1 : ℕ) : ℝ)) := by
      intro d hd
      have hdPos : (0 : ℝ) < d := by
        exact_mod_cast hD.trans_le (Finset.mem_Icc.mp hd).1
      have hdOne : (1 : ℝ) ≤ d := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (hD.trans_le (Finset.mem_Icc.mp hd).1))
      have hdsPos : (0 : ℝ) < d + 1 := by positivity
      push_cast
      field_simp [hdPos.ne', hdsPos.ne']
      nlinarith
    calc
      (∑ d ∈ Finset.Icc D U, (1 : ℝ) / (d : ℝ) ^ 2) ≤
          ∑ d ∈ Finset.Icc D U,
            2 * ((1 : ℝ) / (d : ℝ) -
              1 / ((d + 1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum hpoint
      _ = 2 * (1 / (D : ℝ) - 1 / ((U + 1 : ℕ) : ℝ)) := by
        rw [← Finset.mul_sum]
        congr 1
        exact sum_Icc_inv_sub_inv_succ hDU
      _ ≤ 2 / (D : ℝ) := by
        have : 0 ≤ (1 : ℝ) / ((U + 1 : ℕ) : ℝ) := by positivity
        calc
          2 * (1 / (D : ℝ) - 1 / ((U + 1 : ℕ) : ℝ)) ≤
              2 * (1 / (D : ℝ)) := by nlinarith
          _ = 2 / (D : ℝ) := by ring
  · rw [Finset.Icc_eq_empty hDU, Finset.sum_empty]
    positivity

/-- The natural quotient scale `N / d` has only a harmonic total mass. -/
theorem sum_Icc_natDiv_le_harmonic
    {N D : ℕ} (hD : 0 < D) :
    (∑ d ∈ Finset.Icc D N, ((N / d : ℕ) : ℝ)) ≤
      (N : ℝ) * (((harmonic N : ℚ) : ℝ)) := by
  have hsub : Finset.Icc D N ⊆ Finset.Icc 1 N := by
    intro d hd
    exact Finset.mem_Icc.mpr
      ⟨hD.trans_le (Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2⟩
  have hrecip :
      (∑ d ∈ Finset.Icc D N, (1 : ℝ) / (d : ℝ)) ≤
        (((harmonic N : ℚ) : ℝ)) := by
    calc
      (∑ d ∈ Finset.Icc D N, (1 : ℝ) / (d : ℝ)) ≤
          ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro d hd hdnot
        positivity
      _ = (((harmonic N : ℚ) : ℝ)) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        simp only [one_div]
  calc
    (∑ d ∈ Finset.Icc D N, ((N / d : ℕ) : ℝ)) ≤
        ∑ d ∈ Finset.Icc D N, (N : ℝ) / (d : ℝ) := by
      exact Finset.sum_le_sum fun d hd => Nat.cast_div_le
    _ = (N : ℝ) *
        (∑ d ∈ Finset.Icc D N, (1 : ℝ) / (d : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (N : ℝ) * (((harmonic N : ℚ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg N)

/-- Squared natural quotient scales have the sharp reciprocal-tail mass
needed after choosing `D` at size `N²/T`. -/
theorem sum_Icc_natDiv_sq_le
    {N D : ℕ} (hD : 0 < D) :
    (∑ d ∈ Finset.Icc D N, ((N / d : ℕ) : ℝ) ^ 2) ≤
      2 * (N : ℝ) ^ 2 / (D : ℝ) := by
  have htail := sum_Icc_one_div_sq_tail_le (D := D) (U := N) hD
  calc
    (∑ d ∈ Finset.Icc D N, ((N / d : ℕ) : ℝ) ^ 2) ≤
        ∑ d ∈ Finset.Icc D N,
          ((N : ℝ) / (d : ℝ)) ^ 2 := by
      exact Finset.sum_le_sum fun d hd =>
        pow_le_pow_left₀ (Nat.cast_nonneg (N / d)) Nat.cast_div_le 2
    _ = (N : ℝ) ^ 2 *
        (∑ d ∈ Finset.Icc D N, (1 : ℝ) / (d : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (N : ℝ) ^ 2 * (2 / (D : ℝ)) := by
      exact mul_le_mul_of_nonneg_left htail (sq_nonneg (N : ℝ))
    _ = 2 * (N : ℝ) ^ 2 / (D : ℝ) := by ring

/-- The `gmLargeSecondAggregateShape` definition used by the source-facing construction in `LargeValuesEnergyFinal`. -/
noncomputable def gmLargeSecondAggregateShape
    (N D : ℕ) (T : ℝ) (W : Finset ℝ) : ℝ :=
  (W.card : ℝ) ^ 2 * (N : ℝ) * (((harmonic N : ℚ) : ℝ)) +
    2 * (W.card : ℝ) * (N : ℝ) ^ 2 / (D : ℝ) +
    (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) *
      (N : ℝ) * (((harmonic N : ℚ) : ℝ))

/-- The `gmLargeFourthAggregateShape` definition used by the source-facing construction in `LargeValuesEnergyFinal`. -/
noncomputable def gmLargeFourthAggregateShape
    (N D : ℕ) (T : ℝ) (W : Finset ℝ) : ℝ :=
  (W.card : ℝ) ^ 4 * (N : ℝ) * (((harmonic N : ℚ) : ℝ)) +
    2 * (ApproxAddEnergy 1 W : ℝ) * (N : ℝ) ^ 2 / (D : ℝ) +
    (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
      (W.card : ℝ) * T ^ (1 / 2 : ℝ) *
      (N : ℝ) * (((harmonic N : ℚ) : ℝ))

theorem sum_gmSecondMomentShape_le
    {N D : ℕ} {T : ℝ} {W : Finset ℝ}
    (hD : 0 < D) (hT : 0 ≤ T) :
    (∑ d ∈ Finset.Icc D N, gmSecondMomentShape (N / d) T W) ≤
      gmLargeSecondAggregateShape N D T W := by
  have hOne := sum_Icc_natDiv_le_harmonic (N := N) hD
  have hTwo := sum_Icc_natDiv_sq_le (N := N) hD
  have hW0 : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg W.card
  have hH0 : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  unfold gmLargeSecondAggregateShape
  simp_rw [gmSecondMomentShape]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hA :
      (∑ x ∈ Finset.Icc D N, (W.card : ℝ) ^ 2 * (N / x : ℕ)) ≤
        (W.card : ℝ) ^ 2 *
          ((N : ℝ) * (((harmonic N : ℚ) : ℝ))) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hOne (sq_nonneg _)
  have hB :
      (∑ x ∈ Finset.Icc D N, (W.card : ℝ) * (N / x : ℕ) ^ 2) ≤
        (W.card : ℝ) * (2 * (N : ℝ) ^ 2 / (D : ℝ)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hTwo hW0
  have hC :
      (∑ x ∈ Finset.Icc D N,
        (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * (N / x : ℕ)) ≤
        ((W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) *
          ((N : ℝ) * (((harmonic N : ℚ) : ℝ))) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hOne (by positivity)
  calc
    (∑ x ∈ Finset.Icc D N, (W.card : ℝ) ^ 2 * (N / x : ℕ)) +
          (∑ x ∈ Finset.Icc D N, (W.card : ℝ) * (N / x : ℕ) ^ 2) +
          (∑ x ∈ Finset.Icc D N,
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * (N / x : ℕ)) ≤
        (W.card : ℝ) ^ 2 *
            ((N : ℝ) * (((harmonic N : ℚ) : ℝ))) +
          (W.card : ℝ) * (2 * (N : ℝ) ^ 2 / (D : ℝ)) +
          ((W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) *
            ((N : ℝ) * (((harmonic N : ℚ) : ℝ))) := by
      exact add_le_add (add_le_add hA hB) hC
    _ = (W.card : ℝ) ^ 2 * (N : ℝ) * (((harmonic N : ℚ) : ℝ)) +
          2 * (W.card : ℝ) * (N : ℝ) ^ 2 / (D : ℝ) +
          (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) *
            (N : ℝ) * (((harmonic N : ℚ) : ℝ)) := by ring

theorem sum_gmFourthMomentShape_le
    {N D : ℕ} {T : ℝ} {W : Finset ℝ}
    (hD : 0 < D) (hT : 0 ≤ T) :
    (∑ d ∈ Finset.Icc D N, gmFourthMomentShape (N / d) T W) ≤
      gmLargeFourthAggregateShape N D T W := by
  have hOne := sum_Icc_natDiv_le_harmonic (N := N) hD
  have hTwo := sum_Icc_natDiv_sq_le (N := N) hD
  have hE0 : 0 ≤ (ApproxAddEnergy 1 W : ℝ) := Nat.cast_nonneg _
  have hW0 : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg W.card
  have hH0 : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  unfold gmLargeFourthAggregateShape
  simp_rw [gmFourthMomentShape]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hA :
      (∑ x ∈ Finset.Icc D N, (W.card : ℝ) ^ 4 * (N / x : ℕ)) ≤
        (W.card : ℝ) ^ 4 *
          ((N : ℝ) * (((harmonic N : ℚ) : ℝ))) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hOne (by positivity)
  have hB :
      (∑ x ∈ Finset.Icc D N,
        (ApproxAddEnergy 1 W : ℝ) * (N / x : ℕ) ^ 2) ≤
        (ApproxAddEnergy 1 W : ℝ) *
          (2 * (N : ℝ) ^ 2 / (D : ℝ)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hTwo hE0
  have hC :
      (∑ x ∈ Finset.Icc D N,
        (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
          (W.card : ℝ) * T ^ (1 / 2 : ℝ) * (N / x : ℕ)) ≤
        ((ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
          (W.card : ℝ) * T ^ (1 / 2 : ℝ)) *
          ((N : ℝ) * (((harmonic N : ℚ) : ℝ))) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hOne (by positivity)
  calc
    (∑ x ∈ Finset.Icc D N, (W.card : ℝ) ^ 4 * (N / x : ℕ)) +
          (∑ x ∈ Finset.Icc D N,
            (ApproxAddEnergy 1 W : ℝ) * (N / x : ℕ) ^ 2) +
          (∑ x ∈ Finset.Icc D N,
            (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
              (W.card : ℝ) * T ^ (1 / 2 : ℝ) * (N / x : ℕ)) ≤
        (W.card : ℝ) ^ 4 *
            ((N : ℝ) * (((harmonic N : ℚ) : ℝ))) +
          (ApproxAddEnergy 1 W : ℝ) *
            (2 * (N : ℝ) ^ 2 / (D : ℝ)) +
          ((ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
            (W.card : ℝ) * T ^ (1 / 2 : ℝ)) *
            ((N : ℝ) * (((harmonic N : ℚ) : ℝ))) := by
      exact add_le_add (add_le_add hA hB) hC
    _ = (W.card : ℝ) ^ 4 * (N : ℝ) * (((harmonic N : ℚ) : ℝ)) +
          2 * (ApproxAddEnergy 1 W : ℝ) * (N : ℝ) ^ 2 / (D : ℝ) +
          (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
            (W.card : ℝ) * T ^ (1 / 2 : ℝ) *
            (N : ℝ) * (((harmonic N : ℚ) : ℝ)) := by ring

/-! ### The summed large-gcd Cauchy--Schwarz estimate -/

/-- The `gmMiddleGcdThirdMoment` definition used by the source-facing construction in `LargeValuesEnergyFinal`. -/
noncomputable def gmMiddleGcdThirdMoment
    (N D : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc D N, gmGcdSliceMoment 3 N d W

theorem gmGcdSliceThirdMoment_le_dyadicPlus
    {N d : ℕ} (W : Finset ℝ) (hd : 0 < d) :
    gmGcdSliceMoment 3 N d W ≤
      Real.sqrt (gmDyadicPlusRatioMoment 2 (N / d) W) *
        Real.sqrt (gmDyadicPlusRatioMoment 4 (N / d) W) := by
  rw [gmGcdSliceMoment_eq_reduced]
  calc
    gmReducedRatioMoment 3 N d W ≤
        Real.sqrt (gmReducedRatioMoment 2 N d W) *
          Real.sqrt (gmReducedRatioMoment 4 N d W) :=
      gmReducedThirdMoment_le_sqrt N d W
    _ ≤ Real.sqrt (gmDyadicPlusRatioMoment 2 (N / d) W) *
          Real.sqrt (gmDyadicPlusRatioMoment 4 (N / d) W) := by
      exact mul_le_mul
        (Real.sqrt_le_sqrt (gmReducedRatioMoment_le_plus 2 N d W hd))
        (Real.sqrt_le_sqrt (gmReducedRatioMoment_le_plus 4 N d W hd))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Lemma 11.9 before substituting the physical cutoff and simplifying the
two aggregate moment factors.  Every term is still the actual gcd slice. -/
theorem gmMiddleGcdThirdMoment_raw
    (μ : ℝ) (hμ : 0 < μ) :
    ∃ C₂ C₄ T₀ : ℝ,
      0 < C₂ ∧ 0 < C₄ ∧ 1 ≤ T₀ ∧
      ∀ {N D : ℕ} {T : ℝ} (W : Finset ℝ),
        0 < D → T₀ ≤ T → (N : ℝ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        gmMiddleGcdThirdMoment N D W ≤
          Real.sqrt (C₂ * T ^ μ * gmLargeSecondAggregateShape N D T W) *
            Real.sqrt (C₄ * T ^ μ * gmLargeFourthAggregateShape N D T W) := by
  obtain ⟨C₂, T₂, hC₂, hT₂, hTwo⟩ :=
    gmDyadicPlusSecondMoment_native μ hμ
  obtain ⟨C₄, T₄, hC₄, hT₄, hFour⟩ :=
    gmDyadicPlusFourthMoment_native μ hμ
  let T₀ := max T₂ T₄
  refine ⟨C₂, C₄, T₀, hC₂, hC₄, ?_, ?_⟩
  · exact le_max_of_le_left hT₂
  intro N D T W hD hT hNT hSep hBase
  have hT₂' : T₂ ≤ T := (le_max_left _ _).trans hT
  have hT₄' : T₄ ≤ T := (le_max_right _ _).trans hT
  have hTOne : 1 ≤ T := hT₂.trans hT₂'
  have hT0 : 0 ≤ T := zero_le_one.trans hTOne
  have hTwoSum :
      (∑ d ∈ Finset.Icc D N,
          gmDyadicPlusRatioMoment 2 (N / d) W) ≤
        C₂ * T ^ μ * gmLargeSecondAggregateShape N D T W := by
    calc
      (∑ d ∈ Finset.Icc D N,
          gmDyadicPlusRatioMoment 2 (N / d) W) ≤
          ∑ d ∈ Finset.Icc D N,
            C₂ * T ^ μ * gmSecondMomentShape (N / d) T W := by
        apply Finset.sum_le_sum
        intro d hd
        have hdPos : 0 < d := hD.trans_le (Finset.mem_Icc.mp hd).1
        have hM : 0 < N / d := Nat.div_pos (Finset.mem_Icc.mp hd).2 hdPos
        exact hTwo (N / d) T W hM hT₂' hSep hBase
      _ = C₂ * T ^ μ *
          (∑ d ∈ Finset.Icc D N, gmSecondMomentShape (N / d) T W) := by
        rw [Finset.mul_sum]
      _ ≤ C₂ * T ^ μ * gmLargeSecondAggregateShape N D T W := by
        exact mul_le_mul_of_nonneg_left (sum_gmSecondMomentShape_le hD hT0)
          (mul_nonneg hC₂.le (Real.rpow_nonneg hT0 μ))
  have hFourSum :
      (∑ d ∈ Finset.Icc D N,
          gmDyadicPlusRatioMoment 4 (N / d) W) ≤
        C₄ * T ^ μ * gmLargeFourthAggregateShape N D T W := by
    calc
      (∑ d ∈ Finset.Icc D N,
          gmDyadicPlusRatioMoment 4 (N / d) W) ≤
          ∑ d ∈ Finset.Icc D N,
            C₄ * T ^ μ * gmFourthMomentShape (N / d) T W := by
        apply Finset.sum_le_sum
        intro d hd
        have hdPos : 0 < d := hD.trans_le (Finset.mem_Icc.mp hd).1
        have hM : 0 < N / d := Nat.div_pos (Finset.mem_Icc.mp hd).2 hdPos
        have hMN : (N / d : ℕ) ≤ N := Nat.div_le_self N d
        have hMT : ((N / d : ℕ) : ℝ) ≤ T := by
          exact (Nat.cast_le.mpr hMN).trans hNT
        exact hFour (N / d) T W hM hT₄' hMT hSep hBase
      _ = C₄ * T ^ μ *
          (∑ d ∈ Finset.Icc D N, gmFourthMomentShape (N / d) T W) := by
        rw [Finset.mul_sum]
      _ ≤ C₄ * T ^ μ * gmLargeFourthAggregateShape N D T W := by
        exact mul_le_mul_of_nonneg_left (sum_gmFourthMomentShape_le hD hT0)
          (mul_nonneg hC₄.le (Real.rpow_nonneg hT0 μ))
  have hCauchy :
      gmMiddleGcdThirdMoment N D W ≤
        Real.sqrt (∑ d ∈ Finset.Icc D N,
          gmDyadicPlusRatioMoment 2 (N / d) W) *
        Real.sqrt (∑ d ∈ Finset.Icc D N,
          gmDyadicPlusRatioMoment 4 (N / d) W) := by
    unfold gmMiddleGcdThirdMoment
    calc
      (∑ d ∈ Finset.Icc D N, gmGcdSliceMoment 3 N d W) ≤
          ∑ d ∈ Finset.Icc D N,
            Real.sqrt (gmDyadicPlusRatioMoment 2 (N / d) W) *
              Real.sqrt (gmDyadicPlusRatioMoment 4 (N / d) W) := by
        apply Finset.sum_le_sum
        intro d hd
        exact gmGcdSliceThirdMoment_le_dyadicPlus W
          (hD.trans_le (Finset.mem_Icc.mp hd).1)
      _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _
        (fun d => by unfold gmDyadicPlusRatioMoment; positivity)
        (fun d => by unfold gmDyadicPlusRatioMoment; positivity)
  exact hCauchy.trans (mul_le_mul (Real.sqrt_le_sqrt hTwoSum)
    (Real.sqrt_le_sqrt hFourSum) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem gmLargeSecondAggregateShape_nonneg
    {N D : ℕ} {T : ℝ} {W : Finset ℝ}
    (hD : 0 < D) (hT : 0 ≤ T) :
    0 ≤ gmLargeSecondAggregateShape N D T W := by
  have hH : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  unfold gmLargeSecondAggregateShape
  positivity

theorem gmLargeFourthAggregateShape_nonneg
    {N D : ℕ} {T : ℝ} {W : Finset ℝ}
    (hD : 0 < D) (hT : 0 ≤ T) :
    0 ≤ gmLargeFourthAggregateShape N D T W := by
  have hH : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  unfold gmLargeFourthAggregateShape
  positivity

theorem sqrt_const_mul_rpow_le
    {C T μ : ℝ} (hC : 0 < C) (hT : 1 ≤ T) (hμ : 0 < μ) :
    Real.sqrt (C * T ^ μ) ≤ (C + 1) * T ^ μ := by
  have hpow : 1 ≤ T ^ μ := Real.one_le_rpow hT hμ.le
  have hsC : Real.sqrt C ≤ C + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hsPow : Real.sqrt (T ^ μ) ≤ T ^ μ := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  rw [Real.sqrt_mul hC.le]
  exact mul_le_mul hsC hsPow (Real.sqrt_nonneg _) (by linarith)

/-- The summed middle range in the source `T^epsilon` notation.  This is
the complete Cauchy--Schwarz and harmonic-loss assembly preceding the two
case simplifications in equations (11.5)--(11.6). -/
theorem gmMiddleGcdThirdMoment_native
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ {N D : ℕ} {T : ℝ} (W : Finset ℝ),
        0 < D → T₀ ≤ T → (N : ℝ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        gmMiddleGcdThirdMoment N D W ≤
          C * T ^ ε *
            Real.sqrt (gmLargeSecondAggregateShape N D T W) *
            Real.sqrt (gmLargeFourthAggregateShape N D T W) := by
  let μ := ε / 2
  have hμ : 0 < μ := by dsimp only [μ]; linarith
  obtain ⟨C₂, C₄, T₀, hC₂, hC₄, hT₀, hraw⟩ :=
    gmMiddleGcdThirdMoment_raw μ hμ
  let C := (C₂ + 1) * (C₄ + 1)
  refine ⟨C, T₀, by dsimp only [C]; positivity, hT₀, ?_⟩
  intro N D T W hD hT hNT hSep hBase
  have hTOne : 1 ≤ T := hT₀.trans hT
  have hT0 : 0 ≤ T := zero_le_one.trans hTOne
  have hA0 := gmLargeSecondAggregateShape_nonneg (N := N) (W := W) hD hT0
  have hB0 := gmLargeFourthAggregateShape_nonneg (N := N) (W := W) hD hT0
  have hbase := hraw W hD hT hNT hSep hBase
  have hs₂ := sqrt_const_mul_rpow_le hC₂ hTOne hμ
  have hs₄ := sqrt_const_mul_rpow_le hC₄ hTOne hμ
  have hfac₂ :
      Real.sqrt (C₂ * T ^ μ * gmLargeSecondAggregateShape N D T W) =
        Real.sqrt (C₂ * T ^ μ) *
          Real.sqrt (gmLargeSecondAggregateShape N D T W) := by
    rw [Real.sqrt_mul]
    exact mul_nonneg hC₂.le (Real.rpow_nonneg hT0 μ)
  have hfac₄ :
      Real.sqrt (C₄ * T ^ μ * gmLargeFourthAggregateShape N D T W) =
        Real.sqrt (C₄ * T ^ μ) *
          Real.sqrt (gmLargeFourthAggregateShape N D T W) := by
    rw [Real.sqrt_mul]
    exact mul_nonneg hC₄.le (Real.rpow_nonneg hT0 μ)
  rw [hfac₂, hfac₄] at hbase
  calc
    gmMiddleGcdThirdMoment N D W ≤
        (Real.sqrt (C₂ * T ^ μ) *
          Real.sqrt (gmLargeSecondAggregateShape N D T W)) *
        (Real.sqrt (C₄ * T ^ μ) *
          Real.sqrt (gmLargeFourthAggregateShape N D T W)) := hbase
    _ ≤ ((C₂ + 1) * T ^ μ *
          Real.sqrt (gmLargeSecondAggregateShape N D T W)) *
        ((C₄ + 1) * T ^ μ *
          Real.sqrt (gmLargeFourthAggregateShape N D T W)) := by
      gcongr
    _ = C * T ^ ε *
          Real.sqrt (gmLargeSecondAggregateShape N D T W) *
          Real.sqrt (gmLargeFourthAggregateShape N D T W) := by
      dsimp only [C, μ]
      calc
        (C₂ + 1) * T ^ (ε / 2) *
              Real.sqrt (gmLargeSecondAggregateShape N D T W) *
            ((C₄ + 1) * T ^ (ε / 2) *
              Real.sqrt (gmLargeFourthAggregateShape N D T W)) =
            (C₂ + 1) * (C₄ + 1) *
              (T ^ (ε / 2) * T ^ (ε / 2)) *
              Real.sqrt (gmLargeSecondAggregateShape N D T W) *
              Real.sqrt (gmLargeFourthAggregateShape N D T W) := by ring
        _ = (C₂ + 1) * (C₄ + 1) * T ^ ε *
              Real.sqrt (gmLargeSecondAggregateShape N D T W) *
              Real.sqrt (gmLargeFourthAggregateShape N D T W) := by
          have hp : T ^ (ε / 2) * T ^ (ε / 2) = T ^ ε := by
            rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hTOne)]
            congr 1
            ring
          rw [hp]

/-- The `gmDiagonalGcdThirdMoment` definition used by the source-facing construction in `LargeValuesEnergyFinal`. -/
noncomputable def gmDiagonalGcdThirdMoment
    (N : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc N (2 * N), gmGcdSliceMoment 3 N d W

theorem gmGcdSliceThirdMoment_le_card_cubed_of_lt
    {N d : ℕ} (W : Finset ℝ) (hNd : N < d) :
    gmGcdSliceMoment 3 N d W ≤ (W.card : ℝ) ^ 3 := by
  have hd : 0 < d := (Nat.zero_le N).trans_lt hNd
  have hdiv : N / d = 0 := Nat.div_eq_of_lt hNd
  have hred := gmReducedRatioMoment_le_plus 3 N d W hd
  have hplus := gmDyadicPlusRatioMoment_le 3 0 W
  rw [hdiv] at hred
  rw [gmGcdSliceMoment_eq_reduced]
  exact hred.trans (by
    simpa [gmDiscreteRatioMoment, dyadicInterval] using hplus)

/-- The `d>N` part consists only of diagonal quotient-one slices and costs
at most `N |W|³`, the first term of Lemma 11.9. -/
theorem gmDiagonalGcdThirdMoment_le
    (N : ℕ) (W : Finset ℝ) :
    gmDiagonalGcdThirdMoment N W ≤
      (N : ℝ) * (W.card : ℝ) ^ 3 := by
  unfold gmDiagonalGcdThirdMoment
  calc
    (∑ d ∈ Finset.Ioc N (2 * N), gmGcdSliceMoment 3 N d W) ≤
        ∑ _d ∈ Finset.Ioc N (2 * N), (W.card : ℝ) ^ 3 := by
      apply Finset.sum_le_sum
      intro d hd
      exact gmGcdSliceThirdMoment_le_card_cubed_of_lt W
        (Finset.mem_Ioc.mp hd).1
    _ = (N : ℝ) * (W.card : ℝ) ^ 3 := by
      have hcard : (Finset.Ioc N (2 * N)).card = N := by
        rw [Nat.card_Ioc]
        omega
      simp [hcard]

/-! ### The physical cutoff `D = floor (N²/T)` and equation (11.4) -/

/-- The `gmGcdCutoff` definition used by the source-facing construction in `LargeValuesEnergyFinal`. -/
noncomputable def gmGcdCutoff (N : ℕ) (T : ℝ) : ℕ :=
  ⌊(N : ℝ) ^ 2 / T⌋₊

theorem gmGcdCutoff_bounds
    {N : ℕ} {T : ℝ} (hTwo : 2 ≤ (N : ℝ) ^ 2 / T) :
    0 < gmGcdCutoff N T ∧
      ((N : ℝ) ^ 2 / T) / 2 ≤ (gmGcdCutoff N T : ℝ) ∧
      (gmGcdCutoff N T : ℝ) ≤ (N : ℝ) ^ 2 / T := by
  let x := (N : ℝ) ^ 2 / T
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hUpper : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  have hStrict : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one x
  have hLower : x / 2 ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    dsimp only [x] at hStrict ⊢
    nlinarith
  have hPosCast : (0 : ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ x / 2 := by
      dsimp only [x] at hTwo ⊢
      linarith
    exact lt_of_lt_of_le zero_lt_one (this.trans hLower)
  change 0 < ⌊x⌋₊ ∧ x / 2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x
  exact ⟨by exact_mod_cast hPosCast, hLower, hUpper⟩

theorem gmGcdCutoff_le_N
    {N : ℕ} {T : ℝ} (hT : 0 < T) (hN : 0 < N)
    (hNT : (N : ℝ) ≤ T) :
    gmGcdCutoff N T ≤ N := by
  have hUpper : (gmGcdCutoff N T : ℝ) ≤ (N : ℝ) ^ 2 / T := by
    exact Nat.floor_le (div_nonneg (sq_nonneg _) hT.le)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hxN : (N : ℝ) ^ 2 / T ≤ N := by
    rw [div_le_iff₀ hT]
    nlinarith
  exact_mod_cast hUpper.trans hxN

theorem two_le_sq_div_of_three_quarters_le
    {N : ℕ} {T : ℝ} (hT : 4 ≤ T)
    (hN : T ^ (3 / 4 : ℝ) ≤ (N : ℝ)) :
    2 ≤ (N : ℝ) ^ 2 / T := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hbase0 : 0 ≤ T ^ (3 / 4 : ℝ) := Real.rpow_nonneg hTpos.le _
  have hsq : (T ^ (3 / 4 : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 := by
    nlinarith [mul_self_le_mul_self hbase0 hN]
  have hsqrt : 2 ≤ T ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by norm_num) hTpos.le).2 (by norm_num at hT ⊢; exact hT)
  have hpow : (T ^ (3 / 4 : ℝ)) ^ 2 =
      T * T ^ (1 / 2 : ℝ) := by
    calc
      (T ^ (3 / 4 : ℝ)) ^ 2 =
          T ^ (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by ring
      _ = T ^ ((3 / 4 : ℝ) + 3 / 4) := by
        rw [Real.rpow_add hTpos]
      _ = T ^ ((1 : ℝ) + 1 / 2) := by congr 1; ring
      _ = T ^ (1 : ℝ) * T ^ (1 / 2 : ℝ) := Real.rpow_add hTpos 1 (1 / 2)
      _ = T * T ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
  have htwoT : 2 * T ≤ (N : ℝ) ^ 2 := by
    calc
      2 * T ≤ T ^ (1 / 2 : ℝ) * T := by
        exact mul_le_mul_of_nonneg_right hsqrt hTpos.le
      _ = (T ^ (3 / 4 : ℝ)) ^ 2 := by rw [hpow]; ring
      _ ≤ (N : ℝ) ^ 2 := hsq
  exact (le_div_iff₀ hTpos).2 (by nlinarith)

/-- The `gmLargeSecondPaperShape` definition used by the source-facing construction in `LargeValuesEnergyFinal`. -/
noncomputable def gmLargeSecondPaperShape
    (N : ℕ) (T : ℝ) (W : Finset ℝ) : ℝ :=
  (W.card : ℝ) ^ 2 * N +
    (W.card : ℝ) * T +
    (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N

/-- The `gmLargeFourthPaperShape` definition used by the source-facing construction in `LargeValuesEnergyFinal`. -/
noncomputable def gmLargeFourthPaperShape
    (N : ℕ) (T : ℝ) (W : Finset ℝ) : ℝ :=
  (W.card : ℝ) ^ 4 * N +
    (ApproxAddEnergy 1 W : ℝ) * T +
    (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
      (W.card : ℝ) * T ^ (1 / 2 : ℝ) * N

theorem harmonic_le_scale_rpow
    {η T : ℝ} {N : ℕ} (hη : 0 < η) (hT : 1 ≤ T)
    (hNT : (N : ℝ) ≤ T) :
    (((harmonic N : ℚ) : ℝ)) ≤ (1 + η⁻¹) * T ^ η := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpowNT : (N : ℝ) ^ η ≤ T ^ η :=
    Real.rpow_le_rpow hN0 hNT hη.le
  have hpowOne : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  have hmax : max 1 ((N : ℝ) ^ η) ≤ T ^ η :=
    max_le hpowOne hpowNT
  exact (harmonic_le_epsilon_rpow hη N).trans
    (mul_le_mul_of_nonneg_left hmax (by positivity))

theorem gmCutoff_reciprocal_term_le
    {N : ℕ} {T : ℝ} (hT : 0 < T)
    (hTwo : 2 ≤ (N : ℝ) ^ 2 / T) :
    2 * (N : ℝ) ^ 2 / (gmGcdCutoff N T : ℝ) ≤ 4 * T := by
  obtain ⟨hD, hLower, hUpper⟩ := gmGcdCutoff_bounds hTwo
  have hDcast : (0 : ℝ) < gmGcdCutoff N T := by exact_mod_cast hD
  have hxLe : (N : ℝ) ^ 2 / T ≤ (gmGcdCutoff N T : ℝ) * 2 := by
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hLower
  have hsq : (N : ℝ) ^ 2 ≤ (gmGcdCutoff N T : ℝ) * 2 * T :=
    (div_le_iff₀ hT).mp hxLe
  rw [div_le_iff₀ hDcast]
  nlinarith

theorem gmLargeSecondAggregateShape_le_paper
    {η T : ℝ} {N : ℕ} {W : Finset ℝ}
    (hη : 0 < η) (hT : 1 ≤ T) (hNT : (N : ℝ) ≤ T)
    (hTwo : 2 ≤ (N : ℝ) ^ 2 / T) :
    gmLargeSecondAggregateShape N (gmGcdCutoff N T) T W ≤
      4 * (1 + η⁻¹) * T ^ η * gmLargeSecondPaperShape N T W := by
  have hH := harmonic_le_scale_rpow hη hT hNT
  have hRecip := gmCutoff_reciprocal_term_le (lt_of_lt_of_le zero_lt_one hT) hTwo
  have hPowOne : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  have hL : 1 ≤ 1 + η⁻¹ := by
    have : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
    linarith
  have hLP : 1 ≤ (1 + η⁻¹) * T ^ η := by nlinarith
  have hLP0 : 0 ≤ (1 + η⁻¹) * T ^ η := by linarith
  unfold gmLargeSecondAggregateShape gmLargeSecondPaperShape
  have h₁ : (W.card : ℝ) ^ 2 * (N : ℝ) * (((harmonic N : ℚ) : ℝ)) ≤
      (1 + η⁻¹) * T ^ η * ((W.card : ℝ) ^ 2 * N) := by
    calc
      _ ≤ (W.card : ℝ) ^ 2 * (N : ℝ) * ((1 + η⁻¹) * T ^ η) := by gcongr
      _ = _ := by ring
  have h₂ : 2 * (W.card : ℝ) * (N : ℝ) ^ 2 /
        (gmGcdCutoff N T : ℝ) ≤
      4 * (1 + η⁻¹) * T ^ η * ((W.card : ℝ) * T) := by
    calc
      _ = (W.card : ℝ) *
          (2 * (N : ℝ) ^ 2 / (gmGcdCutoff N T : ℝ)) := by ring
      _ ≤ (W.card : ℝ) * (4 * T) := by gcongr
      _ ≤ 4 * (1 + η⁻¹) * T ^ η * ((W.card : ℝ) * T) := by
        calc
          (W.card : ℝ) * (4 * T) = 4 * ((W.card : ℝ) * T) := by ring
          _ = 1 * (4 * ((W.card : ℝ) * T)) := by ring
          _ ≤ ((1 + η⁻¹) * T ^ η) *
              (4 * ((W.card : ℝ) * T)) := by
            exact mul_le_mul_of_nonneg_right hLP (by positivity)
          _ = _ := by ring
  have h₃ : (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) *
        (N : ℝ) * (((harmonic N : ℚ) : ℝ)) ≤
      (1 + η⁻¹) * T ^ η *
        ((W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N) := by
    calc
      _ ≤ (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) *
          (N : ℝ) * ((1 + η⁻¹) * T ^ η) := by gcongr
      _ = _ := by ring
  have hterm₁ : 0 ≤ (1 + η⁻¹) * T ^ η * ((W.card : ℝ) ^ 2 * N) := by positivity
  have hterm₃ : 0 ≤ (1 + η⁻¹) * T ^ η *
      ((W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N) := by positivity
  calc
    _ ≤ (1 + η⁻¹) * T ^ η * ((W.card : ℝ) ^ 2 * N) +
        4 * (1 + η⁻¹) * T ^ η * ((W.card : ℝ) * T) +
        (1 + η⁻¹) * T ^ η *
          ((W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N) :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ ≤ 4 * (1 + η⁻¹) * T ^ η *
        ((W.card : ℝ) ^ 2 * N + (W.card : ℝ) * T +
          (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N) := by
      nlinarith

theorem gmLargeFourthAggregateShape_le_paper
    {η T : ℝ} {N : ℕ} {W : Finset ℝ}
    (hη : 0 < η) (hT : 1 ≤ T) (hNT : (N : ℝ) ≤ T)
    (hTwo : 2 ≤ (N : ℝ) ^ 2 / T) :
    gmLargeFourthAggregateShape N (gmGcdCutoff N T) T W ≤
      4 * (1 + η⁻¹) * T ^ η * gmLargeFourthPaperShape N T W := by
  have hH := harmonic_le_scale_rpow hη hT hNT
  have hRecip := gmCutoff_reciprocal_term_le (lt_of_lt_of_le zero_lt_one hT) hTwo
  have hPowOne : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  have hL : 1 ≤ 1 + η⁻¹ := by
    have : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
    linarith
  have hLP : 1 ≤ (1 + η⁻¹) * T ^ η := by nlinarith
  have hLP0 : 0 ≤ (1 + η⁻¹) * T ^ η := by linarith
  unfold gmLargeFourthAggregateShape gmLargeFourthPaperShape
  have h₁ : (W.card : ℝ) ^ 4 * (N : ℝ) * (((harmonic N : ℚ) : ℝ)) ≤
      (1 + η⁻¹) * T ^ η * ((W.card : ℝ) ^ 4 * N) := by
    calc
      _ ≤ (W.card : ℝ) ^ 4 * (N : ℝ) * ((1 + η⁻¹) * T ^ η) := by gcongr
      _ = _ := by ring
  have h₂ : 2 * (ApproxAddEnergy 1 W : ℝ) * (N : ℝ) ^ 2 /
        (gmGcdCutoff N T : ℝ) ≤
      4 * (1 + η⁻¹) * T ^ η * ((ApproxAddEnergy 1 W : ℝ) * T) := by
    calc
      _ = (ApproxAddEnergy 1 W : ℝ) *
          (2 * (N : ℝ) ^ 2 / (gmGcdCutoff N T : ℝ)) := by ring
      _ ≤ (ApproxAddEnergy 1 W : ℝ) * (4 * T) := by gcongr
      _ ≤ 4 * (1 + η⁻¹) * T ^ η *
          ((ApproxAddEnergy 1 W : ℝ) * T) := by
        calc
          (ApproxAddEnergy 1 W : ℝ) * (4 * T) =
              4 * ((ApproxAddEnergy 1 W : ℝ) * T) := by ring
          _ = 1 * (4 * ((ApproxAddEnergy 1 W : ℝ) * T)) := by ring
          _ ≤ ((1 + η⁻¹) * T ^ η) *
              (4 * ((ApproxAddEnergy 1 W : ℝ) * T)) := by
            exact mul_le_mul_of_nonneg_right hLP (by positivity)
          _ = _ := by ring
  have h₃ : (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
        (W.card : ℝ) * T ^ (1 / 2 : ℝ) * (N : ℝ) *
        (((harmonic N : ℚ) : ℝ)) ≤
      (1 + η⁻¹) * T ^ η *
        ((ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
          (W.card : ℝ) * T ^ (1 / 2 : ℝ) * N) := by
    calc
      _ ≤ (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
          (W.card : ℝ) * T ^ (1 / 2 : ℝ) * (N : ℝ) *
          ((1 + η⁻¹) * T ^ η) := by gcongr
      _ = _ := by ring
  have hterm₁ : 0 ≤ (1 + η⁻¹) * T ^ η * ((W.card : ℝ) ^ 4 * N) := by positivity
  have hterm₃ : 0 ≤ (1 + η⁻¹) * T ^ η *
      ((ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
        (W.card : ℝ) * T ^ (1 / 2 : ℝ) * N) := by positivity
  calc
    _ ≤ (1 + η⁻¹) * T ^ η * ((W.card : ℝ) ^ 4 * N) +
        4 * (1 + η⁻¹) * T ^ η * ((ApproxAddEnergy 1 W : ℝ) * T) +
        (1 + η⁻¹) * T ^ η *
          ((ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
            (W.card : ℝ) * T ^ (1 / 2 : ℝ) * N) :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ ≤ 4 * (1 + η⁻¹) * T ^ η *
        ((W.card : ℝ) ^ 4 * N + (ApproxAddEnergy 1 W : ℝ) * T +
          (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
            (W.card : ℝ) * T ^ (1 / 2 : ℝ) * N) := by
      nlinarith

theorem approxAddEnergy_le_three_card_cubed
    (W : Finset ℝ) (hSep : IsSeparated 1 W) :
    ApproxAddEnergy 1 W ≤ 3 * W.card ^ 3 := by
  have h := sum_approximateAdditiveQuadruples_le_three_mul_sum_triples
    W hSep (fun _ _ _ => (1 : ℝ)) (by intros; norm_num)
  have h' : (ApproxAddEnergy 1 W : ℝ) ≤ 3 * (W.card : ℝ) ^ 3 := by
    have h'' : (ApproxAddEnergy 1 W : ℝ) ≤
        3 * ((W.card : ℝ) * ((W.card : ℝ) * (W.card : ℝ))) := by
      simpa only [ApproxAddEnergy, Finset.sum_const, nsmul_eq_mul, mul_one] using h
    nlinarith
  exact_mod_cast h'

theorem sqrt_mul_sqrt_le_of_mul_le_sq
    {A B R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (h : A * B ≤ R ^ 2) :
    Real.sqrt A * Real.sqrt B ≤ R := by
  rw [← Real.sqrt_mul hA]
  exact Real.sqrt_le_iff.mpr ⟨hR, h⟩

theorem gmLargePaperShapes_large_card
    {N : ℕ} {T : ℝ} {W : Finset ℝ}
    (hT : 4 ≤ T) (hN : T ^ (3 / 4 : ℝ) ≤ (N : ℝ))
    (hSep : IsSeparated 1 W)
    (hW : T ^ (2 / 3 : ℝ) ≤ (W.card : ℝ)) :
    Real.sqrt (gmLargeSecondPaperShape N T W) *
        Real.sqrt (gmLargeFourthPaperShape N T W) ≤
      5 * (N : ℝ) * (W.card : ℝ) ^ 3 := by
  let w : ℝ := W.card
  let n : ℝ := N
  let E : ℝ := ApproxAddEnergy 1 W
  have hTOne : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hw0 : 0 ≤ w := by dsimp only [w]; positivity
  have hn0 : 0 ≤ n := by dsimp only [n]; positivity
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hE : E ≤ 3 * w ^ 3 := by
    dsimp only [E, w]
    exact_mod_cast approxAddEnergy_le_three_card_cubed W hSep
  have hsqrtW : T ^ (1 / 2 : ℝ) ≤ w ^ (3 / 4 : ℝ) := by
    have hm := Real.rpow_le_rpow (Real.rpow_nonneg hT0 _) hW
      (by norm_num : (0 : ℝ) ≤ 3 / 4)
    calc
      T ^ (1 / 2 : ℝ) = (T ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_mul hT0]
        congr 1
        ring
      _ ≤ w ^ (3 / 4 : ℝ) := hm
  have hthirdN : T ^ (1 / 3 : ℝ) ≤ n := by
    calc
      T ^ (1 / 3 : ℝ) ≤ T ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hTOne (by norm_num)
      _ ≤ n := hN
  have hTN : T ≤ w * n := by
    calc
      T = T ^ (2 / 3 : ℝ) * T ^ (1 / 3 : ℝ) := by
        simpa only [show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, Real.rpow_one] using
          Real.rpow_add (lt_of_lt_of_le zero_lt_one hTOne) (2 / 3 : ℝ) (1 / 3 : ℝ)
      _ ≤ w * n := mul_le_mul hW hthirdN
        (Real.rpow_nonneg hT0 _) hw0
  have hEpow : E ^ (3 / 4 : ℝ) ≤ 3 * w ^ (9 / 4 : ℝ) := by
    have hm := Real.rpow_le_rpow hE0 hE (by norm_num : (0 : ℝ) ≤ 3 / 4)
    have hthree : (3 : ℝ) ^ (3 / 4 : ℝ) ≤ 3 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    calc
      E ^ (3 / 4 : ℝ) ≤ (3 * w ^ 3) ^ (3 / 4 : ℝ) := hm
      _ = 3 ^ (3 / 4 : ℝ) * (w ^ 3) ^ (3 / 4 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
      _ = 3 ^ (3 / 4 : ℝ) * w ^ (9 / 4 : ℝ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hw0]
        congr 2
        ring
      _ ≤ 3 * w ^ (9 / 4 : ℝ) := by gcongr
  have hA : gmLargeSecondPaperShape N T W ≤ 3 * (w ^ 2 * n) := by
    unfold gmLargeSecondPaperShape
    change w ^ 2 * n + w * T + w ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * n ≤ _
    have h₂ : w * T ≤ w ^ 2 * n := by
      calc
        w * T ≤ w * (w * n) := mul_le_mul_of_nonneg_left hTN hw0
        _ = w ^ 2 * n := by ring
    have h₃ : w ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * n ≤
        w ^ 2 * n := by
      calc
        _ ≤ w ^ (5 / 4 : ℝ) * w ^ (3 / 4 : ℝ) * n := by gcongr
        _ = w ^ ((5 / 4 : ℝ) + 3 / 4) * n := by
          rw [Real.rpow_add (show 0 < w by
            exact lt_of_lt_of_le (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hTOne) _)
              hW)]
        _ = w ^ 2 * n := by norm_num
    nlinarith [mul_nonneg (sq_nonneg w) hn0]
  have hB : gmLargeFourthPaperShape N T W ≤ 7 * (w ^ 4 * n) := by
    unfold gmLargeFourthPaperShape
    change w ^ 4 * n + E * T + E ^ (3 / 4 : ℝ) * w * T ^ (1 / 2 : ℝ) * n ≤ _
    have h₂ : E * T ≤ 3 * (w ^ 4 * n) := by
      calc
        E * T ≤ (3 * w ^ 3) * (w * n) :=
          mul_le_mul hE hTN hT0 (by positivity)
        _ = 3 * (w ^ 4 * n) := by ring
    have h₃ : E ^ (3 / 4 : ℝ) * w * T ^ (1 / 2 : ℝ) * n ≤
        3 * (w ^ 4 * n) := by
      have hwpos : 0 < w :=
        lt_of_lt_of_le (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hTOne) _) hW
      have hpow : w ^ (9 / 4 : ℝ) * w * w ^ (3 / 4 : ℝ) = w ^ 4 := by
        calc
          _ = w ^ (9 / 4 : ℝ) * w ^ (1 : ℝ) * w ^ (3 / 4 : ℝ) := by
            rw [Real.rpow_one]
          _ = w ^ ((9 / 4 : ℝ) + 1) * w ^ (3 / 4 : ℝ) := by
            rw [← Real.rpow_add hwpos]
          _ = w ^ ((9 / 4 : ℝ) + 1 + 3 / 4) := by
            rw [← Real.rpow_add hwpos]
          _ = w ^ 4 := by norm_num
      calc
        _ ≤ (3 * w ^ (9 / 4 : ℝ)) * w * w ^ (3 / 4 : ℝ) * n := by gcongr
        _ = 3 * (w ^ 4 * n) := by
          calc
            _ = 3 * (w ^ (9 / 4 : ℝ) * w * w ^ (3 / 4 : ℝ)) * n := by ring
            _ = 3 * w ^ 4 * n := by rw [hpow]
            _ = 3 * (w ^ 4 * n) := by ring
    nlinarith [mul_nonneg (by positivity : 0 ≤ w ^ 4) hn0]
  have hA0 : 0 ≤ gmLargeSecondPaperShape N T W := by
    unfold gmLargeSecondPaperShape
    positivity
  have hB0 : 0 ≤ gmLargeFourthPaperShape N T W := by
    unfold gmLargeFourthPaperShape
    positivity
  have hR0 : 0 ≤ 5 * n * w ^ 3 := by positivity
  apply sqrt_mul_sqrt_le_of_mul_le_sq hA0 hR0
  calc
    gmLargeSecondPaperShape N T W * gmLargeFourthPaperShape N T W ≤
        (3 * (w ^ 2 * n)) * (7 * (w ^ 4 * n)) :=
      mul_le_mul hA hB hB0 (by positivity)
    _ ≤ (5 * n * w ^ 3) ^ 2 := by nlinarith [sq_nonneg (n * w ^ 3)]

/-- Equation (11.6): in the complementary range `|W| ≤ T^(2/3)`, the
two square-rooted moment shapes are controlled by the two nontrivial terms
in Lemma 11.9. -/
theorem gmLargePaperShapes_small_card
    {N : ℕ} {T : ℝ} {W : Finset ℝ}
    (hT : 4 ≤ T) (hN : T ^ (3 / 4 : ℝ) ≤ (N : ℝ))
    (hSep : IsSeparated 1 W)
    (hW : (W.card : ℝ) ≤ T ^ (2 / 3 : ℝ)) :
    Real.sqrt (gmLargeSecondPaperShape N T W) *
        Real.sqrt (gmLargeFourthPaperShape N T W) ≤
      8 * ((N : ℝ) * T ^ (1 / 4 : ℝ) * (W.card : ℝ) ^ (21 / 8 : ℝ) +
        Real.sqrt (ApproxAddEnergy 1 W : ℝ) * Real.sqrt (W.card : ℝ) *
          (N : ℝ) ^ 2) := by
  by_cases hEmpty : W = ∅
  · subst W
    simp [gmLargeSecondPaperShape, gmLargeFourthPaperShape, ApproxAddEnergy]
  let w : ℝ := W.card
  let n : ℝ := N
  let E : ℝ := ApproxAddEnergy 1 W
  have hTOne : 1 ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTOne
  have hwone : 1 ≤ w := by
    dsimp only [w]
    exact_mod_cast Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)
  have hwpos : 0 < w := lt_of_lt_of_le zero_lt_one hwone
  have hn0 : 0 ≤ n := by dsimp only [n]; positivity
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hElower : w ^ 2 ≤ E := by
    dsimp only [w, E]
    exact_mod_cast card_sq_le_approxAddEnergy (by norm_num : (0 : ℝ) ≤ 1) W
  have hEpos : 0 < E := lt_of_lt_of_le (by positivity : 0 < w ^ 2) hElower
  have hwsqrt : w ^ (3 / 4 : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
    have hm := Real.rpow_le_rpow (le_of_lt hwpos) hW
      (by norm_num : (0 : ℝ) ≤ 3 / 4)
    calc
      w ^ (3 / 4 : ℝ) ≤ (T ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) := hm
      _ = T ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul (le_of_lt hTpos)]
        congr 1
        norm_num
  have hpowT : T ^ (1 / 2 : ℝ) * T ^ (3 / 4 : ℝ) =
      T ^ (5 / 4 : ℝ) := by
    rw [← Real.rpow_add hTpos]
    congr 1
    norm_num
  have hTrootN : T ≤ T ^ (1 / 2 : ℝ) * n := by
    calc
      T = T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ T ^ (5 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hTOne (by norm_num)
      _ = T ^ (1 / 2 : ℝ) * T ^ (3 / 4 : ℝ) := hpowT.symm
      _ ≤ T ^ (1 / 2 : ℝ) * n := by gcongr
  let a := w ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * n
  let b := w ^ 4 * n
  let c := E ^ (3 / 4 : ℝ) * w * T ^ (1 / 2 : ℝ) * n
  let p := n * T ^ (1 / 4 : ℝ) * w ^ (21 / 8 : ℝ)
  let q := Real.sqrt E * Real.sqrt w * n ^ 2
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hp0 : 0 ≤ p := by dsimp only [p]; positivity
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hwPow : w ^ 2 = w ^ (5 / 4 : ℝ) * w ^ (3 / 4 : ℝ) := by
    calc
      w ^ 2 = w ^ ((5 / 4 : ℝ) + 3 / 4) := by norm_num
      _ = _ := Real.rpow_add hwpos _ _
  have hA : gmLargeSecondPaperShape N T W ≤ 3 * a := by
    unfold gmLargeSecondPaperShape
    change w ^ 2 * n + w * T + a ≤ 3 * a
    have h₁ : w ^ 2 * n ≤ a := by
      dsimp only [a]
      rw [hwPow]
      gcongr
    have hw54 : w ≤ w ^ (5 / 4 : ℝ) := by
      calc
        w = w ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ w ^ (5 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hwone (by norm_num)
    have h₂ : w * T ≤ a := by
      dsimp only [a]
      calc
        w * T ≤ w * (T ^ (1 / 2 : ℝ) * n) := by gcongr
        _ ≤ w ^ (5 / 4 : ℝ) * (T ^ (1 / 2 : ℝ) * n) := by gcongr
        _ = _ := by ring
    nlinarith
  have hEquarter : E ^ (1 / 4 : ℝ) ≤ 3 * w := by
    have hEupper : E ≤ 3 * w ^ 3 := by
      dsimp only [E, w]
      exact_mod_cast approxAddEnergy_le_three_card_cubed W hSep
    have hm := Real.rpow_le_rpow hE0 hEupper (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hthree : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ 3 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    calc
      E ^ (1 / 4 : ℝ) ≤ (3 * w ^ 3) ^ (1 / 4 : ℝ) := hm
      _ = 3 ^ (1 / 4 : ℝ) * w ^ (3 / 4 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul (le_of_lt hwpos)]
        congr 2
        norm_num
      _ ≤ 3 * w ^ (3 / 4 : ℝ) := by gcongr
      _ ≤ 3 * w := by
        gcongr
        calc
          w ^ (3 / 4 : ℝ) ≤ w ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hwone (by norm_num)
          _ = w := by rw [Real.rpow_one]
  have hET : E * T ≤ 3 * c := by
    have hEsplit : E = E ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ) := by
      simpa only [show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one] using
        Real.rpow_add hEpos (3 / 4 : ℝ) (1 / 4 : ℝ)
    rw [hEsplit]
    dsimp only [c]
    calc
      E ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ) * T ≤
          E ^ (3 / 4 : ℝ) * (3 * w) * T := by gcongr
      _ ≤ E ^ (3 / 4 : ℝ) * (3 * w) *
            (T ^ (1 / 2 : ℝ) * n) := by
        exact mul_le_mul_of_nonneg_left hTrootN
          (mul_nonneg (Real.rpow_nonneg hE0 _)
            (mul_nonneg (by norm_num) hwpos.le))
      _ = 3 * (E ^ (3 / 4 : ℝ) * w * T ^ (1 / 2 : ℝ) * n) := by ring
  have hB : gmLargeFourthPaperShape N T W ≤ 4 * (b + c) := by
    unfold gmLargeFourthPaperShape
    change b + E * T + c ≤ 4 * (b + c)
    nlinarith
  have hab : a * b = p ^ 2 := by
    have hw : w ^ (5 / 4 : ℝ) * w ^ 4 = w ^ (21 / 4 : ℝ) := by
      rw [show w ^ 4 = w ^ (4 : ℝ) by norm_num, ← Real.rpow_add hwpos]
      congr 1
      norm_num
    have hTq : T ^ (1 / 4 : ℝ) * T ^ (1 / 4 : ℝ) =
        T ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hTpos]
      congr 1
      norm_num
    have hwq : w ^ (21 / 8 : ℝ) * w ^ (21 / 8 : ℝ) =
        w ^ (21 / 4 : ℝ) := by
      rw [← Real.rpow_add hwpos]
      congr 1
      norm_num
    dsimp only [a, b, p]
    rw [pow_two]
    calc
      w ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * n * (w ^ 4 * n) =
          (w ^ (5 / 4 : ℝ) * w ^ 4) * T ^ (1 / 2 : ℝ) * (n * n) := by ring
      _ = w ^ (21 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * (n * n) := by rw [hw]
      _ = (w ^ (21 / 8 : ℝ) * w ^ (21 / 8 : ℝ)) *
          (T ^ (1 / 4 : ℝ) * T ^ (1 / 4 : ℝ)) * (n * n) := by
        rw [hwq, hTq]
      _ = n * T ^ (1 / 4 : ℝ) * w ^ (21 / 8 : ℝ) *
          (n * T ^ (1 / 4 : ℝ) * w ^ (21 / 8 : ℝ)) := by ring
  have hEroot : w ^ (1 / 2 : ℝ) ≤ E ^ (1 / 4 : ℝ) := by
    have hm := Real.rpow_le_rpow (by positivity : 0 ≤ w ^ 2) hElower
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    calc
      w ^ (1 / 2 : ℝ) = (w ^ 2) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hwpos)]
        congr 1
        norm_num
      _ ≤ E ^ (1 / 4 : ℝ) := hm
  have hnSq : T ^ (3 / 2 : ℝ) ≤ n ^ 2 := by
    have hs := mul_self_le_mul_self (Real.rpow_nonneg hTpos.le _) hN
    calc
      T ^ (3 / 2 : ℝ) = (T ^ (3 / 4 : ℝ)) ^ 2 := by
        rw [pow_two, ← Real.rpow_add hTpos]
        congr 1
        norm_num
      _ ≤ n ^ 2 := by simpa only [n, pow_two] using hs
  have hwT : w ^ (3 / 4 : ℝ) * T ≤ n ^ 2 := by
    have hpow : T ^ (1 / 2 : ℝ) * T = T ^ (3 / 2 : ℝ) := by
      calc
        T ^ (1 / 2 : ℝ) * T = T ^ (1 / 2 : ℝ) * T ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = T ^ ((1 / 2 : ℝ) + 1) := by rw [← Real.rpow_add hTpos]
        _ = T ^ (3 / 2 : ℝ) := by norm_num
    calc
      _ ≤ T ^ (1 / 2 : ℝ) * T := by gcongr
      _ = T ^ (3 / 2 : ℝ) := hpow
      _ ≤ n ^ 2 := hnSq
  have hac : a * c ≤ q ^ 2 := by
    have hscale : w ^ (5 / 4 : ℝ) * T ≤ E ^ (1 / 4 : ℝ) * n ^ 2 := by
      have hwSplit : w ^ (5 / 4 : ℝ) =
          w ^ (1 / 2 : ℝ) * w ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_add hwpos]
        congr 1
        norm_num
      rw [hwSplit]
      calc
        w ^ (1 / 2 : ℝ) * w ^ (3 / 4 : ℝ) * T =
            w ^ (1 / 2 : ℝ) * (w ^ (3 / 4 : ℝ) * T) := by ring
        _ ≤ E ^ (1 / 4 : ℝ) * (w ^ (3 / 4 : ℝ) * T) := by
          exact mul_le_mul_of_nonneg_right hEroot (by positivity)
        _ ≤ E ^ (1 / 4 : ℝ) * n ^ 2 := by gcongr
    have hEsplit : E = E ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ) := by
      simpa only [show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one] using
        Real.rpow_add hEpos (3 / 4 : ℝ) (1 / 4 : ℝ)
    have hqSq : q ^ 2 = E * w * n ^ 4 := by
      dsimp only [q]
      calc
        (Real.sqrt E * Real.sqrt w * n ^ 2) ^ 2 =
            (Real.sqrt E) ^ 2 * (Real.sqrt w) ^ 2 * (n ^ 2) ^ 2 := by ring
        _ = E * w * (n ^ 2) ^ 2 := by rw [Real.sq_sqrt hE0, Real.sq_sqrt hwpos.le]
        _ = E * w * n ^ 4 := by ring
    calc
      a * c = E ^ (3 / 4 : ℝ) * (w ^ (5 / 4 : ℝ) * T) * w * n ^ 2 := by
        dsimp only [a, c]
        have hroot : T ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) = T := by
          simpa only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one] using
            (Real.rpow_add hTpos (1 / 2 : ℝ) (1 / 2 : ℝ)).symm
        rw [show
          (w ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * n) *
              (E ^ (3 / 4 : ℝ) * w * T ^ (1 / 2 : ℝ) * n) =
            E ^ (3 / 4 : ℝ) * (w ^ (5 / 4 : ℝ) *
              (T ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ))) * w * n ^ 2 by ring,
          hroot]
      _ = (w ^ (5 / 4 : ℝ) * T) *
            (E ^ (3 / 4 : ℝ) * w * n ^ 2) := by ring
      _ ≤ (E ^ (1 / 4 : ℝ) * n ^ 2) *
            (E ^ (3 / 4 : ℝ) * w * n ^ 2) := by
        exact mul_le_mul_of_nonneg_right hscale
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg hE0 _) hwpos.le) (sq_nonneg n))
      _ = E ^ (3 / 4 : ℝ) * (E ^ (1 / 4 : ℝ) * n ^ 2) * w * n ^ 2 := by ring
      _ = (E ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ)) * w * n ^ 4 := by
        ring
      _ = E * w * n ^ 4 := by rw [← hEsplit]
      _ = q ^ 2 := hqSq.symm
  have hA0 : 0 ≤ gmLargeSecondPaperShape N T W := by
    unfold gmLargeSecondPaperShape
    positivity
  have hB0 : 0 ≤ gmLargeFourthPaperShape N T W := by
    unfold gmLargeFourthPaperShape
    positivity
  have hR0 : 0 ≤ 8 * (p + q) := by positivity
  change Real.sqrt (gmLargeSecondPaperShape N T W) *
      Real.sqrt (gmLargeFourthPaperShape N T W) ≤ 8 * (p + q)
  apply sqrt_mul_sqrt_le_of_mul_le_sq hA0 hR0
  calc
    gmLargeSecondPaperShape N T W * gmLargeFourthPaperShape N T W ≤
        (3 * a) * (4 * (b + c)) := mul_le_mul hA hB hB0 (by positivity)
    _ ≤ (8 * (p + q)) ^ 2 := by
      calc
        (3 * a) * (4 * (b + c)) = 12 * (a * b + a * c) := by ring
        _ ≤ 12 * (p ^ 2 + q ^ 2) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hab.le hac) (by norm_num)
        _ ≤ 12 * (p + q) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [show (p + q) ^ 2 = p ^ 2 + q ^ 2 + 2 * (p * q) by ring]
          exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (mul_nonneg hp0 hq0))
        _ ≤ 64 * (p + q) ^ 2 := by
          exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
        _ = (8 * (p + q)) ^ 2 := by ring

/-- The two case computations (11.5)--(11.6), combined in the exact
three-term shape used by Lemma 11.9. -/
theorem gmLargePaperShapes_native
    {N : ℕ} {T : ℝ} {W : Finset ℝ}
    (hT : 4 ≤ T) (hN : T ^ (3 / 4 : ℝ) ≤ (N : ℝ))
    (hSep : IsSeparated 1 W) :
    Real.sqrt (gmLargeSecondPaperShape N T W) *
        Real.sqrt (gmLargeFourthPaperShape N T W) ≤
      8 * ((N : ℝ) * (W.card : ℝ) ^ 3 +
        (N : ℝ) * T ^ (1 / 4 : ℝ) * (W.card : ℝ) ^ (21 / 8 : ℝ) +
        Real.sqrt (ApproxAddEnergy 1 W : ℝ) * Real.sqrt (W.card : ℝ) *
          (N : ℝ) ^ 2) := by
  rcases le_total (W.card : ℝ) (T ^ (2 / 3 : ℝ)) with hsmall | hlarge
  · have h := gmLargePaperShapes_small_card hT hN hSep hsmall
    calc
      _ ≤ 8 * ((N : ℝ) * T ^ (1 / 4 : ℝ) *
          (W.card : ℝ) ^ (21 / 8 : ℝ) +
          Real.sqrt (ApproxAddEnergy 1 W : ℝ) * Real.sqrt (W.card : ℝ) *
            (N : ℝ) ^ 2) := h
      _ ≤ _ := by
        have hx : 0 ≤ (N : ℝ) * (W.card : ℝ) ^ 3 := by positivity
        linarith
  · have h := gmLargePaperShapes_large_card hT hN hSep hlarge
    calc
      _ ≤ 5 * (N : ℝ) * (W.card : ℝ) ^ 3 := h
      _ ≤ _ := by
        have hx : 0 ≤ (N : ℝ) * (W.card : ℝ) ^ 3 := by positivity
        have hy : 0 ≤ (N : ℝ) * T ^ (1 / 4 : ℝ) *
            (W.card : ℝ) ^ (21 / 8 : ℝ) := by positivity
        have hz : 0 ≤ Real.sqrt (ApproxAddEnergy 1 W : ℝ) *
            Real.sqrt (W.card : ℝ) * (N : ℝ) ^ 2 := by positivity
        nlinarith

theorem sqrt_product_le_common_mul
    {F A B X Y : ℝ} (hF : 0 ≤ F)
    (hX : X ≤ F * A) (hY : Y ≤ F * B) :
    Real.sqrt X * Real.sqrt Y ≤
      F * (Real.sqrt A * Real.sqrt B) := by
  have hsX := Real.sqrt_le_sqrt hX
  have hsY := Real.sqrt_le_sqrt hY
  calc
    Real.sqrt X * Real.sqrt Y ≤ Real.sqrt (F * A) * Real.sqrt (F * B) :=
      mul_le_mul hsX hsY (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = F * (Real.sqrt A * Real.sqrt B) := by
      rw [Real.sqrt_mul hF, Real.sqrt_mul hF]
      calc
        Real.sqrt F * Real.sqrt A * (Real.sqrt F * Real.sqrt B) =
            (Real.sqrt F) ^ 2 * (Real.sqrt A * Real.sqrt B) := by ring
        _ = F * (Real.sqrt A * Real.sqrt B) := by rw [Real.sq_sqrt hF]

/-- Lemma 11.9 for the physical middle range `D ≤ d ≤ N`, after the
cutoff, harmonic losses, and the two cardinality regimes have all been
assembled. -/
theorem gmMiddleGcdThirdMoment_physical_native
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4 ≤ T₀ ∧
      ∀ {N : ℕ} {T : ℝ} (W : Finset ℝ),
        T₀ ≤ T → (N : ℝ) ≤ T →
        T ^ (3 / 4 : ℝ) ≤ (N : ℝ) →
        IsSeparated 1 W → InBaseInterval T W →
        gmMiddleGcdThirdMoment N (gmGcdCutoff N T) W ≤
          C * T ^ ε *
            ((N : ℝ) * (W.card : ℝ) ^ 3 +
              (N : ℝ) * T ^ (1 / 4 : ℝ) *
                (W.card : ℝ) ^ (21 / 8 : ℝ) +
              Real.sqrt (ApproxAddEnergy 1 W : ℝ) *
                Real.sqrt (W.card : ℝ) * (N : ℝ) ^ 2) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp only [η]; linarith
  obtain ⟨C₁, T₁, hC₁, hT₁, hmid⟩ := gmMiddleGcdThirdMoment_native η hη
  let T₀ := max 4 T₁
  let K := 32 * C₁ * (1 + η⁻¹)
  refine ⟨K, T₀, by dsimp only [K]; positivity, le_max_left _ _, ?_⟩
  intro N T W hT hNT hN hSep hBase
  have hFour : 4 ≤ T := (le_max_left 4 T₁).trans hT
  have hOne : 1 ≤ T := by linarith
  have hT₁' : T₁ ≤ T := (le_max_right 4 T₁).trans hT
  have hTwo := two_le_sq_div_of_three_quarters_le hFour hN
  have hD := (gmGcdCutoff_bounds hTwo).1
  have hA := gmLargeSecondAggregateShape_le_paper (W := W) hη hOne hNT hTwo
  have hB := gmLargeFourthAggregateShape_le_paper (W := W) hη hOne hNT hTwo
  let F := 4 * (1 + η⁻¹) * T ^ η
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hPaper := gmLargePaperShapes_native hFour hN hSep
  have hAgg :
      Real.sqrt (gmLargeSecondAggregateShape N (gmGcdCutoff N T) T W) *
          Real.sqrt (gmLargeFourthAggregateShape N (gmGcdCutoff N T) T W) ≤
        F * 8 *
          ((N : ℝ) * (W.card : ℝ) ^ 3 +
            (N : ℝ) * T ^ (1 / 4 : ℝ) *
              (W.card : ℝ) ^ (21 / 8 : ℝ) +
            Real.sqrt (ApproxAddEnergy 1 W : ℝ) *
              Real.sqrt (W.card : ℝ) * (N : ℝ) ^ 2) := by
    calc
      _ ≤ F * (Real.sqrt (gmLargeSecondPaperShape N T W) *
          Real.sqrt (gmLargeFourthPaperShape N T W)) := by
        apply sqrt_product_le_common_mul hF0
        · simpa only [F] using hA
        · simpa only [F] using hB
      _ ≤ F * (8 *
          ((N : ℝ) * (W.card : ℝ) ^ 3 +
            (N : ℝ) * T ^ (1 / 4 : ℝ) *
              (W.card : ℝ) ^ (21 / 8 : ℝ) +
            Real.sqrt (ApproxAddEnergy 1 W : ℝ) *
              Real.sqrt (W.card : ℝ) * (N : ℝ) ^ 2)) := by gcongr
      _ = _ := by ring
  have hm := hmid W hD hT₁' hNT hSep hBase
  calc
    gmMiddleGcdThirdMoment N (gmGcdCutoff N T) W ≤
        C₁ * T ^ η *
          (Real.sqrt (gmLargeSecondAggregateShape N (gmGcdCutoff N T) T W) *
            Real.sqrt (gmLargeFourthAggregateShape N (gmGcdCutoff N T) T W)) := by
      simpa only [mul_assoc] using hm
    _ ≤ C₁ * T ^ η * (F * 8 *
          ((N : ℝ) * (W.card : ℝ) ^ 3 +
            (N : ℝ) * T ^ (1 / 4 : ℝ) *
              (W.card : ℝ) ^ (21 / 8 : ℝ) +
            Real.sqrt (ApproxAddEnergy 1 W : ℝ) *
              Real.sqrt (W.card : ℝ) * (N : ℝ) ^ 2)) := by gcongr
    _ = K * T ^ ε *
          ((N : ℝ) * (W.card : ℝ) ^ 3 +
            (N : ℝ) * T ^ (1 / 4 : ℝ) *
              (W.card : ℝ) ^ (21 / 8 : ℝ) +
            Real.sqrt (ApproxAddEnergy 1 W : ℝ) *
              Real.sqrt (W.card : ℝ) * (N : ℝ) ^ 2) := by
      dsimp only [K, F, η]
      have hp : T ^ (ε / 2) * T ^ (ε / 2) = T ^ ε := by
        rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hOne)]
        congr 1
        ring
      rw [show C₁ * T ^ (ε / 2) *
          (4 * (1 + (ε / 2)⁻¹) * T ^ (ε / 2) * 8 *
            ((N : ℝ) * (W.card : ℝ) ^ 3 +
              (N : ℝ) * T ^ (1 / 4 : ℝ) * (W.card : ℝ) ^ (21 / 8 : ℝ) +
              Real.sqrt (ApproxAddEnergy 1 W : ℝ) * Real.sqrt (W.card : ℝ) *
                (N : ℝ) ^ 2)) =
          32 * C₁ * (1 + (ε / 2)⁻¹) *
            (T ^ (ε / 2) * T ^ (ε / 2)) *
            ((N : ℝ) * (W.card : ℝ) ^ 3 +
              (N : ℝ) * T ^ (1 / 4 : ℝ) * (W.card : ℝ) ^ (21 / 8 : ℝ) +
              Real.sqrt (ApproxAddEnergy 1 W : ℝ) * Real.sqrt (W.card : ℝ) *
                (N : ℝ) ^ 2) by ring, hp]

/-- The `gmLargeGcdThirdMoment` definition used by the source-facing construction in `LargeValuesEnergyFinal`. -/
noncomputable def gmLargeGcdThirdMoment
    (N D : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc D (2 * N), gmGcdSliceMoment 3 N d W

theorem gmLargeGcdThirdMoment_eq_middle_add_diagonal
    {N D : ℕ} {W : Finset ℝ} (hDN : D ≤ N) :
    gmLargeGcdThirdMoment N D W =
      gmMiddleGcdThirdMoment N D W + gmDiagonalGcdThirdMoment N W := by
  have hUnion : Finset.Icc D N ∪ Finset.Ioc N (2 * N) =
      Finset.Icc D (2 * N) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hDisj : Disjoint (Finset.Icc D N) (Finset.Ioc N (2 * N)) := by
    rw [Finset.disjoint_left]
    intro d hd₁ hd₂
    exact (not_lt_of_ge (Finset.mem_Icc.mp hd₁).2) (Finset.mem_Ioc.mp hd₂).1
  unfold gmLargeGcdThirdMoment gmMiddleGcdThirdMoment gmDiagonalGcdThirdMoment
  rw [← hUnion, Finset.sum_union hDisj]

/-- Guth--Maynard Lemma 11.9, including the diagonal quotient-one tail
`N < d ≤ 2N`. -/
theorem gmLargeGcdThirdMoment_native
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4 ≤ T₀ ∧
      ∀ {N : ℕ} {T : ℝ} (W : Finset ℝ),
        T₀ ≤ T → (N : ℝ) ≤ T →
        T ^ (3 / 4 : ℝ) ≤ (N : ℝ) →
        IsSeparated 1 W → InBaseInterval T W →
        gmLargeGcdThirdMoment N (gmGcdCutoff N T) W ≤
          C * T ^ ε *
            ((N : ℝ) * (W.card : ℝ) ^ 3 +
              (N : ℝ) * T ^ (1 / 4 : ℝ) *
                (W.card : ℝ) ^ (21 / 8 : ℝ) +
              Real.sqrt (ApproxAddEnergy 1 W : ℝ) *
                Real.sqrt (W.card : ℝ) * (N : ℝ) ^ 2) := by
  obtain ⟨C₁, T₀, hC₁, hT₀, hmid⟩ :=
    gmMiddleGcdThirdMoment_physical_native ε hε
  let C := C₁ + 1
  refine ⟨C, T₀, by dsimp only [C]; linarith, hT₀, ?_⟩
  intro N T W hT hNT hN hSep hBase
  have hFour : 4 ≤ T := hT₀.trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTOne
  have hNposCast : (0 : ℝ) < N :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hTpos _) hN
  have hNpos : 0 < N := by exact_mod_cast hNposCast
  have hDN := gmGcdCutoff_le_N hTpos hNpos hNT
  have hm := hmid W hT hNT hN hSep hBase
  have hd := gmDiagonalGcdThirdMoment_le (N := N) W
  let S := (N : ℝ) * (W.card : ℝ) ^ 3 +
    (N : ℝ) * T ^ (1 / 4 : ℝ) * (W.card : ℝ) ^ (21 / 8 : ℝ) +
    Real.sqrt (ApproxAddEnergy 1 W : ℝ) * Real.sqrt (W.card : ℝ) *
      (N : ℝ) ^ 2
  have hS0 : 0 ≤ S := by dsimp only [S]; positivity
  have hfirst : (N : ℝ) * (W.card : ℝ) ^ 3 ≤ S := by
    dsimp only [S]
    have h₂ : 0 ≤ (N : ℝ) * T ^ (1 / 4 : ℝ) *
        (W.card : ℝ) ^ (21 / 8 : ℝ) := by positivity
    have h₃ : 0 ≤ Real.sqrt (ApproxAddEnergy 1 W : ℝ) *
        Real.sqrt (W.card : ℝ) * (N : ℝ) ^ 2 := by positivity
    linarith
  have hpow : 1 ≤ T ^ ε := Real.one_le_rpow hTOne hε.le
  rw [gmLargeGcdThirdMoment_eq_middle_add_diagonal hDN]
  calc
    gmMiddleGcdThirdMoment N (gmGcdCutoff N T) W +
        gmDiagonalGcdThirdMoment N W ≤
      C₁ * T ^ ε * S + (N : ℝ) * (W.card : ℝ) ^ 3 :=
        add_le_add (by simpa only [S] using hm) hd
    _ ≤ C₁ * T ^ ε * S + T ^ ε * S := by
      apply add_le_add le_rfl
      calc
        (N : ℝ) * (W.card : ℝ) ^ 3 ≤ S := hfirst
        _ = 1 * S := by ring
        _ ≤ T ^ ε * S := mul_le_mul_of_nonneg_right hpow hS0
    _ = C * T ^ ε * S := by dsimp only [C]; ring

theorem gmDiscreteRatioThirdMoment_le_small_add_large
    {N D : ℕ} {W : Finset ℝ} (hD : 0 < D) (hDtop : D ≤ 2 * N) :
    gmDiscreteRatioMoment 3 N W ≤
      gmSmallGcdThirdMoment N D W + gmLargeGcdThirdMoment N D W := by
  have hUnion : Finset.Icc 1 (D - 1) ∪ Finset.Icc D (2 * N) =
      Finset.Icc 1 (2 * N) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hDisj : Disjoint (Finset.Icc 1 (D - 1)) (Finset.Icc D (2 * N)) := by
    rw [Finset.disjoint_left]
    intro d hd₁ hd₂
    simp only [Finset.mem_Icc] at hd₁ hd₂
    omega
  unfold gmSmallGcdThirdMoment gmLargeGcdThirdMoment
  rw [gmDiscreteRatioMoment_eq_sum_gcdSlices, ← hUnion, Finset.sum_union hDisj]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      simp only [Finset.mem_Icc] at hd ⊢
      omega
    · intro d hd hdnot
      unfold gmGcdSliceMoment
      positivity
  · exact le_rfl

/-- Lemmas 11.8 and 11.9 joined at the physical cutoff. -/
theorem gmDiscreteRatioThirdMoment_physical_native
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4 ≤ T₀ ∧
      ∀ {N : ℕ} {T : ℝ} (W : Finset ℝ),
        T₀ ≤ T → (N : ℝ) ≤ T →
        T ^ (3 / 4 : ℝ) ≤ (N : ℝ) →
        IsSeparated 1 W → InBaseInterval T W →
        gmDiscreteRatioMoment 3 N W ≤
          C * T ^ ε *
            ((N : ℝ) * (W.card : ℝ) ^ 3 +
              (N : ℝ) * T ^ (1 / 4 : ℝ) *
                (W.card : ℝ) ^ (21 / 8 : ℝ) +
              Real.sqrt (ApproxAddEnergy 1 W : ℝ) *
                Real.sqrt (W.card : ℝ) * (N : ℝ) ^ 2) := by
  obtain ⟨Cₛ, Tₛ, hCₛ, hTₛ, hsmall⟩ := gmSmallGcdThirdMoment_native ε hε
  obtain ⟨Cₗ, Tₗ, hCₗ, hTₗ, hlarge⟩ := gmLargeGcdThirdMoment_native ε hε
  let T₀ := max Tₛ Tₗ
  let C := 2 * Cₛ + Cₗ
  refine ⟨C, T₀, by dsimp only [C]; positivity,
    le_max_of_le_right hTₗ, ?_⟩
  intro N T W hT hNT hN hSep hBase
  have hTs : Tₛ ≤ T := (le_max_left Tₛ Tₗ).trans hT
  have hTl : Tₗ ≤ T := (le_max_right Tₛ Tₗ).trans hT
  have hFour : 4 ≤ T := hTₗ.trans hTl
  have hTpos : 0 < T := by linarith
  have hNposCast : (0 : ℝ) < N :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hTpos _) hN
  have hNpos : 0 < N := by exact_mod_cast hNposCast
  have hTwo := two_le_sq_div_of_three_quarters_le hFour hN
  obtain ⟨hD, hDlower, hDupper⟩ := gmGcdCutoff_bounds hTwo
  have hDN := gmGcdCutoff_le_N hTpos hNpos hNT
  have hDtop : gmGcdCutoff N T ≤ 2 * N := hDN.trans (by omega)
  have hs := hsmall (D := gmGcdCutoff N T) W hNpos hTs hNT hSep hBase
  have hl := hlarge W hTl hNT hN hSep hBase
  let S := (N : ℝ) * (W.card : ℝ) ^ 3 +
    (N : ℝ) * T ^ (1 / 4 : ℝ) * (W.card : ℝ) ^ (21 / 8 : ℝ) +
    Real.sqrt (ApproxAddEnergy 1 W : ℝ) * Real.sqrt (W.card : ℝ) *
      (N : ℝ) ^ 2
  let q := Real.sqrt (ApproxAddEnergy 1 W : ℝ) *
    Real.sqrt (W.card : ℝ) * (N : ℝ) ^ 2
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hqS : q ≤ S := by
    dsimp only [q, S]
    have h₁ : 0 ≤ (N : ℝ) * (W.card : ℝ) ^ 3 := by positivity
    have h₂ : 0 ≤ (N : ℝ) * T ^ (1 / 4 : ℝ) *
        (W.card : ℝ) ^ (21 / 8 : ℝ) := by positivity
    linarith
  have hDT : (gmGcdCutoff N T : ℝ) * T ≤ (N : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hDupper hTpos.le
    field_simp [hTpos.ne'] at this
    nlinarith
  have hsmallShape :
      ((gmGcdCutoff N T : ℝ) * T + (N : ℝ) ^ 2) *
          Real.sqrt (W.card : ℝ) *
            Real.sqrt (ApproxAddEnergy 1 W : ℝ) ≤ 2 * q := by
    dsimp only [q]
    have hsqrtW : 0 ≤ Real.sqrt (W.card : ℝ) := Real.sqrt_nonneg _
    have hsqrtE : 0 ≤ Real.sqrt (ApproxAddEnergy 1 W : ℝ) := Real.sqrt_nonneg _
    calc
      _ ≤ (2 * (N : ℝ) ^ 2) * Real.sqrt (W.card : ℝ) *
          Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by gcongr; linarith
      _ = 2 * (Real.sqrt (ApproxAddEnergy 1 W : ℝ) *
          Real.sqrt (W.card : ℝ) * (N : ℝ) ^ 2) := by ring
  rw [show C * T ^ ε * S =
      (2 * Cₛ + Cₗ) * T ^ ε * S by rfl]
  calc
    gmDiscreteRatioMoment 3 N W ≤
        gmSmallGcdThirdMoment N (gmGcdCutoff N T) W +
          gmLargeGcdThirdMoment N (gmGcdCutoff N T) W :=
      gmDiscreteRatioThirdMoment_le_small_add_large hD hDtop
    _ ≤ Cₛ * T ^ ε *
          (((gmGcdCutoff N T : ℝ) * T + (N : ℝ) ^ 2) *
            Real.sqrt (W.card : ℝ) * Real.sqrt (ApproxAddEnergy 1 W : ℝ)) +
        Cₗ * T ^ ε * S := add_le_add (by simpa only [mul_assoc] using hs)
          (by simpa only [S] using hl)
    _ ≤ Cₛ * T ^ ε * (2 * q) + Cₗ * T ^ ε * S := by gcongr
    _ ≤ Cₛ * T ^ ε * (2 * S) + Cₗ * T ^ ε * S := by gcongr
    _ = (2 * Cₛ + Cₗ) * T ^ ε * S := by ring

theorem energy_sqrt_term_rearrangement
    {E V L A B : ℝ} (hE : 0 ≤ E) (hV : 0 < V) (hL : 0 ≤ L)
    (hB : 0 ≤ B)
    (h : E * V ^ 2 ≤ L * (A + Real.sqrt E * B)) :
    E ≤ 2 * L * A / V ^ 2 + (L * B / V ^ 2) ^ 2 := by
  have hV2 : 0 < V ^ 2 := sq_pos_of_pos hV
  have hdiv : E ≤ L * A / V ^ 2 + (L * B / V ^ 2) * Real.sqrt E := by
    have heq : L * A / V ^ 2 + (L * B / V ^ 2) * Real.sqrt E =
        L * (A + Real.sqrt E * B) / V ^ 2 := by
      field_simp [hV2.ne']
    rw [heq, le_div_iff₀ hV2]
    exact h
  have hs := Real.sq_sqrt hE
  have hx : 0 ≤ L * B / V ^ 2 := by positivity
  have hyoung : 2 * (L * B / V ^ 2) * Real.sqrt E ≤
      (L * B / V ^ 2) ^ 2 + E := by
    nlinarith [sq_nonneg (Real.sqrt E - L * B / V ^ 2)]
  have htwo := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
  calc
    E ≤ 2 * (L * A / V ^ 2) + (L * B / V ^ 2) ^ 2 := by
      linarith
    _ = 2 * L * A / V ^ 2 + (L * B / V ^ 2) ^ 2 := by ring

set_option maxHeartbeats 1000000 in
/-- Guth--Maynard Proposition 11.1, with all `T^{o(1)}` losses represented
by the project's explicit epsilon-power quantifiers. -/
theorem gmEnergy_prop11_1_native
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4 ≤ T₀ ∧
      ∀ (N : ℕ) (T σ : ℝ) (W : Finset ℝ) (b : ℕ → ℂ),
        0 < N → T₀ ≤ T → (N : ℝ) ≤ T →
        T ^ (3 / 4 : ℝ) ≤ (N : ℝ) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) →
        (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖sourceDirichletPoly N b t‖) →
        (ApproxAddEnergy 1 W : ℝ) ≤
          C * T ^ ε *
            ((W.card : ℝ) * (N : ℝ) ^ (4 - 4 * σ) +
              (W.card : ℝ) ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) *
                (N : ℝ) ^ (1 - 2 * σ) +
              (W.card : ℝ) ^ 3 * (N : ℝ) ^ (1 - 2 * σ)) := by
  let μ := ε / 4
  have hμ : 0 < μ := by dsimp only [μ]; linarith
  obtain ⟨Cₑ, Tₑ, hCₑ, hTₑ, henergy⟩ := gmApproxAddEnergy_largeValues_native μ hμ
  obtain ⟨Cₘ, Tₘ, hCₘ, hTₘ, hmoment⟩ :=
    gmDiscreteRatioThirdMoment_physical_native μ hμ
  let T₀ := max Tₑ Tₘ
  let K := Cₑ * Cₘ
  let C := 2 * K + K ^ 2
  refine ⟨C, T₀, by dsimp only [C, K]; positivity,
    le_max_of_le_right hTₘ, ?_⟩
  intro N T σ W b hN hT hNT hNscale hSep hBase hb hLarge
  have hTe : Tₑ ≤ T := (le_max_left Tₑ Tₘ).trans hT
  have hTm : Tₘ ≤ T := (le_max_right Tₑ Tₘ).trans hT
  have hFour : 4 ≤ T := hTₘ.trans hTm
  have hTOne : 1 ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTOne
  have hnpos : (0 : ℝ) < N := by exact_mod_cast hN
  let n : ℝ := N
  let w : ℝ := W.card
  let E : ℝ := ApproxAddEnergy 1 W
  let V := n ^ σ
  let A := n * w ^ 3 + n * T ^ (1 / 4 : ℝ) * w ^ (21 / 8 : ℝ)
  let B := Real.sqrt w * n ^ 2
  let L := K * T ^ (2 * μ)
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hVpos : 0 < V := by dsimp only [V, n]; exact Real.rpow_pos_of_pos hnpos σ
  have hA0 : 0 ≤ A := by dsimp only [A, n, w]; positivity
  have hB0 : 0 ≤ B := by dsimp only [B, n, w]; positivity
  have hL0 : 0 ≤ L := by dsimp only [L, K]; positivity
  have he := henergy N T V W b hN hTe hNT hVpos.le hSep hb (by
    intro t ht
    simpa only [V, n] using hLarge t ht)
  have hm := hmoment W hTm hNT hNscale hSep hBase
  have hinput : E * V ^ 2 ≤ L * (A + Real.sqrt E * B) := by
    calc
      E * V ^ 2 ≤ Cₑ * T ^ μ * gmDiscreteRatioMoment 3 N W := by
        simpa only [E, V, n] using he
      _ ≤ Cₑ * T ^ μ * (Cₘ * T ^ μ *
          (n * w ^ 3 + n * T ^ (1 / 4 : ℝ) * w ^ (21 / 8 : ℝ) +
            Real.sqrt E * Real.sqrt w * n ^ 2)) := by gcongr
      _ = L * (A + Real.sqrt E * B) := by
        dsimp only [L, K, A, B]
        rw [show T ^ (2 * μ) = T ^ μ * T ^ μ by
          simpa only [two_mul] using Real.rpow_add hTpos μ μ]
        ring
  have hrearr := energy_sqrt_term_rearrangement hE0 hVpos hL0 hB0 hinput
  have hV2 : V ^ 2 = n ^ (2 * σ) := by
    dsimp only [V]
    rw [pow_two, ← Real.rpow_add (by simpa only [n] using hnpos)]
    congr 1
    ring
  have hV4 : V ^ 4 = n ^ (4 * σ) := by
    dsimp only [V]
    calc
      (n ^ σ) ^ 4 = n ^ σ * n ^ σ * n ^ σ * n ^ σ := by ring
      _ = n ^ (σ + σ + σ + σ) := by
        rw [Real.rpow_add (by simpa only [n] using hnpos),
          Real.rpow_add (by simpa only [n] using hnpos),
          Real.rpow_add (by simpa only [n] using hnpos)]
      _ = n ^ (4 * σ) := by congr 1; ring
  have hnSubOne : n ^ (1 - 2 * σ) = n / n ^ (2 * σ) := by
    rw [Real.rpow_sub (by simpa only [n] using hnpos), Real.rpow_one]
  have hnSubFour : n ^ (4 - 4 * σ) = n ^ 4 / n ^ (4 * σ) := by
    rw [Real.rpow_sub (by simpa only [n] using hnpos)]
    norm_num
  have hX : A / V ^ 2 =
      w ^ 3 * n ^ (1 - 2 * σ) +
        w ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * n ^ (1 - 2 * σ) := by
    dsimp only [A]
    rw [hV2, hnSubOne]
    field_simp [(Real.rpow_pos_of_pos (by simpa only [n] using hnpos) (2 * σ)).ne']
  have hBsq : B ^ 2 = w * n ^ 4 := by
    dsimp only [B]
    calc
      (Real.sqrt w * n ^ 2) ^ 2 = (Real.sqrt w) ^ 2 * n ^ 4 := by ring
      _ = w * n ^ 4 := by rw [Real.sq_sqrt (by dsimp only [w]; positivity)]
  have hY : B ^ 2 / V ^ 4 = w * n ^ (4 - 4 * σ) := by
    rw [hBsq, hV4, hnSubFour]
    field_simp [(Real.rpow_pos_of_pos (by simpa only [n] using hnpos) (4 * σ)).ne']
  have hPowHalf : T ^ (2 * μ) ≤ T ^ ε := by
    apply Real.rpow_le_rpow_of_exponent_le hTOne
    dsimp only [μ]
    linarith
  have hPowSq : (T ^ (2 * μ)) ^ 2 = T ^ ε := by
    rw [pow_two, ← Real.rpow_add hTpos]
    dsimp only [μ]
    congr 1
    ring
  let X := w ^ 3 * n ^ (1 - 2 * σ) +
    w ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * n ^ (1 - 2 * σ)
  let Y := w * n ^ (4 - 4 * σ)
  let S := Y + X
  have hX0 : 0 ≤ X := by dsimp only [X, n, w]; positivity
  have hY0 : 0 ≤ Y := by dsimp only [Y, n, w]; positivity
  have hS0 : 0 ≤ S := by dsimp only [S]; positivity
  have hrearr' : E ≤
      2 * K * T ^ (2 * μ) * X + K ^ 2 * (T ^ (2 * μ)) ^ 2 * Y := by
    calc
      E ≤ 2 * L * A / V ^ 2 + (L * B / V ^ 2) ^ 2 := hrearr
      _ = 2 * K * T ^ (2 * μ) * X +
          K ^ 2 * (T ^ (2 * μ)) ^ 2 * Y := by
        have hBV : (B / V ^ 2) ^ 2 = B ^ 2 / V ^ 4 := by
          field_simp [hVpos.ne']
        dsimp only [L]
        rw [show 2 * (K * T ^ (2 * μ)) * A / V ^ 2 =
            2 * K * T ^ (2 * μ) * (A / V ^ 2) by ring, hX]
        rw [show (K * T ^ (2 * μ) * B / V ^ 2) ^ 2 =
            K ^ 2 * (T ^ (2 * μ)) ^ 2 * (B / V ^ 2) ^ 2 by ring,
          hBV, hY]
  calc
    E ≤ 2 * K * T ^ (2 * μ) * X +
        K ^ 2 * (T ^ (2 * μ)) ^ 2 * Y := hrearr'
    _ ≤ 2 * K * T ^ ε * X + K ^ 2 * T ^ ε * Y := by
      rw [hPowSq]
      gcongr
    _ ≤ (2 * K + K ^ 2) * T ^ ε * S := by
      dsimp only [S]
      have hK0 : 0 ≤ K := by dsimp only [K]; positivity
      nlinarith [mul_nonneg (mul_nonneg hK0 (Real.rpow_nonneg hTpos.le ε)) hY0,
        mul_nonneg (mul_nonneg (sq_nonneg K) (Real.rpow_nonneg hTpos.le ε)) hX0]
    _ = C * T ^ ε *
        (w * n ^ (4 - 4 * σ) +
          w ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * n ^ (1 - 2 * σ) +
          w ^ 3 * n ^ (1 - 2 * σ)) := by
      dsimp only [C, S, X, Y]
      ring

/-! ## Proposition 10.1 in the source-facing scale -/

theorem sqrt_add_le_add_sqrt {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (A + B) ≤ Real.sqrt A + Real.sqrt B := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · rw [add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
    nlinarith [mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]

theorem sqrt_pow_six_mul_sq
    {Q X : ℝ} (hQ : 0 ≤ Q) (hX : 0 ≤ X) :
    Real.sqrt (Q ^ 6 * X ^ 2) = Q ^ 3 * X := by
  rw [Real.sqrt_mul (pow_nonneg hQ 6), Real.sqrt_sq hX]
  rw [show Q ^ 6 = (Q ^ 3) ^ 2 by ring, Real.sqrt_sq (pow_nonneg hQ 3)]

theorem sqrt_pow_four_mul
    {Q X : ℝ} (hQ : 0 ≤ Q) :
    Real.sqrt (Q ^ 4 * X) = Q ^ 2 * Real.sqrt X := by
  rw [Real.sqrt_mul (pow_nonneg hQ 4)]
  rw [show Q ^ 4 = (Q ^ 2) ^ 2 by ring, Real.sqrt_sq (pow_nonneg hQ 2)]

theorem sqrt_rpow_eq_rpow_half
    {x a : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x ^ a) = x ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

theorem sqrt_rpow_mul_rpow
    {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x ^ a * y ^ b) = x ^ (a / 2) * y ^ (b / 2) := by
  rw [Real.sqrt_mul (Real.rpow_nonneg hx a),
    sqrt_rpow_eq_rpow_half hx, sqrt_rpow_eq_rpow_half hy]

theorem sqrt_rpow_mul_rpow_mul_rpow
    {x y z a b c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x ^ a * y ^ b * z ^ c) =
      x ^ (a / 2) * y ^ (b / 2) * z ^ (c / 2) := by
  rw [show x ^ a * y ^ b * z ^ c = (x ^ a * y ^ b) * z ^ c by ring,
    Real.sqrt_mul (mul_nonneg (Real.rpow_nonneg hx a) (Real.rpow_nonneg hy b)),
    sqrt_rpow_mul_rpow hx hy, sqrt_rpow_eq_rpow_half hz]

theorem gmCubicAffineTerminalScale_le_ratio
    {η T : ℝ} {N : ℕ} {p : ℕ × ℕ}
    (hT : 1 ≤ T) (hη : 0 ≤ η) (hN : 0 < N) (hNT : (N : ℝ) ≤ T)
    (hp : p ∈ gmCubicDyadicIndexPairs (gmCubicFrequencyRadius η T N)) :
    (gmCubicAffineTerminalScale p.2 : ℝ) ≤
      256 * T ^ (1 + η) / (N : ℝ) := by
  have hM := twoPow_second_dyadicIndex_le_two_ratio hT hη hN hNT hp
  unfold gmCubicAffineTerminalScale
  push_cast
  calc
    (128 : ℝ) * (2 : ℝ) ^ p.2 ≤
        128 * (2 * T ^ (1 + η) / (N : ℝ)) := by
      norm_num at hM ⊢
      exact hM
    _ = 256 * T ^ (1 + η) / (N : ℝ) := by ring

theorem gmCubicSelectedScale_first_le
    {η T : ℝ} {N : ℕ} {p : ℕ × ℕ}
    (hT : 1 ≤ T) (hη : 0 ≤ η) (hN : 0 < N) (hNT : (N : ℝ) ≤ T)
    (hp : p ∈ gmCubicDyadicIndexPairs (gmCubicFrequencyRadius η T N)) :
    (N : ℝ) ^ 2 / ((2 ^ p.2 : ℕ) : ℝ) *
        (gmCubicAffineTerminalScale p.2 : ℝ) ^ 3 ≤
      4 * 128 ^ 3 * T ^ (2 * (1 + η)) := by
  have hM := twoPow_second_dyadicIndex_le_two_ratio hT hη hN hNT hp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < ((2 ^ p.2 : ℕ) : ℝ) := by positivity
  have hNM : (N : ℝ) * ((2 ^ p.2 : ℕ) : ℝ) ≤ 2 * T ^ (1 + η) := by
    rw [le_div_iff₀ hNpos] at hM
    nlinarith
  have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (N : ℝ) * ((2 ^ p.2 : ℕ) : ℝ)) hNM
  calc
    (N : ℝ) ^ 2 / ((2 ^ p.2 : ℕ) : ℝ) *
          (gmCubicAffineTerminalScale p.2 : ℝ) ^ 3 =
        128 ^ 3 * ((N : ℝ) * ((2 ^ p.2 : ℕ) : ℝ)) ^ 2 := by
      unfold gmCubicAffineTerminalScale
      push_cast
      field_simp [hMpos.ne']
    _ ≤ 128 ^ 3 * (2 * T ^ (1 + η)) ^ 2 := by gcongr
    _ = 4 * 128 ^ 3 * T ^ (2 * (1 + η)) := by
      have hpow : (T ^ (1 + η)) ^ 2 = T ^ (2 * (1 + η)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ T)]
        congr 1
        ring
      rw [show (2 * T ^ (1 + η)) ^ 2 = 4 * (T ^ (1 + η)) ^ 2 by ring]
      rw [hpow]
      ring

theorem gmCubicSelectedScale_second_le
    {η T : ℝ} {N : ℕ} {p : ℕ × ℕ}
    (hT : 1 ≤ T) (hη : 0 ≤ η) (hN : 0 < N) (hNT : (N : ℝ) ≤ T)
    (hp : p ∈ gmCubicDyadicIndexPairs (gmCubicFrequencyRadius η T N)) :
    (N : ℝ) ^ 2 / ((2 ^ p.2 : ℕ) : ℝ) *
        (gmCubicAffineTerminalScale p.2 : ℝ) ^ 2 ≤
      2 * 128 ^ 2 * T ^ (1 + η) * (N : ℝ) := by
  have hM := twoPow_second_dyadicIndex_le_two_ratio hT hη hN hNT hp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < ((2 ^ p.2 : ℕ) : ℝ) := by positivity
  have hNM : (N : ℝ) * ((2 ^ p.2 : ℕ) : ℝ) ≤ 2 * T ^ (1 + η) := by
    rw [le_div_iff₀ hNpos] at hM
    nlinarith
  calc
    (N : ℝ) ^ 2 / ((2 ^ p.2 : ℕ) : ℝ) *
          (gmCubicAffineTerminalScale p.2 : ℝ) ^ 2 =
        128 ^ 2 * ((N : ℝ) * ((2 ^ p.2 : ℕ) : ℝ)) * (N : ℝ) := by
      unfold gmCubicAffineTerminalScale
      push_cast
      field_simp [hMpos.ne']
    _ ≤ 128 ^ 2 * (2 * T ^ (1 + η)) * (N : ℝ) := by gcongr
    _ = 2 * 128 ^ 2 * T ^ (1 + η) * (N : ℝ) := by ring

set_option maxHeartbeats 1000000 in
/-- Proposition 10.1 with the selected dyadic and affine scales eliminated.
The two displayed summands are exactly the two terms of the source estimate;
only the two logarithmic pigeonhole factors and the explicit Poisson tails
remain to be absorbed into an epsilon power. -/
theorem gmCubicS3_prop10_1_physical_explicit
    (cutoff : GMSmoothCutoff) (μ η : ℝ)
    (hμ : 0 < μ) (hηpos : 0 < η) (hη : η ≤ 1 / 6) :
    ∃ C K T₀ : ℝ, 0 < C ∧ 0 < K ∧ 4096 ≤ T₀ ∧
      ∀ {T : ℝ} {N : ℕ} {W : Finset ℝ},
      T₀ ≤ T → 0 < N → (N : ℝ) ≤ T →
      T ^ (2 / 3 : ℝ) ≤ (N : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      ‖gmCubicS3 cutoff N W‖ ≤
        C * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (T ^ (2 + 3 * η + 3 * μ) * Real.sqrt (W.card : ℝ) * (W.card : ℝ) +
            T ^ (1 + 2 * η + 3 * μ) * (N : ℝ) *
              Real.sqrt (W.card : ℝ) *
              Real.sqrt (ApproxAddEnergy 1 W : ℝ)) +
        C * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          T ^ 5 / T ^ 200 + K / T ^ 100 := by
  obtain ⟨K, C₇, C₉, T₀, hK, hC₇, hC₉, hT₀, hselected⟩ :=
    gmCubicS3_prop10_1_selected_explicit cutoff μ η hμ hηpos hη
  let C₂ := gmCubicL2Constant μ
  let Cw := gmCubicWideL2Constant μ
  let C₄ := gmCubicWideFourthConstant μ
  let A := 48 * C₇ * (C₂ + 1) * (C₉ + 1) * Cw * 128 ^ 3
  let B := 12 * C₇ * (C₂ + 1) * (C₉ + 1) * (6 * C₄ + 1) * 128 ^ 2
  let C := 6 * A + 6 * B + 750 * C₇
  have hC₂ : 0 < C₂ := by exact gmCubicL2Constant_pos hμ
  have hCw : 0 < Cw := by exact gmCubicWideL2Constant_pos hμ
  have hC₄ : 0 < C₄ := by exact gmCubicWideFourthConstant_pos hμ
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, K, T₀, hC, hK, hT₀, ?_⟩
  intro T N W hT hN hNT hNlower hSep hBase
  obtain ⟨p, hp, hraw⟩ := hselected hT hN hNT hNlower hSep hBase
  have hTone : (1 : ℝ) ≤ T := (by norm_num : (1 : ℝ) ≤ 4096).trans (hT₀.trans hT)
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hη0 : 0 ≤ η := hηpos.le
  have hn0 : 0 ≤ (N : ℝ) := by positivity
  have hw0 : 0 ≤ (W.card : ℝ) := by positivity
  have hE0 : 0 ≤ (ApproxAddEnergy 1 W : ℝ) := by positivity
  let m : ℝ := ((2 ^ p.2 : ℕ) : ℝ)
  let q : ℝ := gmCubicAffineTerminalScale p.2
  let x : ℝ := 2 * Cw * T ^ μ * (W.card : ℝ)
  let y : ℝ := 6 * C₄ * T ^ μ * (ApproxAddEnergy 1 W : ℝ)
  have hmpos : 0 < m := by dsimp only [m]; positivity
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hs₂ := sqrt_const_mul_rpow_le hC₂ hTone hμ
  have hs₉ := sqrt_const_mul_rpow_le hC₉ hTone hμ
  have hs₄ := sqrt_const_mul_rpow_le (by dsimp only [C₄]; positivity : 0 < 6 * C₄) hTone hμ
  have hsL :
      Real.sqrt (C₂ * T ^ μ * (W.card : ℝ)) ≤
        (C₂ + 1) * T ^ μ * Real.sqrt (W.card : ℝ) := by
    rw [show C₂ * T ^ μ * (W.card : ℝ) = (C₂ * T ^ μ) * (W.card : ℝ) by ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ C₂ * T ^ μ)]
    gcongr
  have hsy : Real.sqrt y ≤
      (6 * C₄ + 1) * T ^ μ * Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
    dsimp only [y]
    rw [show 6 * C₄ * T ^ μ * (ApproxAddEnergy 1 W : ℝ) =
        (6 * C₄ * T ^ μ) * (ApproxAddEnergy 1 W : ℝ) by ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ 6 * C₄ * T ^ μ)]
    gcongr
  have hsInner :
      Real.sqrt (q ^ 6 * x ^ 2 + q ^ 4 * y) ≤
        q ^ 3 * x + q ^ 2 *
          ((6 * C₄ + 1) * T ^ μ * Real.sqrt (ApproxAddEnergy 1 W : ℝ)) := by
    calc
      Real.sqrt (q ^ 6 * x ^ 2 + q ^ 4 * y) ≤
          Real.sqrt (q ^ 6 * x ^ 2) + Real.sqrt (q ^ 4 * y) :=
        sqrt_add_le_add_sqrt (by positivity) (by positivity)
      _ = q ^ 3 * x + q ^ 2 * Real.sqrt y := by
        rw [sqrt_pow_six_mul_sq hq0 hx0, sqrt_pow_four_mul hq0]
      _ ≤ _ := by gcongr
  have hsJ :
      Real.sqrt (C₉ * T ^ μ * (q ^ 6 * x ^ 2 + q ^ 4 * y)) ≤
        (C₉ + 1) * T ^ μ *
          (q ^ 3 * x + q ^ 2 *
            ((6 * C₄ + 1) * T ^ μ *
              Real.sqrt (ApproxAddEnergy 1 W : ℝ))) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ C₉ * T ^ μ)]
    exact mul_le_mul hs₉ hsInner (Real.sqrt_nonneg _)
      (mul_nonneg (by positivity) (by positivity))
  have hscale₁ := gmCubicSelectedScale_first_le hTone hη0 hN hNT hp
  have hscale₂ := gmCubicSelectedScale_second_le hTone hη0 hN hNT hp
  have hTprod : T ^ η * T ^ μ * T ^ μ * T ^ μ = T ^ (η + 3 * μ) := by
    rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
    congr 1
    ring
  have hmain :
      C₇ * T ^ η * (N : ℝ) ^ 2 / m *
          (6 * Real.sqrt (C₂ * T ^ μ * (W.card : ℝ)) *
            Real.sqrt (C₉ * T ^ μ * (q ^ 6 * x ^ 2 + q ^ 4 * y))) ≤
        A * T ^ (2 + 3 * η + 3 * μ) * Real.sqrt (W.card : ℝ) * (W.card : ℝ) +
          B * T ^ (1 + 2 * η + 3 * μ) * (N : ℝ) *
            Real.sqrt (W.card : ℝ) *
            Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
    calc
      _ ≤ C₇ * T ^ η * (N : ℝ) ^ 2 / m *
          (6 * ((C₂ + 1) * T ^ μ * Real.sqrt (W.card : ℝ)) *
            ((C₉ + 1) * T ^ μ *
              (q ^ 3 * x + q ^ 2 * ((6 * C₄ + 1) * T ^ μ *
                Real.sqrt (ApproxAddEnergy 1 W : ℝ))))) := by gcongr
      _ = 6 * C₇ * (C₂ + 1) * (C₉ + 1) *
            (T ^ η * T ^ μ * T ^ μ) *
            ((N : ℝ) ^ 2 / m * q ^ 3) *
            Real.sqrt (W.card : ℝ) * x +
          6 * C₇ * (C₂ + 1) * (C₉ + 1) * (6 * C₄ + 1) *
            (T ^ η * T ^ μ * T ^ μ * T ^ μ) *
            ((N : ℝ) ^ 2 / m * q ^ 2) *
            Real.sqrt (W.card : ℝ) * Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by ring
      _ = 12 * C₇ * (C₂ + 1) * (C₉ + 1) * Cw *
            (T ^ η * T ^ μ * T ^ μ * T ^ μ) *
            ((N : ℝ) ^ 2 / m * q ^ 3) *
            Real.sqrt (W.card : ℝ) * (W.card : ℝ) +
          6 * C₇ * (C₂ + 1) * (C₉ + 1) * (6 * C₄ + 1) *
            (T ^ η * T ^ μ * T ^ μ * T ^ μ) *
            ((N : ℝ) ^ 2 / m * q ^ 2) *
            Real.sqrt (W.card : ℝ) * Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
        dsimp only [x]
        ring
      _ ≤ 12 * C₇ * (C₂ + 1) * (C₉ + 1) * Cw *
            T ^ (η + 3 * μ) * (4 * 128 ^ 3 * T ^ (2 * (1 + η))) *
            Real.sqrt (W.card : ℝ) * (W.card : ℝ) +
          6 * C₇ * (C₂ + 1) * (C₉ + 1) * (6 * C₄ + 1) *
            T ^ (η + 3 * μ) *
            (2 * 128 ^ 2 * T ^ (1 + η) * (N : ℝ)) *
            Real.sqrt (W.card : ℝ) * Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
        rw [hTprod]
        gcongr
      _ = _ := by
        dsimp only [A, B]
        have hp₁ : T ^ (η + 3 * μ) * T ^ (2 * (1 + η)) =
            T ^ (2 + 3 * η + 3 * μ) := by
          rw [← Real.rpow_add hTpos]
          congr 1
          ring
        have hp₂ : T ^ (η + 3 * μ) * T ^ (1 + η) =
            T ^ (1 + 2 * η + 3 * μ) := by
          rw [← Real.rpow_add hTpos]
          congr 1
          ring
        rw [← hp₁, ← hp₂]
        ring
  have hcard := card_gmCubicDyadicFrequencyBlock_sourceRadius_le
    (T := T) (N := N) (r := p.1) (s := p.2) hTone hη0
      (hη.trans (by norm_num)) hN
  have htail :
      ((gmCubicDyadicFrequencyBlock
          (gmCubicFrequencyRadius η T N) p.1 p.2).card : ℝ) * (C₇ / T ^ 200) ≤
        125 * C₇ * T ^ 5 / T ^ 200 := by
    calc
      _ ≤ (125 * T ^ 5) * (C₇ / T ^ 200) := by gcongr
      _ = _ := by ring
  have hlog0 : 0 ≤
      (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 := by positivity
  have hraw' :
      ‖gmCubicS3 cutoff N W‖ ≤
        6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (A * T ^ (2 + 3 * η + 3 * μ) * Real.sqrt (W.card : ℝ) * (W.card : ℝ) +
            B * T ^ (1 + 2 * η + 3 * μ) * (N : ℝ) *
              Real.sqrt (W.card : ℝ) * Real.sqrt (ApproxAddEnergy 1 W : ℝ) +
            125 * C₇ * T ^ 5 / T ^ 200) + K / T ^ 100 := by
    calc
      _ ≤ 6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (C₇ * T ^ η * (N : ℝ) ^ 2 / m *
              (6 * Real.sqrt (C₂ * T ^ μ * (W.card : ℝ)) *
                Real.sqrt (C₉ * T ^ μ * (q ^ 6 * x ^ 2 + q ^ 4 * y))) +
            ((gmCubicDyadicFrequencyBlock
              (gmCubicFrequencyRadius η T N) p.1 p.2).card : ℝ) *
                (C₇ / T ^ 200)) + K / T ^ 100 := by
        simpa only [C₂, Cw, C₄, m, q, x, y] using hraw
      _ ≤ _ := by gcongr
  calc
    ‖gmCubicS3 cutoff N W‖ ≤ _ := hraw'
    _ ≤ C * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (T ^ (2 + 3 * η + 3 * μ) * Real.sqrt (W.card : ℝ) * (W.card : ℝ) +
            T ^ (1 + 2 * η + 3 * μ) * (N : ℝ) *
              Real.sqrt (W.card : ℝ) * Real.sqrt (ApproxAddEnergy 1 W : ℝ)) +
        C * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          T ^ 5 / T ^ 200 + K / T ^ 100 := by
      have hA0 : 0 ≤ A := hA.le
      have hB0 : 0 ≤ B := hB.le
      let P := T ^ (2 + 3 * η + 3 * μ) * Real.sqrt (W.card : ℝ) * (W.card : ℝ)
      let Q := T ^ (1 + 2 * η + 3 * μ) * (N : ℝ) *
        Real.sqrt (W.card : ℝ) * Real.sqrt (ApproxAddEnergy 1 W : ℝ)
      let R := T ^ 5 / T ^ 200
      have hP0 : 0 ≤ P := by dsimp only [P]; positivity
      have hQ0 : 0 ≤ Q := by dsimp only [Q]; positivity
      have hR0 : 0 ≤ R := by dsimp only [R]; positivity
      have hinside :
          6 * (A * P + B * Q + 125 * C₇ * R) ≤ C * (P + Q + R) := by
        dsimp only [C]
        nlinarith [mul_nonneg hA0 hQ0, mul_nonneg hA0 hR0,
          mul_nonneg hB0 hP0, mul_nonneg hB0 hR0,
          mul_nonneg hC₇.le hP0, mul_nonneg hC₇.le hQ0]
      have hgoal :
          6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
              (A * P + B * Q + 125 * C₇ * R) + K / T ^ 100 ≤
            C * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
              (P + Q) +
            C * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
              R + K / T ^ 100 := by
        calc
          6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
                (A * P + B * Q + 125 * C₇ * R) + K / T ^ 100 =
              (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
                (6 * (A * P + B * Q + 125 * C₇ * R)) + K / T ^ 100 := by ring
          _ ≤
              (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
                (C * (P + Q + R)) + K / T ^ 100 := by gcongr
          _ = _ := by ring
      dsimp only [P, Q, R] at hgoal
      convert hgoal using 1 <;> ring

set_option maxHeartbeats 1000000 in
/-- Guth--Maynard Proposition 10.1 in its final epsilon-power form. -/
theorem gmCubicS3_prop10_1_native
    (cutoff : GMSmoothCutoff) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C T₀ : ℝ, 0 < C ∧ 4096 ≤ T₀ ∧
        ∀ {T : ℝ} {N : ℕ} {W : Finset ℝ},
        T₀ ≤ T → 0 < N → (N : ℝ) ≤ T →
        T ^ (2 / 3 : ℝ) ≤ (N : ℝ) →
        IsSeparated 1 W → InBaseInterval T W →
        ‖gmCubicS3 cutoff N W‖ ≤
          C * (T ^ (2 + ε) * Real.sqrt (W.card : ℝ) * (W.card : ℝ) +
            T ^ (1 + ε) * (N : ℝ) * Real.sqrt (W.card : ℝ) *
              Real.sqrt (ApproxAddEnergy 1 W : ℝ)) + C / T ^ 90 := by
  intro ε hε
  let η : ℝ := min (ε / 24) (1 / 12)
  let μ : ℝ := ε / 24
  have hηpos : 0 < η := by
    dsimp only [η]
    exact lt_min (by positivity) (by norm_num)
  have hη : η ≤ 1 / 6 := (min_le_right _ _).trans (by norm_num)
  have hηbudget : 3 * η ≤ ε / 8 := by
    have := min_le_left (ε / 24) (1 / 12)
    dsimp only [η]
    linarith
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  obtain ⟨C₀, K, T₁, hC₀, hK, hT₁, hraw⟩ :=
    gmCubicS3_prop10_1_physical_explicit cutoff μ η hμ hηpos hη
  have hLogMainEventually := gmEventuallyLogNatPower_le_rpow 2 (ε / 2) (by positivity)
  have hLogTailEventually := gmEventuallyLogNatPower_le_rpow 2 1 (by norm_num)
  rw [Filter.eventually_atTop] at hLogMainEventually hLogTailEventually
  obtain ⟨Tmain, hTmain⟩ := hLogMainEventually
  obtain ⟨Ttail, hTtail⟩ := hLogTailEventually
  let T₀ := max T₁ (max (Real.exp 1) (max Tmain Ttail))
  let C := 36 * C₀ + 36 * C₀ + K
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, T₀, hC, hT₁.trans (le_max_left _ _), ?_⟩
  intro T N W hT hN hNT hNlower hSep hBase
  have hT₁' : T₁ ≤ T := (le_max_left T₁ _).trans hT
  have hExp : Real.exp 1 ≤ T := (le_max_left (Real.exp 1) _).trans
    ((le_max_right T₁ _).trans hT)
  have hTm : Tmain ≤ T := (le_max_left Tmain Ttail).trans
    ((le_max_right (Real.exp 1) _).trans ((le_max_right T₁ _).trans hT))
  have hTt : Ttail ≤ T := (le_max_right Tmain Ttail).trans
    ((le_max_right (Real.exp 1) _).trans ((le_max_right T₁ _).trans hT))
  have hTone : (1 : ℝ) ≤ T := (by norm_num : (1 : ℝ) ≤ Real.exp 1).trans hExp
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hlogNat := gmCubicDyadicLogFactor_sq_le_realLog_sq
    (η := η) (T := T) (N := N) hExp hηpos.le (hη.trans (by norm_num)) hN hNT
  have hlogMain := hTmain T hTm
  have hlogTail := hTtail T hTt
  have hLmain :
      (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 ≤
        36 * T ^ (ε / 2) := hlogNat.trans (by gcongr)
  have hLtail :
      (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 ≤
        36 * T := by
    calc
      _ ≤ 36 * (Real.log T) ^ 2 := hlogNat
      _ ≤ 36 * T ^ (1 : ℝ) := by gcongr
      _ = 36 * T := by rw [Real.rpow_one]
  have hloss₁ : ε / 2 + (2 + 3 * η + 3 * μ) ≤ 2 + ε := by
    dsimp only [μ]
    linarith
  have hloss₂ : ε / 2 + (1 + 2 * η + 3 * μ) ≤ 1 + ε := by
    have hηtwo : 2 * η ≤ ε / 12 := by linarith
    dsimp only [μ]
    linarith
  have hp₁ : T ^ (ε / 2) * T ^ (2 + 3 * η + 3 * μ) ≤ T ^ (2 + ε) := by
    rw [← Real.rpow_add hTpos]
    exact Real.rpow_le_rpow_of_exponent_le hTone hloss₁
  have hp₂ : T ^ (ε / 2) * T ^ (1 + 2 * η + 3 * μ) ≤ T ^ (1 + ε) := by
    rw [← Real.rpow_add hTpos]
    exact Real.rpow_le_rpow_of_exponent_le hTone hloss₂
  have htailPow : T ^ 6 / T ^ 200 ≤ 1 / T ^ 90 := by
    rw [div_le_div_iff₀ (pow_pos hTpos 200) (pow_pos hTpos 90)]
    calc
      T ^ 6 * T ^ 90 = T ^ 96 := by rw [← pow_add]
      _ ≤ T ^ 200 := pow_le_pow_right₀ hTone (by omega)
      _ = 1 * T ^ 200 := by ring
  have htail100 : 1 / T ^ 100 ≤ 1 / T ^ 90 := by
    rw [one_div, one_div]
    exact inv_anti₀ (pow_pos hTpos 90)
      (pow_le_pow_right₀ hTone (by omega : 90 ≤ 100))
  have hsource := hraw hT₁' hN hNT hNlower hSep hBase
  let P := Real.sqrt (W.card : ℝ) * (W.card : ℝ)
  let Q := (N : ℝ) * Real.sqrt (W.card : ℝ) *
    Real.sqrt (ApproxAddEnergy 1 W : ℝ)
  have hP0 : 0 ≤ P := by dsimp only [P]; positivity
  have hQ0 : 0 ≤ Q := by dsimp only [Q]; positivity
  have hmain₁ :
      C₀ * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (T ^ (2 + 3 * η + 3 * μ) * P) ≤
        36 * C₀ * T ^ (2 + ε) * P := by
    calc
      _ ≤ C₀ * (36 * T ^ (ε / 2)) *
          (T ^ (2 + 3 * η + 3 * μ) * P) := by gcongr
      _ = 36 * C₀ *
          (T ^ (ε / 2) * T ^ (2 + 3 * η + 3 * μ)) * P := by ring
      _ ≤ _ := by gcongr
  have hmain₂ :
      C₀ * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (T ^ (1 + 2 * η + 3 * μ) * Q) ≤
        36 * C₀ * T ^ (1 + ε) * Q := by
    calc
      _ ≤ C₀ * (36 * T ^ (ε / 2)) *
          (T ^ (1 + 2 * η + 3 * μ) * Q) := by gcongr
      _ = 36 * C₀ *
          (T ^ (ε / 2) * T ^ (1 + 2 * η + 3 * μ)) * Q := by ring
      _ ≤ _ := by gcongr
  have htail :
      C₀ * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          T ^ 5 / T ^ 200 + K / T ^ 100 ≤
        (36 * C₀ + K) / T ^ 90 := by
    have hfirst :
        C₀ * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
            T ^ 5 / T ^ 200 ≤ 36 * C₀ / T ^ 90 := by
      calc
        _ ≤ C₀ * (36 * T) * T ^ 5 / T ^ 200 := by gcongr
        _ = 36 * C₀ * (T ^ 6 / T ^ 200) := by ring
        _ ≤ 36 * C₀ * (1 / T ^ 90) := by gcongr
        _ = 36 * C₀ / T ^ 90 := by ring
    have hKtail : K / T ^ 100 ≤ K * (1 / T ^ 90) := by
      calc
        K / T ^ 100 = K * (1 / T ^ 100) := by ring
        _ ≤ K * (1 / T ^ 90) := mul_le_mul_of_nonneg_left htail100 hK.le
    calc
      _ ≤ 36 * C₀ / T ^ 90 + K * (1 / T ^ 90) := by
        exact add_le_add hfirst hKtail
      _ = (36 * C₀ + K) / T ^ 90 := by ring
  calc
    ‖gmCubicS3 cutoff N W‖ ≤
        C₀ * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (T ^ (2 + 3 * η + 3 * μ) * P +
            T ^ (1 + 2 * η + 3 * μ) * Q) +
        C₀ * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          T ^ 5 / T ^ 200 + K / T ^ 100 := by
      simpa only [P, Q, mul_assoc] using hsource
    _ = C₀ * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (T ^ (2 + 3 * η + 3 * μ) * P) +
        C₀ * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (T ^ (1 + 2 * η + 3 * μ) * Q) +
        (C₀ * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          T ^ 5 / T ^ 200 + K / T ^ 100) := by ring
    _ ≤ 36 * C₀ * T ^ (2 + ε) * P +
        36 * C₀ * T ^ (1 + ε) * Q + (36 * C₀ + K) / T ^ 90 :=
      add_le_add (add_le_add hmain₁ hmain₂) htail
    _ ≤ C * (T ^ (2 + ε) * P + T ^ (1 + ε) * Q) + C / T ^ 90 := by
      have hcoef : 36 * C₀ ≤ C := by dsimp only [C]; linarith [hC₀.le, hK.le]
      have hcoefTail : 36 * C₀ + K ≤ C := by
        dsimp only [C]
        linarith [hC₀.le]
      calc
        36 * C₀ * T ^ (2 + ε) * P +
              36 * C₀ * T ^ (1 + ε) * Q + (36 * C₀ + K) / T ^ 90 ≤
            C * T ^ (2 + ε) * P + C * T ^ (1 + ε) * Q + C / T ^ 90 := by
          gcongr
        _ = _ := by ring
    _ = _ := by dsimp only [P, Q]; ring

set_option maxHeartbeats 1500000 in
/-- Guth--Maynard Proposition 11.2.  This substitutes the native Proposition
11.1 energy estimate into the native Proposition 10.1 bound and simplifies
each of the three square-root branches at the source exponents. -/
theorem gmCubicS3_prop11_2_native
    (cutoff : GMSmoothCutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 4096 ≤ T₀ ∧
      ∀ (N : ℕ) (T σ : ℝ) (W : Finset ℝ) (b : ℕ → ℂ),
      0 < N → T₀ ≤ T → (N : ℝ) ≤ T →
      T ^ (3 / 4 : ℝ) ≤ (N : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      (∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖sourceDirichletPoly N b t‖) →
      ‖gmCubicS3 cutoff N W‖ ≤
        C * T ^ ε *
          (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
            T * (W.card : ℝ) * (N : ℝ) ^ (3 - 2 * σ) +
            T * (W.card : ℝ) ^ 2 * (N : ℝ) ^ (3 / 2 - σ) +
            T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) *
              (N : ℝ) ^ (3 / 2 - σ)) + C / T ^ 90 := by
  let μ := ε / 8
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  obtain ⟨C₁, T₁, hC₁, hT₁, hprop10⟩ := gmCubicS3_prop10_1_native cutoff μ hμ
  obtain ⟨C₂, T₂, hC₂, hT₂, henergy⟩ := gmEnergy_prop11_1_native μ hμ
  let D := C₂ + 1
  let C := C₁ * (D + 1) + C₁
  let T₀ := max T₁ T₂
  have hD : 0 < D := by dsimp only [D]; linarith
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, T₀, hC, ?_, ?_⟩
  · exact hT₁.trans (le_max_left _ _)
  intro N T σ W b hN hT hNT hNscale hSep hBase hb hLarge
  have hT₁' : T₁ ≤ T := (le_max_left T₁ T₂).trans hT
  have hT₂' : T₂ ≤ T := (le_max_right T₁ T₂).trans hT
  have hTone : (1 : ℝ) ≤ T := (by norm_num : (1 : ℝ) ≤ 4096).trans (hT₁.trans hT₁')
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hnpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) ≤ N := hnpos.le
  by_cases hWempty : W = ∅
  · subst W
    simp [gmCubicS3]
    positivity
  have hWcard : 0 < W.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hWempty)
  have hwpos : (0 : ℝ) < W.card := by exact_mod_cast hWcard
  have hw0 : (0 : ℝ) ≤ W.card := hwpos.le
  let w : ℝ := W.card
  let n : ℝ := N
  let E : ℝ := ApproxAddEnergy 1 W
  let X₁ := w * n ^ (4 - 4 * σ)
  let X₂ := w ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * n ^ (1 - 2 * σ)
  let X₃ := w ^ 3 * n ^ (1 - 2 * σ)
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hX₁0 : 0 ≤ X₁ := by dsimp only [X₁, w, n]; positivity
  have hX₂0 : 0 ≤ X₂ := by dsimp only [X₂, w, n]; positivity
  have hX₃0 : 0 ≤ X₃ := by dsimp only [X₃, w, n]; positivity
  have he := henergy N T σ W b hN hT₂' hNT hNscale hSep hBase hb hLarge
  have hsC₂ := sqrt_const_mul_rpow_le hC₂ hTone hμ
  have hsSum : Real.sqrt (X₁ + X₂ + X₃) ≤
      Real.sqrt X₁ + Real.sqrt X₂ + Real.sqrt X₃ := by
    calc
      Real.sqrt (X₁ + X₂ + X₃) = Real.sqrt ((X₁ + X₂) + X₃) := by ring_nf
      _ ≤ Real.sqrt (X₁ + X₂) + Real.sqrt X₃ :=
        sqrt_add_le_add_sqrt (add_nonneg hX₁0 hX₂0) hX₃0
      _ ≤ (Real.sqrt X₁ + Real.sqrt X₂) + Real.sqrt X₃ := by
        gcongr
        exact sqrt_add_le_add_sqrt hX₁0 hX₂0
      _ = _ := by ring
  have hsE : Real.sqrt E ≤ D * T ^ μ *
      (Real.sqrt X₁ + Real.sqrt X₂ + Real.sqrt X₃) := by
    have hs := Real.sqrt_le_sqrt he
    calc
      Real.sqrt E ≤ Real.sqrt (C₂ * T ^ μ * (X₁ + X₂ + X₃)) := by
        simpa only [E, X₁, X₂, X₃, w, n] using hs
      _ = Real.sqrt (C₂ * T ^ μ) * Real.sqrt (X₁ + X₂ + X₃) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ C₂ * T ^ μ)]
      _ ≤ D * T ^ μ * (Real.sqrt X₁ + Real.sqrt X₂ + Real.sqrt X₃) := by
        dsimp only [D]
        exact mul_le_mul hsC₂ hsSum (Real.sqrt_nonneg _)
          (mul_nonneg (by positivity) (by positivity))
  have hroot₁ : n * Real.sqrt w * Real.sqrt X₁ =
      w * n ^ (3 - 2 * σ) := by
    have hr : Real.sqrt X₁ = w ^ (1 / 2 : ℝ) * n ^ (2 - 2 * σ) := by
      dsimp only [X₁]
      rw [show w = w ^ (1 : ℝ) by rw [Real.rpow_one],
        sqrt_rpow_mul_rpow hw0 hn0]
      simp only [Real.rpow_one]
      dsimp only [n]
      rw [show (4 - 4 * σ) / 2 = 2 - 2 * σ by ring]
    calc
      n * Real.sqrt w * Real.sqrt X₁ =
          n ^ (1 : ℝ) * w ^ (1 / 2 : ℝ) *
            (w ^ (1 / 2 : ℝ) * n ^ (2 - 2 * σ)) := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow, hr]
      _ = (w ^ (1 / 2 : ℝ) * w ^ (1 / 2 : ℝ)) *
          (n ^ (1 : ℝ) * n ^ (2 - 2 * σ)) := by ring
      _ = w ^ ((1 / 2 : ℝ) + 1 / 2) * n ^ ((1 : ℝ) + (2 - 2 * σ)) := by
        rw [← Real.rpow_add hwpos, ← Real.rpow_add hnpos]
      _ = w * n ^ (3 - 2 * σ) := by
        rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
        congr 1
        ring_nf
  have hroot₂ : n * Real.sqrt w * Real.sqrt X₂ =
      T ^ (1 / 8 : ℝ) * w ^ (29 / 16 : ℝ) * n ^ (3 / 2 - σ) := by
    have hr : Real.sqrt X₂ = w ^ (21 / 16 : ℝ) * T ^ (1 / 8 : ℝ) *
        n ^ (1 / 2 - σ) := by
      dsimp only [X₂]
      rw [sqrt_rpow_mul_rpow_mul_rpow hw0 hTpos.le hn0]
      rw [show (21 / 8 : ℝ) / 2 = 21 / 16 by norm_num,
        show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num,
        show (1 - 2 * σ) / 2 = 1 / 2 - σ by ring]
    calc
      n * Real.sqrt w * Real.sqrt X₂ =
          n ^ (1 : ℝ) * w ^ (1 / 2 : ℝ) *
            (w ^ (21 / 16 : ℝ) * T ^ (1 / 8 : ℝ) * n ^ (1 / 2 - σ)) := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow, hr]
      _ = T ^ (1 / 8 : ℝ) *
          (w ^ (1 / 2 : ℝ) * w ^ (21 / 16 : ℝ)) *
          (n ^ (1 : ℝ) * n ^ (1 / 2 - σ)) := by ring
      _ = T ^ (1 / 8 : ℝ) * w ^ ((1 / 2 : ℝ) + 21 / 16) *
          n ^ ((1 : ℝ) + (1 / 2 - σ)) := by
        rw [← Real.rpow_add hwpos, ← Real.rpow_add hnpos]
      _ = _ := by congr 2 <;> ring_nf
  have hroot₃ : n * Real.sqrt w * Real.sqrt X₃ =
      w ^ 2 * n ^ (3 / 2 - σ) := by
    have hr : Real.sqrt X₃ = w ^ (3 / 2 : ℝ) * n ^ (1 / 2 - σ) := by
      dsimp only [X₃]
      rw [show w ^ (3 : ℕ) = w ^ (3 : ℝ) by norm_num [Real.rpow_natCast]]
      rw [sqrt_rpow_mul_rpow hw0 hn0]
      rw [show (3 : ℝ) / 2 = 3 / 2 by rfl,
        show (1 - 2 * σ) / 2 = 1 / 2 - σ by ring]
    calc
      n * Real.sqrt w * Real.sqrt X₃ =
          n ^ (1 : ℝ) * w ^ (1 / 2 : ℝ) *
            (w ^ (3 / 2 : ℝ) * n ^ (1 / 2 - σ)) := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow, hr]
      _ = (w ^ (1 / 2 : ℝ) * w ^ (3 / 2 : ℝ)) *
          (n ^ (1 : ℝ) * n ^ (1 / 2 - σ)) := by ring
      _ = w ^ ((1 / 2 : ℝ) + 3 / 2) * n ^ ((1 : ℝ) + (1 / 2 - σ)) := by
        rw [← Real.rpow_add hwpos, ← Real.rpow_add hnpos]
      _ = _ := by
        rw [show (1 / 2 : ℝ) + 3 / 2 = 2 by norm_num,
          show (1 : ℝ) + (1 / 2 - σ) = 3 / 2 - σ by ring]
        norm_num [Real.rpow_natCast]
  have htw : Real.sqrt w * w = w ^ (3 / 2 : ℝ) := by
    calc
      Real.sqrt w * w = w ^ (1 / 2 : ℝ) * w ^ (1 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_one]
      _ = w ^ ((1 / 2 : ℝ) + 1) := (Real.rpow_add hwpos _ _).symm
      _ = _ := by norm_num
  have hNlower : T ^ (2 / 3 : ℝ) ≤ (N : ℝ) := by
    calc
      T ^ (2 / 3 : ℝ) ≤ T ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hTone (by norm_num)
      _ ≤ (N : ℝ) := hNscale
  have hs := hprop10 hT₁' hN hNT hNlower hSep hBase
  have hμeps : μ ≤ ε := by dsimp only [μ]; linarith
  have hTμ : T ^ μ ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hTone hμeps
  have hpowμ : T ^ μ * T ^ 2 ≤ T ^ ε * T ^ 2 :=
    mul_le_mul_of_nonneg_right hTμ (by positivity)
  have hpow2μ : T ^ μ * T ^ μ ≤ T ^ ε := by
    rw [← Real.rpow_add hTpos]
    exact Real.rpow_le_rpow_of_exponent_le hTone (by dsimp only [μ]; linarith)
  have hmainEnergy :
      C₁ * T ^ (1 + μ) * n * Real.sqrt w * Real.sqrt E ≤
        C₁ * D * T ^ ε *
          (T * w * n ^ (3 - 2 * σ) +
            T * w ^ 2 * n ^ (3 / 2 - σ) +
            T ^ (9 / 8 : ℝ) * w ^ (29 / 16 : ℝ) * n ^ (3 / 2 - σ)) := by
    have hsMul := mul_le_mul_of_nonneg_left hsE
      (mul_nonneg (mul_nonneg (mul_nonneg hC₁.le (Real.rpow_nonneg hTpos.le (1 + μ))) hn0)
        (Real.sqrt_nonneg w))
    calc
      C₁ * T ^ (1 + μ) * n * Real.sqrt w * Real.sqrt E ≤
          C₁ * T ^ (1 + μ) * n * Real.sqrt w *
            (D * T ^ μ * (Real.sqrt X₁ + Real.sqrt X₂ + Real.sqrt X₃)) := by
        exact hsMul
      _ = C₁ * D * (T ^ μ * T ^ μ) *
          (T * (n * Real.sqrt w * Real.sqrt X₁) +
            T * (n * Real.sqrt w * Real.sqrt X₃) +
            T * (n * Real.sqrt w * Real.sqrt X₂)) := by
        rw [show T ^ (1 + μ) = T * T ^ μ by
          calc
            T ^ (1 + μ) = T ^ (1 : ℝ) * T ^ μ := Real.rpow_add hTpos _ _
            _ = T * T ^ μ := by rw [Real.rpow_one]]
        ring
      _ = C₁ * D * (T ^ μ * T ^ μ) *
          (T * (w * n ^ (3 - 2 * σ)) +
            T * (w ^ 2 * n ^ (3 / 2 - σ)) +
            T * (T ^ (1 / 8 : ℝ) * w ^ (29 / 16 : ℝ) * n ^ (3 / 2 - σ))) := by
        rw [hroot₁, hroot₂, hroot₃]
      _ ≤ C₁ * D * T ^ ε *
          (T * w * n ^ (3 - 2 * σ) +
            T * w ^ 2 * n ^ (3 / 2 - σ) +
            T ^ (9 / 8 : ℝ) * w ^ (29 / 16 : ℝ) * n ^ (3 / 2 - σ)) := by
        have hTnine : T * T ^ (1 / 8 : ℝ) = T ^ (9 / 8 : ℝ) := by
          calc
            T * T ^ (1 / 8 : ℝ) = T ^ (1 : ℝ) * T ^ (1 / 8 : ℝ) := by rw [Real.rpow_one]
            _ = T ^ ((1 : ℝ) + 1 / 8) := (Real.rpow_add hTpos _ _).symm
            _ = _ := by norm_num
        have hinside :
            T * (w * n ^ (3 - 2 * σ)) +
                T * (w ^ 2 * n ^ (3 / 2 - σ)) +
                T * (T ^ (1 / 8 : ℝ) * w ^ (29 / 16 : ℝ) * n ^ (3 / 2 - σ)) =
              T * w * n ^ (3 - 2 * σ) +
                T * w ^ 2 * n ^ (3 / 2 - σ) +
                T ^ (9 / 8 : ℝ) * w ^ (29 / 16 : ℝ) * n ^ (3 / 2 - σ) := by
          rw [← hTnine]
          ring
        rw [hinside]
        gcongr
  calc
    ‖gmCubicS3 cutoff N W‖ ≤
        C₁ * (T ^ (2 + μ) * Real.sqrt w * w +
          T ^ (1 + μ) * n * Real.sqrt w * Real.sqrt E) + C₁ / T ^ 90 := by
      simpa only [w, n, E, mul_assoc] using hs
    _ ≤ C₁ * (T ^ μ * T ^ 2 * w ^ (3 / 2 : ℝ)) +
        C₁ * D * T ^ ε *
          (T * w * n ^ (3 - 2 * σ) +
            T * w ^ 2 * n ^ (3 / 2 - σ) +
            T ^ (9 / 8 : ℝ) * w ^ (29 / 16 : ℝ) * n ^ (3 / 2 - σ)) +
        C₁ / T ^ 90 := by
      have hTtwo : T ^ (2 + μ) = T ^ μ * T ^ 2 := by
        calc
          T ^ (2 + μ) = T ^ μ * T ^ (2 : ℝ) := by
            rw [← Real.rpow_add hTpos]
            congr 1
            ring
          _ = T ^ μ * T ^ 2 := by norm_num [Real.rpow_natCast]
      have hfirstEq :
          C₁ * (T ^ (2 + μ) * Real.sqrt w * w +
              T ^ (1 + μ) * n * Real.sqrt w * Real.sqrt E) + C₁ / T ^ 90 =
            C₁ * (T ^ μ * T ^ 2 * w ^ (3 / 2 : ℝ)) +
              C₁ * T ^ (1 + μ) * n * Real.sqrt w * Real.sqrt E +
              C₁ / T ^ 90 := by
        rw [hTtwo]
        have hfactor : T ^ μ * T ^ 2 * Real.sqrt w * w =
            T ^ μ * T ^ 2 * w ^ (3 / 2 : ℝ) := by
          calc
            T ^ μ * T ^ 2 * Real.sqrt w * w =
                (T ^ μ * T ^ 2) * (Real.sqrt w * w) := by ring
            _ = _ := by rw [htw]
        rw [hfactor]
        ring
      rw [hfirstEq]
      exact add_le_add (add_le_add le_rfl hmainEnergy) le_rfl
    _ ≤ C * T ^ ε *
          (T ^ 2 * w ^ (3 / 2 : ℝ) +
            T * w * n ^ (3 - 2 * σ) +
            T * w ^ 2 * n ^ (3 / 2 - σ) +
            T ^ (9 / 8 : ℝ) * w ^ (29 / 16 : ℝ) * n ^ (3 / 2 - σ)) +
        C / T ^ 90 := by
      have hfirst : C₁ * (T ^ μ * T ^ 2 * w ^ (3 / 2 : ℝ)) ≤
          C₁ * T ^ ε * (T ^ 2 * w ^ (3 / 2 : ℝ)) := by
        calc
          C₁ * (T ^ μ * T ^ 2 * w ^ (3 / 2 : ℝ)) ≤
              C₁ * (T ^ ε * T ^ 2 * w ^ (3 / 2 : ℝ)) := by gcongr
          _ = _ := by ring
      have hC₁C : C₁ ≤ C := by dsimp only [C]; nlinarith [hC₁.le, hD.le]
      have hC₁DC : C₁ * D ≤ C := by dsimp only [C]; nlinarith [hC₁.le]
      have htail : C₁ / T ^ 90 ≤ C / T ^ 90 := by gcongr
      have hY0 : 0 ≤
          T * w * n ^ (3 - 2 * σ) +
            T * w ^ 2 * n ^ (3 / 2 - σ) +
            T ^ (9 / 8 : ℝ) * w ^ (29 / 16 : ℝ) * n ^ (3 / 2 - σ) := by
        dsimp only [w, n]
        positivity
      calc
        _ ≤ C₁ * T ^ ε * (T ^ 2 * w ^ (3 / 2 : ℝ)) +
            C₁ * D * T ^ ε *
              (T * w * n ^ (3 - 2 * σ) +
                T * w ^ 2 * n ^ (3 / 2 - σ) +
                T ^ (9 / 8 : ℝ) * w ^ (29 / 16 : ℝ) * n ^ (3 / 2 - σ)) +
            C / T ^ 90 := add_le_add (add_le_add hfirst le_rfl) htail
        _ ≤ C * T ^ ε * (T ^ 2 * w ^ (3 / 2 : ℝ)) +
            C * T ^ ε *
              (T * w * n ^ (3 - 2 * σ) +
                T * w ^ 2 * n ^ (3 / 2 - σ) +
                T ^ (9 / 8 : ℝ) * w ^ (29 / 16 : ℝ) * n ^ (3 / 2 - σ)) +
            C / T ^ 90 := by gcongr
        _ = _ := by ring

end RiemannZeta.GuthMaynard
