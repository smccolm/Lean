import Tao2026.BadIntervalRecombination

/-!
# The final dyadic summation for Theorem 1.7

The source reduces the global count to dyadic windows.  A local window is
already bounded by the cumulative one-term count at its endpoint.  To sum
those cumulative bounds without losing a logarithm, one needs the adjacent
dyadic values of the one-term count to grow geometrically.  This file isolates
that precise analytic consequence and proves the finite summation mechanism.
-/

namespace Tao2026

open Filter Finset Asymptotics
open scoped Topology Real BigOperators

noncomputable section

/-- The exact adjacent-dyadic regular-variation statement needed by the
source's opening "by dyadic decomposition" reduction.  The detailed Ivić
asymptotic predicts this limit; it is not asserted here. -/
def TaoBadOneTermDyadicRatioConclusion : Prop :=
  Tendsto (fun r : ℕ =>
    (badOneTermCount (2 ^ r) : ℝ) /
      (badOneTermCount (2 ^ (r + 1)) : ℝ)) atTop (𝓝 (1 / 2 : ℝ))

theorem one_le_badOneTermCount {x : ℕ} (hx : 4 ≤ x) :
    1 ≤ badOneTermCount x := by
  classical
  unfold badOneTermCount countUpTo
  apply Finset.card_pos.mpr
  refine ⟨4, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hx⟩, ?_⟩⟩
  apply mem_badOneTermSet_iff_exists_prime_sq_mul_smooth.mpr
  refine ⟨2, 1, Nat.prime_two, ?_, by norm_num⟩
  simp only [IsSmooth, Nat.smoothNumbers, Set.mem_setOf_eq]
  constructor
  · norm_num
  · intro p hp
    simp at hp

@[simp]
theorem log_natCast_two_pow (r : ℕ) :
    Real.log (2 ^ r : ℕ) = (r : ℝ) * Real.log 2 := by
  rw [Nat.cast_pow, Real.log_pow]
  norm_num

theorem tendsto_taoDyadicLogSucc_div_self_one :
    Tendsto (fun r : ℕ =>
      Real.log (2 ^ (r + 1) : ℕ) / Real.log (2 ^ r : ℕ))
        atTop (𝓝 1) := by
  have hinv : Tendsto (fun r : ℕ => ((r : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun r : ℕ => (1 : ℝ) + ((r : ℝ))⁻¹)
      atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add hinv :
        Tendsto (fun r : ℕ => (1 : ℝ) + ((r : ℝ))⁻¹)
          atTop (𝓝 ((1 : ℝ) + 0)))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [log_natCast_two_pow, log_natCast_two_pow]
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  push_cast
  field_simp

theorem tendsto_taoDyadicLogRpowRatio_one (a : ℝ) :
    Tendsto (fun r : ℕ =>
      Real.log (2 ^ (r + 1) : ℕ) ^ a /
        Real.log (2 ^ r : ℕ) ^ a) atTop (𝓝 1) := by
  have hpow :=
    (Real.continuousAt_rpow_const (1 : ℝ) a (Or.inl one_ne_zero)).tendsto.comp
      tendsto_taoDyadicLogSucc_div_self_one
  have hpow' : Tendsto (fun r : ℕ =>
      (Real.log (2 ^ (r + 1) : ℕ) / Real.log (2 ^ r : ℕ)) ^ a)
        atTop (𝓝 1) := by
    simpa only [Function.comp_apply, Real.one_rpow] using hpow
  apply hpow'.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  have hnum : 0 ≤ Real.log (2 ^ (r + 1) : ℕ) := by
    apply Real.log_nonneg
    exact_mod_cast (one_le_pow₀ (by omega) : 1 ≤ (2 : ℕ) ^ (r + 1))
  have hden : 0 ≤ Real.log (2 ^ r : ℕ) := by
    apply Real.log_nonneg
    exact_mod_cast (one_le_pow₀ (by omega) : 1 ≤ (2 : ℕ) ^ r)
  rw [← Real.div_rpow hnum hden]

/-- The logarithmically weighted cumulative one-term count at dyadic scale. -/
def taoDyadicBadOneTermLogWeight (ε : ℝ) (r : ℕ) : ℝ :=
  (badOneTermCount (2 ^ r) : ℝ) /
    Real.log (2 ^ r : ℕ) ^ (1 - ε)

theorem taoDyadicBadOneTermLogWeight_nonneg (ε : ℝ) (r : ℕ) :
    0 ≤ taoDyadicBadOneTermLogWeight ε r := by
  exact div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Real.log_nonneg
    (by exact_mod_cast (one_le_pow₀ (by omega) : 1 ≤ (2 : ℕ) ^ r))) _)

theorem taoDyadicBadOneTermLogWeight_pos (ε : ℝ) {r : ℕ} (hr : 2 ≤ r) :
    0 < taoDyadicBadOneTermLogWeight ε r := by
  apply div_pos
  · exact_mod_cast one_le_badOneTermCount
      (show 4 ≤ (2 : ℕ) ^ r by
        calc
          4 = (2 : ℕ) ^ 2 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hr)
  · apply Real.rpow_pos_of_pos
    apply Real.log_pos
    exact_mod_cast (show 1 < (2 : ℕ) ^ r by
      exact one_lt_pow₀ (by omega) (by omega))

/-- Adjacent dyadic regular variation is unchanged by the logarithmic weight. -/
theorem tendsto_taoDyadicBadOneTermLogWeight_ratio
    (hratio : TaoBadOneTermDyadicRatioConclusion) (ε : ℝ) :
    Tendsto (fun r : ℕ =>
      taoDyadicBadOneTermLogWeight ε r /
        taoDyadicBadOneTermLogWeight ε (r + 1)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hmul := hratio.mul (tendsto_taoDyadicLogRpowRatio_one (1 - ε))
  have hmul' : Tendsto (fun r : ℕ =>
      ((badOneTermCount (2 ^ r) : ℝ) /
        (badOneTermCount (2 ^ (r + 1)) : ℝ)) *
          (Real.log (2 ^ (r + 1) : ℕ) ^ (1 - ε) /
            Real.log (2 ^ r : ℕ) ^ (1 - ε))) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [mul_one] using hmul
  apply hmul'.congr'
  filter_upwards [eventually_ge_atTop 2] with r hr
  have hlogr : 0 < Real.log (2 ^ r : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < (2 : ℕ) ^ r by
      exact one_lt_pow₀ (by omega) (by omega))
  have hlogrs : 0 < Real.log (2 ^ (r + 1) : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < (2 : ℕ) ^ (r + 1) by
      exact one_lt_pow₀ (by omega) (by omega))
  have hpowr : Real.log (2 ^ r : ℕ) ^ (1 - ε) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hlogr _)
  have hpowrs : Real.log (2 ^ (r + 1) : ℕ) ^ (1 - ε) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hlogrs _)
  have hcount : (badOneTermCount (2 ^ (r + 1)) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (one_le_badOneTermCount
      (show 4 ≤ (2 : ℕ) ^ (r + 1) by
        calc
          4 = (2 : ℕ) ^ 2 := by norm_num
          _ ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega))))
  unfold taoDyadicBadOneTermLogWeight
  field_simp

/-- The weighted dyadic one-term counts eventually satisfy a uniform
three-quarters contraction when read backwards. -/
theorem eventually_four_mul_taoDyadicBadOneTermLogWeight_le_three_mul_succ
    (hratio : TaoBadOneTermDyadicRatioConclusion) (ε : ℝ) :
    ∀ᶠ r : ℕ in atTop,
      4 * taoDyadicBadOneTermLogWeight ε r ≤
        3 * taoDyadicBadOneTermLogWeight ε (r + 1) := by
  have hlim := tendsto_taoDyadicBadOneTermLogWeight_ratio hratio ε
  have hlt := (tendsto_order.1 hlim).2 (3 / 4 : ℝ) (by norm_num)
  filter_upwards [hlt, eventually_ge_atTop 2] with r hratioLt hr
  have hnext := taoDyadicBadOneTermLogWeight_pos ε (show 2 ≤ r + 1 by omega)
  have hmul := (div_lt_iff₀ hnext).mp hratioLt
  nlinarith

/-- A geometric one-step inequality makes a finite tail at most four times
its last term. -/
theorem sum_Icc_le_four_mul_last_of_four_mul_le_three_mul
    (f : ℕ → ℝ) {R L : ℕ} (hRL : R ≤ L)
    (hf : ∀ r, 0 ≤ f r)
    (hstep : ∀ r, R ≤ r → r < L → 4 * f r ≤ 3 * f (r + 1)) :
    ∑ r ∈ Icc R L, f r ≤ 4 * f L := by
  induction L, hRL using Nat.le_induction with
  | base =>
      simp
      linarith [hf R]
  | succ L hRL ih =>
      rw [sum_Icc_succ_top (hRL.trans (Nat.le_succ L))]
      have htail := ih (fun r hrR hrL =>
        hstep r hrR (hrL.trans (Nat.lt_succ_self L)))
      have hgeom := hstep L hRL (Nat.lt_succ_self L)
      linarith

/-- Consequently, every sufficiently late finite tail of the weighted
one-term counts is controlled by its top scale. -/
theorem exists_forall_sum_Icc_taoDyadicBadOneTermLogWeight_le
    (hratio : TaoBadOneTermDyadicRatioConclusion) (ε : ℝ) :
    ∃ R : ℕ, ∀ L : ℕ, R ≤ L →
      ∑ r ∈ Icc R L, taoDyadicBadOneTermLogWeight ε r ≤
        4 * taoDyadicBadOneTermLogWeight ε L := by
  obtain ⟨R, hR⟩ := (eventually_atTop.1
    (eventually_four_mul_taoDyadicBadOneTermLogWeight_le_three_mul_succ
      hratio ε))
  refine ⟨R, fun L hRL =>
    sum_Icc_le_four_mul_last_of_four_mul_le_three_mul
      (taoDyadicBadOneTermLogWeight ε) hRL
      (taoDyadicBadOneTermLogWeight_nonneg ε) ?_⟩
  intro r hrR _hrL
  exact hR r hrR

/-- The complete tail of local dyadic-window estimates is summable once the
adjacent one-term ratio is known.  This is the exact analytic consumer behind
the source's dyadic-decomposition sentence. -/
theorem exists_taoBadIntervalDyadicTail_logSaving
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hSS : SylvesterSchurConclusion)
    (h16ii : TaoLemma16iiConclusion)
    (hratio : TaoBadOneTermDyadicRatioConclusion) :
    ∃ q : ℕ → ℕ, ∃ K : ℝ,
      0 < K ∧
      Tendsto q atTop atTop ∧
      Tendsto (fun x =>
        Real.log (taoPrimeTupleSlowLowerCutoff q x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log (taoPrimeTupleSlowUpperCutoff q x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ R : ℕ, 2 ≤ R ∧ ∀ L : ℕ, R ≤ L →
            (∑ r ∈ Icc R L,
                ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) ≤
              4 * K * taoDyadicBadOneTermLogWeight ε L) ∧
            (∑ r ∈ Icc R L, taoDyadicBadOneTermLogWeight ε r ≤
              4 * taoDyadicBadOneTermLogWeight ε L) := by
  obtain ⟨q, K, hK, hq, hlower, hupper, hlocal⟩ :=
    exists_taoBadIntervalDyadicWindow_logSaving hC hburgess hSS h16ii
  refine ⟨q, K, hK, hq, hlower, hupper, ?_⟩
  intro ε hε
  obtain ⟨Rsum, hsum⟩ :=
    exists_forall_sum_Icc_taoDyadicBadOneTermLogWeight_le hratio ε
  have hpow : Tendsto (fun r : ℕ => 2 ^ r) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlocalPow : ∀ᶠ r : ℕ in atTop,
      ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) ≤
        K * taoDyadicBadOneTermLogWeight ε r := by
    have h := hpow.eventually (hlocal ε hε)
    simpa only [taoDyadicBadOneTermLogWeight] using h
  obtain ⟨Rlocal, hRlocal⟩ := eventually_atTop.1 hlocalPow
  let R := max (max Rsum Rlocal) 2
  refine ⟨R, le_max_right _ _, fun L hRL => ?_⟩
  have hRsum : Rsum ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRlocal' : Rlocal ≤ R :=
    le_trans (le_max_right Rsum Rlocal) (le_max_left _ _)
  have hsum' := hsum L (hRsum.trans hRL)
  have hterm : ∀ r ∈ Icc R L,
      ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) ≤
        K * taoDyadicBadOneTermLogWeight ε r := by
    intro r hr
    exact hRlocal r (hRlocal'.trans (Finset.mem_Icc.mp hr).1)
  have hweights :
      ∑ r ∈ Icc R L, taoDyadicBadOneTermLogWeight ε r ≤
        4 * taoDyadicBadOneTermLogWeight ε L := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (show Icc R L ⊆ Icc Rsum L by
        intro r hr
        exact Finset.mem_Icc.mpr
          ⟨hRsum.trans (Finset.mem_Icc.mp hr).1, (Finset.mem_Icc.mp hr).2⟩)
      (fun _ _ _ => taoDyadicBadOneTermLogWeight_nonneg ε _)).trans hsum'
  refine ⟨?_, hweights⟩
  calc
      ∑ r ∈ Icc R L,
          ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) ≤
          ∑ r ∈ Icc R L, K * taoDyadicBadOneTermLogWeight ε r :=
        Finset.sum_le_sum fun r hr => hterm r hr
      _ = K * ∑ r ∈ Icc R L, taoDyadicBadOneTermLogWeight ε r := by
        rw [Finset.mul_sum]
      _ ≤ K * (4 * taoDyadicBadOneTermLogWeight ε L) :=
        mul_le_mul_of_nonneg_left hweights hK.le
      _ = 4 * K * taoDyadicBadOneTermLogWeight ε L := by ring

/-- Dyadic-tail summation from the packaged local window estimate. -/
theorem exists_taoBadIntervalDyadicTail_logSaving_of_window
    (hwindow : TaoBadIntervalDyadicWindowLogSavingConclusion)
    (hratio : TaoBadOneTermDyadicRatioConclusion) :
    ∃ q : ℕ → ℕ, ∃ K : ℝ,
      0 < K ∧
      Tendsto q atTop atTop ∧
      Tendsto (fun x =>
        Real.log (taoPrimeTupleSlowLowerCutoff q x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log (taoPrimeTupleSlowUpperCutoff q x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ R : ℕ, 2 ≤ R ∧ ∀ L : ℕ, R ≤ L →
            (∑ r ∈ Icc R L,
                ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) ≤
              4 * K * taoDyadicBadOneTermLogWeight ε L) ∧
            (∑ r ∈ Icc R L, taoDyadicBadOneTermLogWeight ε r ≤
              4 * taoDyadicBadOneTermLogWeight ε L) := by
  obtain ⟨q, K, hK, hq, hlower, hupper, hlocal⟩ := hwindow
  refine ⟨q, K, hK, hq, hlower, hupper, ?_⟩
  intro ε hε
  obtain ⟨Rsum, hsum⟩ :=
    exists_forall_sum_Icc_taoDyadicBadOneTermLogWeight_le hratio ε
  have hpow : Tendsto (fun r : ℕ => 2 ^ r) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlocalPow : ∀ᶠ r : ℕ in atTop,
      ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) ≤
        K * taoDyadicBadOneTermLogWeight ε r := by
    have h := hpow.eventually (hlocal ε hε)
    simpa only [taoDyadicBadOneTermLogWeight] using h
  obtain ⟨Rlocal, hRlocal⟩ := eventually_atTop.1 hlocalPow
  let R := max (max Rsum Rlocal) 2
  refine ⟨R, le_max_right _ _, fun L hRL => ?_⟩
  have hRsum : Rsum ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRlocal' : Rlocal ≤ R :=
    le_trans (le_max_right Rsum Rlocal) (le_max_left _ _)
  have hsum' := hsum L (hRsum.trans hRL)
  have hterm : ∀ r ∈ Icc R L,
      ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) ≤
        K * taoDyadicBadOneTermLogWeight ε r := by
    intro r hr
    exact hRlocal r (hRlocal'.trans (Finset.mem_Icc.mp hr).1)
  have hweights :
      ∑ r ∈ Icc R L, taoDyadicBadOneTermLogWeight ε r ≤
        4 * taoDyadicBadOneTermLogWeight ε L := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (show Icc R L ⊆ Icc Rsum L by
        intro r hr
        exact Finset.mem_Icc.mpr
          ⟨hRsum.trans (Finset.mem_Icc.mp hr).1, (Finset.mem_Icc.mp hr).2⟩)
      (fun _ _ _ => taoDyadicBadOneTermLogWeight_nonneg ε _)).trans hsum'
  refine ⟨?_, hweights⟩
  calc
      ∑ r ∈ Icc R L,
          ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) ≤
          ∑ r ∈ Icc R L, K * taoDyadicBadOneTermLogWeight ε r :=
        Finset.sum_le_sum fun r hr => hterm r hr
      _ = K * ∑ r ∈ Icc R L, taoDyadicBadOneTermLogWeight ε r := by
        rw [Finset.mul_sum]
      _ ≤ K * (4 * taoDyadicBadOneTermLogWeight ε L) :=
        mul_le_mul_of_nonneg_left hweights hK.le
      _ = 4 * K * taoDyadicBadOneTermLogWeight ε L := by ring

/-- The complete dyadic tail no longer needs unrestricted Sylvester--Schur. -/
theorem exists_taoBadIntervalDyadicTail_logSaving_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (h16ii : TaoLemma16iiConclusion)
    (hratio : TaoBadOneTermDyadicRatioConclusion) :
    ∃ q : ℕ → ℕ, ∃ K : ℝ,
      0 < K ∧
      Tendsto q atTop atTop ∧
      Tendsto (fun x =>
        Real.log (taoPrimeTupleSlowLowerCutoff q x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log (taoPrimeTupleSlowUpperCutoff q x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ R : ℕ, 2 ≤ R ∧ ∀ L : ℕ, R ≤ L →
            (∑ r ∈ Icc R L,
                ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) ≤
              4 * K * taoDyadicBadOneTermLogWeight ε L) ∧
            (∑ r ∈ Icc R L, taoDyadicBadOneTermLogWeight ε r ≤
              4 * taoDyadicBadOneTermLogWeight ε L) :=
  exists_taoBadIntervalDyadicTail_logSaving_of_window
    (taoBadIntervalDyadicWindowLogSaving_of_explicitBurgess hC hburgess h16ii)
    hratio

/-- The complete conclusion delivered by dyadic-tail summation. -/
abbrev TaoBadIntervalDyadicTailLogSavingConclusion : Prop :=
  ∃ q : ℕ → ℕ, ∃ K : ℝ,
    0 < K ∧
    Tendsto q atTop atTop ∧
    Tendsto (fun x =>
      Real.log (taoPrimeTupleSlowLowerCutoff q x) /
        Real.log (taoZ x)) atTop (𝓝 1) ∧
    Tendsto (fun x =>
      Real.log (taoPrimeTupleSlowUpperCutoff q x) /
        Real.log (taoZ x)) atTop (𝓝 1) ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ R : ℕ, 2 ≤ R ∧ ∀ L : ℕ, R ≤ L →
          (∑ r ∈ Icc R L,
              ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) ≤
            4 * K * taoDyadicBadOneTermLogWeight ε L) ∧
          (∑ r ∈ Icc R L, taoDyadicBadOneTermLogWeight ε r ≤
            4 * taoDyadicBadOneTermLogWeight ε L)

/-- The complete conclusion after absorbing the finitely many early dyadic
windows. -/
abbrev TaoBadIntervalDyadicPartialSumsLogSavingConclusion : Prop :=
  ∃ q : ℕ → ℕ,
    Tendsto q atTop atTop ∧
    Tendsto (fun x =>
      Real.log (taoPrimeTupleSlowLowerCutoff q x) /
        Real.log (taoZ x)) atTop (𝓝 1) ∧
    Tendsto (fun x =>
      Real.log (taoPrimeTupleSlowUpperCutoff q x) /
        Real.log (taoZ x)) atTop (𝓝 1) ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ A : ℝ, 0 < A ∧ ∃ R : ℕ, ∀ L : ℕ, R ≤ L →
        ∑ r ∈ range (L + 1),
            ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) ≤
          A * taoDyadicBadOneTermLogWeight ε L

/-- After enlarging the epsilon-dependent constant, the finitely many early
dyadic windows can be included as well. -/
theorem exists_taoBadIntervalDyadicPartialSums_logSaving_of_tail
    (htailConclusion : TaoBadIntervalDyadicTailLogSavingConclusion) :
    TaoBadIntervalDyadicPartialSumsLogSavingConclusion := by
  obtain ⟨q, K, hK, hq, hlower, hupper, htail⟩ :=
    htailConclusion
  refine ⟨q, hq, hlower, hupper, ?_⟩
  intro ε hε
  obtain ⟨R, hRtwo, hR⟩ := htail ε hε
  let P : ℝ := ∑ r ∈ range R,
    ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ)
  let W : ℝ := taoDyadicBadOneTermLogWeight ε R
  have hW : 0 < W := taoDyadicBadOneTermLogWeight_pos ε hRtwo
  let A : ℝ := 4 * K + 4 * P / W
  have hP : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  refine ⟨A, hA, R, fun L hRL => ?_⟩
  have htailL := hR L hRL
  have hWleSum : W ≤
      ∑ r ∈ Icc R L, taoDyadicBadOneTermLogWeight ε r := by
    dsimp only [W]
    exact Finset.single_le_sum
      (fun r _ => taoDyadicBadOneTermLogWeight_nonneg ε r)
      (Finset.mem_Icc.mpr ⟨le_rfl, hRL⟩)
  have hWle : W ≤ 4 * taoDyadicBadOneTermLogWeight ε L :=
    hWleSum.trans htailL.2
  have hprefix : P ≤ (4 * P / W) *
      taoDyadicBadOneTermLogWeight ε L := by
    have hPW : 0 ≤ P / W := div_nonneg hP hW.le
    have hmul := mul_le_mul_of_nonneg_left hWle hPW
    calc
      P = (P / W) * W := by field_simp
      _ ≤ (P / W) * (4 * taoDyadicBadOneTermLogWeight ε L) := hmul
      _ = (4 * P / W) * taoDyadicBadOneTermLogWeight ε L := by ring
  have hsplit :
      (∑ r ∈ range (L + 1),
          ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ)) =
        P + ∑ r ∈ Icc R L,
          ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) := by
    dsimp only [P]
    rw [← Finset.sum_range_add_sum_Ico
      (f := fun r =>
        ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ))
          (hRL.trans (Nat.le_succ L))]
    congr 2
  rw [hsplit]
  calc
    P + ∑ r ∈ Icc R L,
        ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) ≤
        (4 * P / W) * taoDyadicBadOneTermLogWeight ε L +
          4 * K * taoDyadicBadOneTermLogWeight ε L :=
      add_le_add hprefix htailL.1
    _ = A * taoDyadicBadOneTermLogWeight ε L := by
      dsimp only [A]
      ring

/-- Compatibility form of the partial-sum estimate using the global
Sylvester--Schur interface. -/
theorem exists_taoBadIntervalDyadicPartialSums_logSaving
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hSS : SylvesterSchurConclusion)
    (h16ii : TaoLemma16iiConclusion)
    (hratio : TaoBadOneTermDyadicRatioConclusion) :
    TaoBadIntervalDyadicPartialSumsLogSavingConclusion :=
  exists_taoBadIntervalDyadicPartialSums_logSaving_of_tail
    (exists_taoBadIntervalDyadicTail_logSaving
      hC hburgess hSS h16ii hratio)

/-- The complete dyadic partial sums no longer need unrestricted
Sylvester--Schur. -/
theorem exists_taoBadIntervalDyadicPartialSums_logSaving_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (h16ii : TaoLemma16iiConclusion)
    (hratio : TaoBadOneTermDyadicRatioConclusion) :
    TaoBadIntervalDyadicPartialSumsLogSavingConclusion :=
  exists_taoBadIntervalDyadicPartialSums_logSaving_of_tail
    (exists_taoBadIntervalDyadicTail_logSaving_of_explicitBurgess
      hC hburgess h16ii hratio)

/-! ## Comparison of the top dyadic endpoint with the original cutoff -/

/-- The endpoint selected by the exact finite cover lies between `x` and
`2*x`. -/
theorem taoDyadicTopEndpoint_bounds {x : ℕ} (hx : 0 < x) :
    x ≤ 2 ^ (Nat.log 2 x + 1) ∧
      2 ^ (Nat.log 2 x + 1) ≤ 2 * x := by
  constructor
  · exact (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) x).le
  · rw [pow_succ]
    have hpow := Nat.pow_log_le_self 2 hx.ne'
    omega

/-- Lemma 1.6(ii) compares the weighted count at the top endpoint of the
dyadic cover with the same weighted count at `x`, provided the logarithmic
exponent is nonnegative. -/
theorem exists_eventually_taoDyadicTopLogWeight_le
    (h16ii : TaoLemma16iiConclusion) {ε : ℝ} (hεone : ε ≤ 1) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ x : ℕ in atTop,
        taoDyadicBadOneTermLogWeight ε (Nat.log 2 x + 1) ≤
          D * ((badOneTermCount x : ℝ) /
            Real.log x ^ (1 - ε)) := by
  obtain ⟨D, hDpos, hD⟩ :=
    ((h16ii (2 : ℝ) (by norm_num)).isBigO).exists_pos
  refine ⟨D, hDpos, ?_⟩
  filter_upwards [hD.bound, eventually_ge_atTop 3] with x hDx hx
  have hxpos : 0 < x := by omega
  have hbounds := taoDyadicTopEndpoint_bounds hxpos
  have hDilation :
      (badOneTermCount (2 * x) : ℝ) ≤
        D * (badOneTermCount x : ℝ) := by
    have hdilationEq : taoNaturalDilation (2 : ℝ) x = 2 * x := by
      simpa using taoNaturalDilation_natCast 2 x
    rw [hdilationEq] at hDx
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (badOneTermCount (2 * x) : ℝ) by positivity),
      abs_of_nonneg (show 0 ≤ (badOneTermCount x : ℝ) by positivity)] using hDx
  have hcountNat :
      badOneTermCount (2 ^ (Nat.log 2 x + 1)) ≤
        badOneTermCount (2 * x) :=
    countUpTo_mono_right hbounds.2
  have hcount :
      (badOneTermCount (2 ^ (Nat.log 2 x + 1)) : ℝ) ≤
        D * (badOneTermCount x : ℝ) := by
    have hcountCast :
        (badOneTermCount (2 ^ (Nat.log 2 x + 1)) : ℝ) ≤
          (badOneTermCount (2 * x) : ℝ) := by
      exact_mod_cast hcountNat
    exact hcountCast.trans hDilation
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlogtop : 0 < Real.log (2 ^ (Nat.log 2 x + 1) : ℕ) :=
    Real.log_pos (by
      exact_mod_cast (show 1 < 2 ^ (Nat.log 2 x + 1) from
        one_lt_pow₀ (by norm_num) (by omega)))
  have hlogle :
      Real.log (x : ℝ) ≤
        Real.log (2 ^ (Nat.log 2 x + 1) : ℕ) := by
    exact Real.log_le_log (by exact_mod_cast hxpos) (by exact_mod_cast hbounds.1)
  have hexponent : 0 ≤ 1 - ε := sub_nonneg.mpr hεone
  have hdenle :
      Real.log (x : ℝ) ^ (1 - ε) ≤
        Real.log (2 ^ (Nat.log 2 x + 1) : ℕ) ^ (1 - ε) :=
    Real.rpow_le_rpow hlogx.le hlogle hexponent
  have hdentop :
      0 < Real.log (2 ^ (Nat.log 2 x + 1) : ℕ) ^ (1 - ε) :=
    Real.rpow_pos_of_pos hlogtop _
  have hdenx : 0 < Real.log (x : ℝ) ^ (1 - ε) :=
    Real.rpow_pos_of_pos hlogx _
  unfold taoDyadicBadOneTermLogWeight
  calc
    (badOneTermCount (2 ^ (Nat.log 2 x + 1)) : ℝ) /
          Real.log (2 ^ (Nat.log 2 x + 1) : ℕ) ^ (1 - ε) ≤
        (D * (badOneTermCount x : ℝ)) /
          Real.log (2 ^ (Nat.log 2 x + 1) : ℕ) ^ (1 - ε) :=
      div_le_div_of_nonneg_right hcount hdentop.le
    _ ≤ (D * (badOneTermCount x : ℝ)) /
          Real.log (x : ℝ) ^ (1 - ε) :=
      div_le_div_of_nonneg_left
        (mul_nonneg hDpos.le (Nat.cast_nonneg _)) hdenx hdenle
    _ = D * ((badOneTermCount x : ℝ) /
          Real.log x ^ (1 - ε)) := by ring

/-- Global logarithmic saving from the packaged dyadic partial sums.  This
separates the exact finite dyadic cover from the upstream interval input. -/
theorem taoTheorem17_logPowerSaving_of_partialSums
    (h16ii : TaoLemma16iiConclusion)
    (hpartialConclusion :
      TaoBadIntervalDyadicPartialSumsLogSavingConclusion) :
    LogPowerSavingRelative
      (fun x => (nontrivialBadCount x : ℝ))
      (fun x => (badOneTermCount x : ℝ)) := by
  intro ε hε
  let δ : ℝ := min ε (1 / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδone : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨q, hq, hlower, hupper, hpartial⟩ :=
    hpartialConclusion
  obtain ⟨A, hA, R, hR⟩ := hpartial δ hδ
  obtain ⟨D, hD, htop⟩ :=
    exists_eventually_taoDyadicTopLogWeight_le h16ii hδone
  refine IsBigO.of_bound (A * D) ?_
  filter_upwards [htop,
    eventually_ge_atTop (max (2 ^ R) 3)] with x htopX hx
  have hxpow : 2 ^ R ≤ x := le_trans (le_max_left _ _) hx
  have hxthree : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hRlog : R ≤ Nat.log 2 x :=
    Nat.le_log_of_pow_le (by norm_num) hxpow
  have hRtop : R ≤ Nat.log 2 x + 1 := hRlog.trans (Nat.le_succ _)
  have hpartialX := hR (Nat.log 2 x + 1) hRtop
  have hcoverNat := nontrivialBadCount_le_sum_dyadicWindowCards x
  have hcoverReal :
      (nontrivialBadCount x : ℝ) ≤
        ∑ r ∈ nontrivialBadDyadicExponents x,
          ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) := by
    exact_mod_cast hcoverNat
  have hsum :
      (nontrivialBadCount x : ℝ) ≤
        A * taoDyadicBadOneTermLogWeight δ (Nat.log 2 x + 1) := by
    calc
      (nontrivialBadCount x : ℝ) ≤
          ∑ r ∈ nontrivialBadDyadicExponents x,
            ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) :=
        hcoverReal
      _ = ∑ r ∈ range (Nat.log 2 x + 1 + 1),
            ((nontrivialBadNumbersInDyadicWindow (2 ^ r)).card : ℝ) := by
        simp only [nontrivialBadDyadicExponents]
      _ ≤ A * taoDyadicBadOneTermLogWeight δ (Nat.log 2 x + 1) :=
        hpartialX
  have hxpos : 0 < x := by omega
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlogone : 1 ≤ Real.log (x : ℝ) := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast hxpos)]
    exact (Real.exp_one_lt_three.le.trans (by exact_mod_cast hxthree))
  have hexponents : 1 - ε ≤ 1 - δ := sub_le_sub_left hδε 1
  have hdenExponent :
      Real.log (x : ℝ) ^ (1 - ε) ≤
        Real.log (x : ℝ) ^ (1 - δ) :=
    Real.rpow_le_rpow_of_exponent_le hlogone hexponents
  have hdenε : 0 < Real.log (x : ℝ) ^ (1 - ε) :=
    Real.rpow_pos_of_pos hlogx _
  have hquotient :
      (badOneTermCount x : ℝ) / Real.log x ^ (1 - δ) ≤
        (badOneTermCount x : ℝ) / Real.log x ^ (1 - ε) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hdenε hdenExponent
  have hresult :
      (nontrivialBadCount x : ℝ) ≤
        (A * D) * ((badOneTermCount x : ℝ) /
          Real.log x ^ (1 - ε)) := by
    calc
      (nontrivialBadCount x : ℝ) ≤
          A * taoDyadicBadOneTermLogWeight δ (Nat.log 2 x + 1) := hsum
      _ ≤ A * (D * ((badOneTermCount x : ℝ) /
            Real.log x ^ (1 - δ))) :=
        mul_le_mul_of_nonneg_left htopX hA.le
      _ ≤ A * (D * ((badOneTermCount x : ℝ) /
            Real.log x ^ (1 - ε))) := by
        gcongr
      _ = (A * D) * ((badOneTermCount x : ℝ) /
            Real.log x ^ (1 - ε)) := by ring
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (nontrivialBadCount x : ℝ) by positivity),
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hdenε.le)] using hresult

/-- Compatibility form of the logarithmic saving using the global
Sylvester--Schur interface. -/
theorem taoTheorem17_logPowerSaving_of_badOneTermDyadicRatio
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hSS : SylvesterSchurConclusion)
    (h16ii : TaoLemma16iiConclusion)
    (hratio : TaoBadOneTermDyadicRatioConclusion) :
    LogPowerSavingRelative
      (fun x => (nontrivialBadCount x : ℝ))
      (fun x => (badOneTermCount x : ℝ)) :=
  taoTheorem17_logPowerSaving_of_partialSums h16ii
    (exists_taoBadIntervalDyadicPartialSums_logSaving
      hC hburgess hSS h16ii hratio)

/-- The logarithmic saving required by Theorem 1.7 follows from explicit
Burgess and the analytic one-term inputs, without unrestricted
Sylvester--Schur. -/
theorem taoTheorem17_logPowerSaving_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (h16ii : TaoLemma16iiConclusion)
    (hratio : TaoBadOneTermDyadicRatioConclusion) :
    LogPowerSavingRelative
      (fun x => (nontrivialBadCount x : ℝ))
      (fun x => (badOneTermCount x : ℝ)) :=
  taoTheorem17_logPowerSaving_of_partialSums h16ii
    (exists_taoBadIntervalDyadicPartialSums_logSaving_of_explicitBurgess
      hC hburgess h16ii hratio)

/-- The logarithmic saving for the nontrivial part, together with Lemma
1.6(i) for the one-term part, implies the quotient-power asymptotic for the
full bad count. -/
theorem badCount_quotientPowerScale_of_logPowerSavingRelative
    (hsaving : LogPowerSavingRelative
      (fun x => (nontrivialBadCount x : ℝ))
      (fun x => (badOneTermCount x : ℝ))) :
    QuotientPowerScale
      (fun x => (badCount x : ℝ))
      (fun x => (x : ℝ)) taoZ 2 := by
  have hnonO := hsaving 1 (by norm_num)
  obtain ⟨E, hEpos, hE⟩ := hnonO.exists_pos
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hscale := badOneTermCount_quotientPowerScale ε hε
  have hscaleHalf := badOneTermCount_quotientPowerScale (ε / 2) hhalf
  have habsorb : ∀ᶠ x : ℕ in atTop,
      E + 1 ≤ taoZ x ^ (ε / 2) :=
    ((tendsto_rpow_atTop hhalf).comp tendsto_taoZ_atTop).eventually
      (eventually_ge_atTop (E + 1))
  filter_upwards [hE.bound, hscale, hscaleHalf, habsorb] with
      x hnonNorm hscaleX hscaleHalfX habsorbX
  have hnon :
      (nontrivialBadCount x : ℝ) ≤
        E * (badOneTermCount x : ℝ) := by
    simpa only [sub_self, Real.rpow_zero, div_one, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (nontrivialBadCount x : ℝ) by positivity),
      abs_of_nonneg (show 0 ≤ (badOneTermCount x : ℝ) by positivity)]
        using hnonNorm
  have hcountEq :
      (nontrivialBadCount x : ℝ) + (badOneTermCount x : ℝ) =
        (badCount x : ℝ) := by
    exact_mod_cast nontrivialBadCount_add_badOneTermCount x
  constructor
  · calc
      (x : ℝ) / taoZ x ^ (2 + ε) ≤
          (badOneTermCount x : ℝ) := hscaleX.1
      _ ≤ (badCount x : ℝ) := by
        rw [← hcountEq]
        linarith [show 0 ≤ (nontrivialBadCount x : ℝ) by positivity]
  · have hbadUpper :
        (badCount x : ℝ) ≤
          (E + 1) * (badOneTermCount x : ℝ) := by
      rw [← hcountEq]
      linarith
    have hmodelNonneg :
        0 ≤ (x : ℝ) / taoZ x ^ (2 - ε / 2) :=
      div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (taoZ_pos x).le _)
    calc
      (badCount x : ℝ) ≤
          (E + 1) * (badOneTermCount x : ℝ) := hbadUpper
      _ ≤ (E + 1) *
          ((x : ℝ) / taoZ x ^ (2 - ε / 2)) :=
        mul_le_mul_of_nonneg_left hscaleHalfX.2 (by linarith)
      _ ≤ taoZ x ^ (ε / 2) *
          ((x : ℝ) / taoZ x ^ (2 - ε / 2)) :=
        mul_le_mul_of_nonneg_right habsorbX hmodelNonneg
      _ = (x : ℝ) / taoZ x ^ (2 - ε) := by
        have hzHalf : taoZ x ^ (ε / 2) ≠ 0 :=
          ne_of_gt (Real.rpow_pos_of_pos (taoZ_pos x) _)
        have hzBase : taoZ x ^ (2 - ε) ≠ 0 :=
          ne_of_gt (Real.rpow_pos_of_pos (taoZ_pos x) _)
        rw [show (2 - ε / 2 : ℝ) = (2 - ε) + ε / 2 by ring,
          Real.rpow_add (taoZ_pos x)]
        field_simp [hzHalf, hzBase]

/-- Exact conditional form of Tao's Theorem 1.7 obtained from the three
remaining analytic hypotheses. -/
theorem taoTheorem17_of_badOneTermDyadicRatio
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hSS : SylvesterSchurConclusion)
    (h16ii : TaoLemma16iiConclusion)
    (hratio : TaoBadOneTermDyadicRatioConclusion) :
    TaoTheorem17Conclusion := by
  have hsaving := taoTheorem17_logPowerSaving_of_badOneTermDyadicRatio
    hC hburgess hSS h16ii hratio
  exact ⟨hsaving,
    badCount_quotientPowerScale_of_logPowerSavingRelative hsaving⟩

/-- Exact form of Tao's Theorem 1.7 from explicit Burgess and the two
one-term analytic inputs.  Unrestricted Sylvester--Schur is not needed:
the eventual start-uniform theorem supplies every sufficiently large
admissible dyadic scale. -/
theorem taoTheorem17_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (h16ii : TaoLemma16iiConclusion)
    (hratio : TaoBadOneTermDyadicRatioConclusion) :
    TaoTheorem17Conclusion := by
  have hsaving := taoTheorem17_logPowerSaving_of_explicitBurgess
    hC hburgess h16ii hratio
  exact ⟨hsaving,
    badCount_quotientPowerScale_of_logPowerSavingRelative hsaving⟩

end

end Tao2026
