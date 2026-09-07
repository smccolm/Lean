import PrimeShell.ShiftBlock

namespace PrimeShell

noncomputable section

open scoped BigOperators ArithmeticFunction
open Set MeasureTheory Real
open Zeta23 Zeta23.PrimeSide

/-- The literal dyadic trace contribution from shifts in `(J,K]`. -/
def dyadicShiftBlockSum
    (Phi : ℝ → ℝ) (T : ℝ) (N J K : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2 * N), rowShiftBlockSum Phi T N n J K

/-- Exact row-wise reindexing of a dyadic shift block. -/
theorem dyadicShiftBlockSum_eq_double_sum
    (Phi : ℝ → ℝ) (T : ℝ) (N J K : ℕ) :
    dyadicShiftBlockSum Phi T N J K =
      ∑ h ∈ Finset.Ioc J K, ∑ n ∈ Finset.Ioc N (2 * N),
        if n + h ∈ Finset.Ioc N (2 * N) then
          dyadicLambdaWeight n h * dyadicShiftKernel Phi T n h
        else 0 := by
  unfold dyadicShiftBlockSum rowShiftBlockSum
  rw [Finset.sum_comm]

/-- Rows on which both the dyadic right edge and every requested GM endpoint
are valid. -/
def goodInteriorRows
    (C : ℝ) (N K : ℕ) (lengths : Finset ℕ) : Finset ℕ :=
  (Finset.Ioc N (2 * N)).filter fun n =>
    n + K ≤ 2 * N ∧ n ∉ gmSimultaneousLambdaBadSet C N lengths

/-- The exact anchored main term over all good interior rows. -/
def goodDyadicShiftBlockMain
    (Phi : ℝ → ℝ) (T C : ℝ) (N J K : ℕ)
    (lengths : Finset ℕ) : ℝ :=
  ∑ n ∈ goodInteriorRows C N K lengths,
    rowShiftBlockAnchor Phi T n J * normalizedRowBlockMain n J K

/-- Exact residual trace on the complementary exceptional-or-boundary rows. -/
def badOrBoundaryShiftBlock
    (Phi : ℝ → ℝ) (T C : ℝ) (N J K : ℕ)
    (lengths : Finset ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc N (2 * N)).filter fun n =>
      ¬(n + K ≤ 2 * N ∧
        n ∉ gmSimultaneousLambdaBadSet C N lengths),
    rowShiftBlockSum Phi T N n J K

/-- Exact partition of the full block into its good anchored main, good-row
errors, and the complementary exceptional-or-boundary contribution. -/
theorem dyadicShiftBlockSum_eq_good_main_add_errors
    (Phi : ℝ → ℝ) (T C : ℝ) (N J K : ℕ)
    (lengths : Finset ℕ) :
    dyadicShiftBlockSum Phi T N J K =
      goodDyadicShiftBlockMain Phi T C N J K lengths +
      (∑ n ∈ goodInteriorRows C N K lengths,
        (rowShiftBlockSum Phi T N n J K -
          rowShiftBlockAnchor Phi T n J * normalizedRowBlockMain n J K)) +
      badOrBoundaryShiftBlock Phi T C N J K lengths := by
  unfold dyadicShiftBlockSum goodDyadicShiftBlockMain
    badOrBoundaryShiftBlock goodInteriorRows
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.Ioc N (2 * N))
    (fun n => n + K ≤ 2 * N ∧
      n ∉ gmSimultaneousLambdaBadSet C N lengths)]
  rw [← Finset.sum_add_distrib]
  apply congrArg₂ (· + ·) _ rfl
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Complete finite global block consumer.  Its last term is deliberately
the literal complement rather than a hidden `O`-term; subsequent lemmas
bound the exceptional and boundary pieces separately. -/
theorem abs_dyadicShiftBlockSum_sub_goodMain_le
    {Phi : ℝ → ℝ} {T C : ℝ} {N J K : ℕ}
    {lengths : Finset ℕ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hN : 1 ≤ N)
    (hJ : J ∈ lengths) (hK : K ∈ lengths) (hJK : J ≤ K)
    (hKN : K ≤ N)
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|) :
    |dyadicShiftBlockSum Phi T N J K -
        goodDyadicShiftBlockMain Phi T C N J K lengths| ≤
      (∑ n ∈ goodInteriorRows C N K lengths,
        goodRowShiftBlockErrorBudget Phi T C N N n J K) +
      |badOrBoundaryShiftBlock Phi T C N J K lengths| := by
  rw [dyadicShiftBlockSum_eq_good_main_add_errors]
  ring_nf
  calc
    |(∑ n ∈ goodInteriorRows C N K lengths,
        (rowShiftBlockSum Phi T N n J K -
          rowShiftBlockAnchor Phi T n J * normalizedRowBlockMain n J K)) +
        badOrBoundaryShiftBlock Phi T C N J K lengths| ≤
      |∑ n ∈ goodInteriorRows C N K lengths,
        (rowShiftBlockSum Phi T N n J K -
          rowShiftBlockAnchor Phi T n J * normalizedRowBlockMain n J K)| +
        |badOrBoundaryShiftBlock Phi T C N J K lengths| := abs_add_le _ _
    _ ≤ (∑ n ∈ goodInteriorRows C N K lengths,
          goodRowShiftBlockErrorBudget Phi T C N N n J K) +
        |badOrBoundaryShiftBlock Phi T C N J K lengths| := by
      apply add_le_add _ le_rfl
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro n hnGood
      have hnData := (Finset.mem_filter.mp hnGood)
      have hnDyadic := hnData.1
      have hnConditions := hnData.2
      exact abs_rowShiftBlockSum_sub_anchoredMain_le
        hT hC hN hnDyadic
        (Finset.mem_Icc.mpr ⟨Nat.le_of_lt (Finset.mem_Ioc.mp hnDyadic).1,
          (Finset.mem_Ioc.mp hnDyadic).2⟩)
        hnConditions.2 hJ hK hJK hnConditions.1 hKN hPhi hPhi2 hPhiAbs

/-- Uniform coefficient majorant on an explicitly bounded dyadic region. -/
theorem acoef_le_log_three_mul_div_sqrt
    {N n : ℕ} (hN : 1 ≤ N) (hnN : N ≤ n) (hn3 : n ≤ 3 * N) :
    acoef n ≤ Real.log (3 * N : ℕ) / Real.sqrt N := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hN.trans hnN)
  have h3Npos : (0 : ℝ) < (↑(3 * N) : ℝ) := by positivity
  have hlog : Real.log n ≤ Real.log (3 * N : ℕ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hnpos) (Set.mem_Ioi.mpr h3Npos)
      (by exact_mod_cast hn3)
  have hsqrt : Real.sqrt N ≤ Real.sqrt n :=
    Real.sqrt_le_sqrt (by exact_mod_cast hnN)
  unfold acoef
  calc
    ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤
        Real.log n / Real.sqrt n :=
      div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
        (Real.sqrt_nonneg _)
    _ ≤ Real.log n / Real.sqrt N :=
      div_le_div_of_nonneg_left (Real.log_natCast_nonneg n)
        (Real.sqrt_pos.2 hNpos) hsqrt
    _ ≤ Real.log (3 * N : ℕ) / Real.sqrt N :=
      div_le_div_of_nonneg_right hlog (Real.sqrt_nonneg _)

/-- A named coefficient majorant used in the global exceptional and boundary
ledgers. -/
def dyadicAcoefMajorant (N : ℕ) : ℝ :=
  Real.log (3 * N : ℕ) / Real.sqrt N

/-- Literal boundary strip where a full shift block no longer fits before
the dyadic right endpoint. -/
def rightBoundaryRows (N K : ℕ) : Finset ℕ :=
  (Finset.Ioc N (2 * N)).filter fun n => 2 * N < n + K

theorem card_rightBoundaryRows_le (N K : ℕ) :
    (rightBoundaryRows N K).card ≤ K := by
  have hsub : rightBoundaryRows N K ⊆ Finset.Ioc (2 * N - K) (2 * N) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    simp only [Finset.mem_Ioc]
    have hnIoc := Finset.mem_Ioc.mp hn'.1
    omega
  calc
    (rightBoundaryRows N K).card ≤
        (Finset.Ioc (2 * N - K) (2 * N)).card := Finset.card_le_card hsub
    _ = 2 * N - (2 * N - K) := by simp
    _ ≤ K := by omega

/-- The complementary rows are covered by the simultaneous GM exceptional
set and the explicit right-boundary strip. -/
theorem card_badOrBoundaryRows_le
    (C : ℝ) (N K : ℕ) (lengths : Finset ℕ) :
    ((Finset.Ioc N (2 * N)).filter fun n =>
      ¬(n + K ≤ 2 * N ∧
        n ∉ gmSimultaneousLambdaBadSet C N lengths)).card ≤
      (gmSimultaneousLambdaBadSet C N lengths).card + K := by
  let S := (Finset.Ioc N (2 * N)).filter fun n =>
    ¬(n + K ≤ 2 * N ∧
      n ∉ gmSimultaneousLambdaBadSet C N lengths)
  have hsub : S ⊆
      gmSimultaneousLambdaBadSet C N lengths ∪ rightBoundaryRows N K := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    simp only [Finset.mem_union]
    by_cases hbad : n ∈ gmSimultaneousLambdaBadSet C N lengths
    · exact Or.inl hbad
    · right
      unfold rightBoundaryRows
      simp only [Finset.mem_filter]
      refine ⟨hn'.1, ?_⟩
      have hnotRight : ¬n + K ≤ 2 * N := by
        intro hRight
        exact hn'.2 ⟨hRight, hbad⟩
      omega
  change S.card ≤ _
  calc
    S.card ≤
        (gmSimultaneousLambdaBadSet C N lengths ∪
          rightBoundaryRows N K).card := Finset.card_le_card hsub
    _ ≤ (gmSimultaneousLambdaBadSet C N lengths).card +
          (rightBoundaryRows N K).card :=
      Finset.card_union_le _ _
    _ ≤ (gmSimultaneousLambdaBadSet C N lengths).card + K :=
      add_le_add le_rfl (card_rightBoundaryRows_le N K)

/-- Uniform absolute bound for one literal row/block, valid on good,
exceptional, and boundary rows alike. -/
theorem abs_rowShiftBlockSum_le_uniform
    {Phi : ℝ → ℝ} {T : ℝ} {N n J K : ℕ}
    (hT : 0 ≤ T) (hN : 1 ≤ N)
    (hn : n ∈ Finset.Ioc N (2 * N))
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2) :
    |rowShiftBlockSum Phi T N n J K| ≤
      (K - J : ℕ) * dyadicAcoefMajorant N ^ 2 *
        (2 * T * ∫ x, Phi x ^ 2) := by
  unfold rowShiftBlockSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    (∑ h ∈ Finset.Ioc J K,
      |if n + h ∈ Finset.Ioc N (2 * N) then
        dyadicLambdaWeight n h * dyadicShiftKernel Phi T n h else 0|) ≤
      ∑ _h ∈ Finset.Ioc J K,
        dyadicAcoefMajorant N ^ 2 * (2 * T * ∫ x, Phi x ^ 2) := by
      apply Finset.sum_le_sum
      intro h hhmem
      by_cases hmem : n + h ∈ Finset.Ioc N (2 * N)
      · simp only [hmem, if_true, abs_mul]
        rw [abs_of_nonneg (dyadicLambdaWeight_nonneg n h)]
        have hnData := Finset.mem_Ioc.mp hn
        have hnhData := Finset.mem_Ioc.mp hmem
        have hnMajor : acoef n ≤ dyadicAcoefMajorant N := by
          unfold dyadicAcoefMajorant
          exact acoef_le_log_three_mul_div_sqrt hN
            (Nat.le_of_lt hnData.1) (hnData.2.trans (by omega))
        have hnhMajor : acoef (n + h) ≤ dyadicAcoefMajorant N := by
          unfold dyadicAcoefMajorant
          exact acoef_le_log_three_mul_div_sqrt hN
            (Nat.le_of_lt hnhData.1) (hnhData.2.trans (by omega))
        have hw : dyadicLambdaWeight n h ≤ dyadicAcoefMajorant N ^ 2 := by
          unfold dyadicLambdaWeight
          rw [pow_two]
          exact mul_le_mul hnMajor hnhMajor (acoef_nonneg _) (by
            unfold dyadicAcoefMajorant
            positivity)
        have hhOne : 1 ≤ h := by
          have hh := Finset.mem_Ioc.mp hhmem
          omega
        have hk := abs_dyadicShiftKernel_le_two_mul_T
          (n := n) (h := h) hT (by omega) hhOne hPhi hPhi2
        exact mul_le_mul hw hk (abs_nonneg _) (by positivity)
      · simp only [hmem, if_false, abs_zero]
        positivity
    _ = (K - J : ℕ) * dyadicAcoefMajorant N ^ 2 *
        (2 * T * ∫ x, Phi x ^ 2) := by simp [mul_assoc]

/-- The exceptional-plus-boundary trace is controlled by its exact row
count and the uniform literal row majorant. -/
theorem abs_badOrBoundaryShiftBlock_le
    {Phi : ℝ → ℝ} {T C : ℝ} {N J K : ℕ}
    {lengths : Finset ℕ}
    (hT : 0 ≤ T) (hN : 1 ≤ N)
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2) :
    |badOrBoundaryShiftBlock Phi T C N J K lengths| ≤
      ((gmSimultaneousLambdaBadSet C N lengths).card + K : ℕ) *
        ((K - J : ℕ) * dyadicAcoefMajorant N ^ 2 *
          (2 * T * ∫ x, Phi x ^ 2)) := by
  unfold badOrBoundaryShiftBlock
  let S := (Finset.Ioc N (2 * N)).filter fun n =>
      ¬(n + K ≤ 2 * N ∧
        n ∉ gmSimultaneousLambdaBadSet C N lengths)
  change |∑ n ∈ S, rowShiftBlockSum Phi T N n J K| ≤ _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    (∑ n ∈ S, |rowShiftBlockSum Phi T N n J K|) ≤
      ∑ _n ∈ S, (K - J : ℕ) * dyadicAcoefMajorant N ^ 2 *
        (2 * T * ∫ x, Phi x ^ 2) := by
      apply Finset.sum_le_sum
      intro n hnS
      exact abs_rowShiftBlockSum_le_uniform hT hN
        (Finset.mem_filter.mp hnS).1 hPhi hPhi2
    _ = (S.card : ℝ) * ((K - J : ℕ) * dyadicAcoefMajorant N ^ 2 *
        (2 * T * ∫ x, Phi x ^ 2)) := by simp
    _ ≤ ((gmSimultaneousLambdaBadSet C N lengths).card + K : ℕ) *
        ((K - J : ℕ) * dyadicAcoefMajorant N ^ 2 *
          (2 * T * ∫ x, Phi x ^ 2)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_badOrBoundaryRows_le C N K lengths
      · positivity

/-- Fully explicit arithmetic, oscillation, exceptional-set, and boundary
budget for one dyadic shift block. -/
def dyadicShiftBlockErrorBudget
    (Phi : ℝ → ℝ) (T C : ℝ) (N J K : ℕ)
    (lengths : Finset ℕ) : ℝ :=
  (∑ n ∈ goodInteriorRows C N K lengths,
    goodRowShiftBlockErrorBudget Phi T C N N n J K) +
  ((gmSimultaneousLambdaBadSet C N lengths).card + K : ℕ) *
    ((K - J : ℕ) * dyadicAcoefMajorant N ^ 2 *
      (2 * T * ∫ x, Phi x ^ 2))

/-- Complete one-block consumer with no literal complement left on the
right-hand side. -/
theorem abs_dyadicShiftBlockSum_sub_goodMain_le_explicit
    {Phi : ℝ → ℝ} {T C : ℝ} {N J K : ℕ}
    {lengths : Finset ℕ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hN : 1 ≤ N)
    (hJ : J ∈ lengths) (hK : K ∈ lengths) (hJK : J ≤ K)
    (hKN : K ≤ N)
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|) :
    |dyadicShiftBlockSum Phi T N J K -
        goodDyadicShiftBlockMain Phi T C N J K lengths| ≤
      dyadicShiftBlockErrorBudget Phi T C N J K lengths := by
  unfold dyadicShiftBlockErrorBudget
  exact (abs_dyadicShiftBlockSum_sub_goodMain_le hT hC hN hJ hK hJK
    hKN hPhi hPhi2 hPhiAbs).trans <|
      add_le_add le_rfl
        (abs_badOrBoundaryShiftBlock_le hT hN hPhi hPhi2)

end

end PrimeShell
