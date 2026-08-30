import PrimeShell.GlobalBlock

namespace PrimeShell

noncomputable section

open scoped BigOperators

/-- Left endpoint of the `i`-th uniform shift block. -/
def shiftGridLeft (L W i : ℕ) : ℕ := L + i * W

/-- Right endpoint of the `i`-th uniform shift block. -/
def shiftGridRight (L W i : ℕ) : ℕ := L + (i + 1) * W

/-- Every endpoint length needed for simultaneous fixed-length GM control. -/
def shiftGridLengths (L W q : ℕ) : Finset ℕ :=
  (Finset.range q).biUnion fun i =>
    {shiftGridLeft L W i, shiftGridRight L W i}

theorem shiftGridLeft_mem_lengths
    {L W q i : ℕ} (hi : i < q) :
    shiftGridLeft L W i ∈ shiftGridLengths L W q := by
  unfold shiftGridLengths
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
  simp

theorem shiftGridRight_mem_lengths
    {L W q i : ℕ} (hi : i < q) :
    shiftGridRight L W i ∈ shiftGridLengths L W q := by
  unfold shiftGridLengths
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
  simp

theorem shiftGridLeft_le_right (L W i : ℕ) :
    shiftGridLeft L W i ≤ shiftGridRight L W i := by
  unfold shiftGridLeft shiftGridRight
  exact Nat.add_le_add_left (Nat.mul_le_mul_right W (Nat.le_succ i)) L

/-- Exact partition of `(L,L+qW]` into `q` adjacent blocks.  The theorem is
purely finite and therefore keeps every endpoint correction visible. -/
theorem sum_Ioc_eq_sum_shiftGrid
    {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (L W q : ℕ) :
    (∑ h ∈ Finset.Ioc L (L + q * W), f h) =
      ∑ i ∈ Finset.range q,
        ∑ h ∈ Finset.Ioc (shiftGridLeft L W i)
          (shiftGridRight L W i), f h := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hLmid : L ≤ L + q * W := by omega
      have hmidRight : L + q * W ≤ L + (q + 1) * W :=
        Nat.add_le_add_left (Nat.mul_le_mul_right W (Nat.le_succ q)) L
      rw [← Finset.Ioc_union_Ioc_eq_Ioc hLmid hmidRight]
      rw [Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (b := L + q * W)
        (c := L + q * W) le_rfl)]
      rw [ih, Finset.sum_range_succ]
      unfold shiftGridLeft shiftGridRight
      simp only [Nat.add_mul, one_mul]

/-- The literal dyadic trace on a uniform shift grid is the sum of the
literal block traces. -/
theorem dyadicShiftGridSum_eq
    (Phi : ℝ → ℝ) (T : ℝ) (N L W q : ℕ) :
    (∑ h ∈ Finset.Ioc L (L + q * W),
      ∑ n ∈ Finset.Ioc N (2 * N),
        if n + h ∈ Finset.Ioc N (2 * N) then
          dyadicLambdaWeight n h * dyadicShiftKernel Phi T n h else 0) =
      ∑ i ∈ Finset.range q,
        dyadicShiftBlockSum Phi T N
          (shiftGridLeft L W i) (shiftGridRight L W i) := by
  rw [sum_Ioc_eq_sum_shiftGrid]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dyadicShiftBlockSum_eq_double_sum]

/-- The simultaneous endpoint family has at most two entries per block. -/
theorem card_shiftGridLengths_le (L W q : ℕ) :
    (shiftGridLengths L W q).card ≤ 2 * q := by
  unfold shiftGridLengths
  calc
    ((Finset.range q).biUnion fun i =>
        {shiftGridLeft L W i, shiftGridRight L W i}).card ≤
      ∑ _i ∈ Finset.range q,
        ({shiftGridLeft L W _i, shiftGridRight L W _i} : Finset ℕ).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range q, 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.card_le_two
    _ = 2 * q := by simp; ring

/-- Every grid endpoint lies between the initial and final lengths. -/
theorem shiftGridLengths_mem_bounds
    {L W q H : ℕ} (hH : H ∈ shiftGridLengths L W q) :
    L ≤ H ∧ H ≤ L + q * W := by
  unfold shiftGridLengths at hH
  obtain ⟨i, hi, hendpoint⟩ := Finset.mem_biUnion.mp hH
  have hiq := Finset.mem_range.mp hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hendpoint
  rcases hendpoint with rfl | rfl
  · unfold shiftGridLeft
    exact ⟨Nat.le_add_right _ _, Nat.add_le_add_left
      (Nat.mul_le_mul_right W (Nat.le_of_lt hiq)) L⟩
  · unfold shiftGridRight
    exact ⟨Nat.le_add_right _ _, Nat.add_le_add_left
      (Nat.mul_le_mul_right W (Nat.succ_le_iff.mpr hiq)) L⟩

/-- Anchored arithmetic main term summed over every block of the grid. -/
def goodDyadicShiftGridMain
    (Phi : ℝ → ℝ) (T C : ℝ) (N L W q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range q,
    goodDyadicShiftBlockMain Phi T C N
      (shiftGridLeft L W i) (shiftGridRight L W i)
      (shiftGridLengths L W q)

/-- Complete explicit error ledger for the uniform shift grid. -/
def dyadicShiftGridErrorBudget
    (Phi : ℝ → ℝ) (T C : ℝ) (N L W q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range q,
    dyadicShiftBlockErrorBudget Phi T C N
      (shiftGridLeft L W i) (shiftGridRight L W i)
      (shiftGridLengths L W q)

/-- Complete finite uniform-grid consumer for the literal two-variable
kernel.  The only arithmetic data it uses are the fixed-length bad sets at
the explicitly enumerated grid endpoints. -/
theorem abs_dyadicShiftGridSum_sub_goodMain_le
    {Phi : ℝ → ℝ} {T C : ℝ} {N L W q : ℕ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hN : 1 ≤ N)
    (hFinal : L + q * W ≤ N)
    (hPhi : Continuous Phi)
    (hPhi2 : MeasureTheory.Integrable fun x => Phi x ^ 2)
    (hPhiAbs : MeasureTheory.Integrable fun x => Phi x ^ 2 * |x|) :
    |(∑ h ∈ Finset.Ioc L (L + q * W),
        ∑ n ∈ Finset.Ioc N (2 * N),
          if n + h ∈ Finset.Ioc N (2 * N) then
            dyadicLambdaWeight n h * dyadicShiftKernel Phi T n h else 0) -
      goodDyadicShiftGridMain Phi T C N L W q| ≤
        dyadicShiftGridErrorBudget Phi T C N L W q := by
  rw [dyadicShiftGridSum_eq]
  unfold goodDyadicShiftGridMain dyadicShiftGridErrorBudget
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  have hiq := Finset.mem_range.mp hi
  apply abs_dyadicShiftBlockSum_sub_goodMain_le_explicit
  · exact hT
  · exact hC
  · exact hN
  · exact shiftGridLeft_mem_lengths hiq
  · exact shiftGridRight_mem_lengths hiq
  · exact shiftGridLeft_le_right L W i
  · exact (shiftGridLengths_mem_bounds
      (shiftGridRight_mem_lengths hiq)).2.trans hFinal
  · exact hPhi
  · exact hPhi2
  · exact hPhiAbs

end

end PrimeShell
