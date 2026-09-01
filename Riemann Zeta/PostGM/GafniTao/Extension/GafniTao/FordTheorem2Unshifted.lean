import GafniTao.FordLemma73Coefficient

/-!
# The unshifted endpoint of Ford's Theorem 2

Ford states Theorem 2 as a maximum over `0 < u <= 1`, but applies it to the
ordinary zeta sum.  The latter is the `u -> 0+` limit.  This file proves that
closed-endpoint bridge for the exact finite sums.
-/

open Complex Finset Filter Topology

namespace GafniTao

noncomputable section

theorem continuousAt_fordShiftedLogPhase_zero
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ContinuousAt (fun u : ℝ => fordShiftedLogPhase n u t) 0 := by
  unfold fordShiftedLogPhase
  have hlog : ContinuousAt (fun u : ℝ => Real.log ((n : ℝ) + u)) 0 := by
    fun_prop (disch := positivity)
  fun_prop

theorem continuousAt_fordShiftedExponentialSum_zero
    {N R : ℕ} (hN : 0 < N) (t : ℝ) :
    ContinuousAt (fun u : ℝ => fordShiftedExponentialSum N R u t) 0 := by
  unfold fordShiftedExponentialSum
  have hsum : ∀ s : Finset ℕ,
      (∀ n ∈ s, 0 < n) →
      ContinuousAt (fun u : ℝ => ∑ n ∈ s, fordShiftedLogPhase n u t) 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _h
        simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℂ)) 0)
    | @insert n s hn ih =>
        intro hpos
        simpa [Finset.sum_insert, hn] using
          (continuousAt_fordShiftedLogPhase_zero (hpos n (by simp)) t).add
            (ih fun m hm => hpos m (by simp [hm]))
  exact hsum (Finset.Ioc N R) fun n hn => by
    have hnN := (Finset.mem_Ioc.mp hn).1
    omega

/-- The source-open shift interval controls its `u = 0` endpoint by finite
continuity. -/
theorem fordTheorem2_unshifted
    (hFord : FordTheorem2) {N R : ℕ} {t : ℝ}
    (hN : 0 < N) (hNt : (N : ℝ) ≤ t)
    (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedExponentialSum N R 0 t‖ ≤
      9.463 * (N : ℝ) ^
        (1 - 1 / (133.66 * fordLambda N t ^ 2)) := by
  let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have huLim : Tendsto u atTop (𝓝 0) := by
    simpa [u, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsumLim : Tendsto
      (fun k => fordShiftedExponentialSum N R (u k) t) atTop
      (𝓝 (fordShiftedExponentialSum N R 0 t)) :=
    (continuousAt_fordShiftedExponentialSum_zero hN t).tendsto.comp huLim
  apply le_of_tendsto hsumLim.norm
  exact Filter.Eventually.of_forall fun k => by
    apply hFord hN hNt
    · dsimp [u]
      positivity
    · dsimp [u]
      rw [div_le_one (by positivity)]
      norm_num
    · exact hNR
    · exact hR

#print axioms continuousAt_fordShiftedExponentialSum_zero
#print axioms fordTheorem2_unshifted

end

end GafniTao
