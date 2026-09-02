import GafniTao.FordLemma36Sequence

/-! # Ford Lemma 3.6: finite potential iteration -/

namespace GafniTao

noncomputable section

def fordPotentialLoss36 (k : ℕ) : ℝ :=
  fordBeta36 k + (2 / 5) * fordBeta36 k ^ 2

def fordReciprocalCoeff36 (k : ℕ) : ℝ :=
  fordC36 k * (1 + 8 / (5 * (k : ℝ)))

theorem fordPotential36_sequence_step
    {k n : ℕ} (hk : 1000 ≤ k)
    (habove : ∀ m, m ≤ n → (k : ℝ) < fordDeltaSequence36 k m) :
    fordPotential36 (fordDSequence36 k (n + 1)) ≤
      fordPotential36 (fordDSequence36 k n) - fordPotentialLoss36 k +
        fordReciprocalCoeff36 k / fordDSequence36 k n := by
  have hbounds := fordDSequence36_bounds_of_above hk
    (n := n) (fun m hm => habove m hm.le)
  have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hdeltaUpper :
      fordDeltaSequence36 k n ≤ ((k : ℝ) ^ 2 - k) / 2 := by
    have hnorm := hbounds.2
    unfold fordDSequence36 at hnorm
    rw [fordDeltaSequence36_zero, fordDeltaInitial35] at hnorm
    exact (div_le_div_iff_of_pos_right hkSq).mp hnorm
  have hstep := fordPotential36_actual_step hk (habove n le_rfl) hdeltaUpper
  have hbeta := (fordBeta36_bounds hk).2
  have hkR : (0 : ℝ) < k := by positivity
  have hcoeff : 1 + (4 / 5) * fordBeta36 k ≤
      1 + 8 / (5 * (k : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hbeta (by norm_num : (0 : ℝ) ≤ 4 / 5)
    calc
      1 + (4 / 5) * fordBeta36 k ≤ 1 + (4 / 5) * (2 / (k : ℝ)) := by linarith
      _ = 1 + 8 / (5 * (k : ℝ)) := by field_simp; ring
  have hcdiv0 : 0 ≤ fordC36 k / fordDSequence36 k n := by
    apply div_nonneg
    · unfold fordC36
      positivity
    · exact hbounds.1.le
  have herror :
      fordC36 k * (1 + (4 / 5) * fordBeta36 k) /
          fordDSequence36 k n ≤
        fordReciprocalCoeff36 k / fordDSequence36 k n := by
    calc
      fordC36 k * (1 + (4 / 5) * fordBeta36 k) /
          fordDSequence36 k n =
        (fordC36 k / fordDSequence36 k n) *
          (1 + (4 / 5) * fordBeta36 k) := by ring
      _ ≤ (fordC36 k / fordDSequence36 k n) *
          (1 + 8 / (5 * (k : ℝ))) :=
        mul_le_mul_of_nonneg_left hcoeff hcdiv0
      _ = fordReciprocalCoeff36 k / fordDSequence36 k n := by
        unfold fordReciprocalCoeff36
        ring
  have hstep' : fordPotential36 (fordDSequence36 k (n + 1)) ≤
      fordPotential36 (fordDSequence36 k n) - fordBeta36 k -
        (2 / 5) * fordBeta36 k ^ 2 +
          fordC36 k * (1 + (4 / 5) * fordBeta36 k) /
            fordDSequence36 k n := by
    simpa [fordDSequence36, fordRSequence36] using hstep
  calc
    fordPotential36 (fordDSequence36 k (n + 1)) ≤
        fordPotential36 (fordDSequence36 k n) - fordBeta36 k -
          (2 / 5) * fordBeta36 k ^ 2 +
            fordC36 k * (1 + (4 / 5) * fordBeta36 k) /
              fordDSequence36 k n := hstep'
    _ ≤ fordPotential36 (fordDSequence36 k n) - fordBeta36 k -
          (2 / 5) * fordBeta36 k ^ 2 +
            fordReciprocalCoeff36 k / fordDSequence36 k n := by linarith
    _ = fordPotential36 (fordDSequence36 k n) - fordPotentialLoss36 k +
          fordReciprocalCoeff36 k / fordDSequence36 k n := by
            unfold fordPotentialLoss36
            ring

theorem fordPotential36_iterated
    {k n : ℕ} (hk : 1000 ≤ k)
    (habove : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m) :
    fordPotential36 (fordDSequence36 k n) ≤
      fordPotential36 (fordDSequence36 k 0) -
        (n : ℝ) * fordPotentialLoss36 k +
          fordReciprocalCoeff36 k *
            ∑ m ∈ Finset.range n, 1 / fordDSequence36 k m := by
  induction n with
  | zero => simp
  | succ n ih =>
      have habovePrev : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m := by
        intro m hm
        exact habove m (by omega)
      have hih := ih habovePrev
      have hstep := fordPotential36_sequence_step hk
        (n := n) (fun m hm => habove m (by omega))
      calc
        fordPotential36 (fordDSequence36 k (n + 1)) ≤
            fordPotential36 (fordDSequence36 k n) - fordPotentialLoss36 k +
              fordReciprocalCoeff36 k / fordDSequence36 k n := hstep
        _ ≤ (fordPotential36 (fordDSequence36 k 0) -
              (n : ℝ) * fordPotentialLoss36 k +
                fordReciprocalCoeff36 k *
                  ∑ m ∈ Finset.range n, 1 / fordDSequence36 k m) -
              fordPotentialLoss36 k +
                fordReciprocalCoeff36 k / fordDSequence36 k n := by
                  gcongr
        _ = fordPotential36 (fordDSequence36 k 0) -
              ((n + 1 : ℕ) : ℝ) * fordPotentialLoss36 k +
                fordReciprocalCoeff36 k *
                  ∑ m ∈ Finset.range (n + 1), 1 / fordDSequence36 k m := by
          rw [Finset.sum_range_succ]
          push_cast
          ring

#print axioms fordPotential36_sequence_step
#print axioms fordPotential36_iterated

end

end GafniTao
