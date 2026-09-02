import GafniTao.FordLemma34Eta

/-!
# Ford Lemma 3.4: the `E_J` iteration

This file formalizes the exact backwards recurrence in equation (3.10) and
the infinite-geometric majorant used by Ford to bound `E₀`.  The majorant is
encoded as a decreasing induction, so no convergence assertion or suppressed
tail is needed in the finite Lean proof.
-/

namespace GafniTao

noncomputable section

/-- The exponent of `eta` in the `J`-th backwards step of Ford's `E_J`
recurrence. -/
def fordEStepExponent (s k J : ℕ) : ℝ :=
  (s : ℝ) + ((k : ℝ) ^ 2 - k + (J : ℝ) ^ 2 - J) / 4

/-- The exact finite `E_J` recurrence from Ford equation (3.10).  Positivity
is recorded because it is an immediate property of the canonical backwards
construction and is needed to take logarithms. -/
structure FordESchedule (s k j : ℕ) (eta : ℝ) where
  E : ℕ → ℝ
  terminal : E (j - 1) = 1
  recurrence : ∀ J, 1 ≤ J → J < j →
    E (J - 1) =
      (k : ℝ) ^ k * eta ^ fordEStepExponent s k J * √(E J)
  positive : ∀ J, J < j → 0 < E J

/-- Backwards recursion, indexed by distance from `j-1`. -/
def fordEBackwardAux (s k j : ℕ) (eta : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      (k : ℝ) ^ k * eta ^ fordEStepExponent s k (j - 1 - n) *
        √(fordEBackwardAux s k j eta n)

theorem fordEBackwardAux_pos
    {s k j : ℕ} {eta : ℝ} (hk : 1 ≤ k) (heta : 1 ≤ eta) :
    ∀ n, 0 < fordEBackwardAux s k j eta n := by
  intro n
  induction n with
  | zero => simp [fordEBackwardAux]
  | succ n ih =>
      simp only [fordEBackwardAux]
      have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have heta0 : 0 < eta := zero_lt_one.trans_le heta
      exact mul_pos
        (mul_pos (pow_pos hkR _) (Real.rpow_pos_of_pos heta0 _))
        (Real.sqrt_pos.2 ih)

/-- The canonical finite schedule obtained by running Ford's recurrence
backwards from `E_{j-1}=1`. -/
def fordCanonicalESchedule
    (s k j : ℕ) (eta : ℝ) (hk : 1 ≤ k) (heta : 1 ≤ eta) :
    FordESchedule s k j eta where
  E J := fordEBackwardAux s k j eta (j - 1 - J)
  terminal := by simp [fordEBackwardAux]
  recurrence J hJ hJj := by
    have hsub : j - 1 - (J - 1) = (j - 1 - J) + 1 := by omega
    have hindex : j - 1 - (j - 1 - J) = J := by omega
    simp only [hsub, fordEBackwardAux, hindex]
  positive J _ := fordEBackwardAux_pos hk heta _

theorem fordCanonicalESchedule_apply
    {s k j : ℕ} {eta : ℝ} (hk : 1 ≤ k) (heta : 1 ≤ eta) (J : ℕ) :
    (fordCanonicalESchedule s k j eta hk heta).E J =
      fordEBackwardAux s k j eta (j - 1 - J) := rfl

/-- Ford's geometric-series upper envelope for `log E_J`.  At `J=0` its
`eta` coefficient is exactly `2s + (k²-k)/2 + 2`. -/
def fordELogMajorant (s k J : ℕ) (eta : ℝ) : ℝ :=
  2 * (k : ℝ) * Real.log k +
    (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 +
      ((J : ℝ) ^ 2 + 3 * J) / 2 + 2) * Real.log eta

theorem fordELogMajorant_step
    {s k J : ℕ} {eta : ℝ} (hJ : 1 ≤ J) :
    fordELogMajorant s k (J - 1) eta =
      (k : ℝ) * Real.log k +
        fordEStepExponent s k J * Real.log eta +
          fordELogMajorant s k J eta / 2 := by
  unfold fordELogMajorant fordEStepExponent
  norm_num only [Nat.cast_sub hJ, Nat.cast_one]
  ring

theorem FordESchedule.log_recurrence
    {s k j : ℕ} {eta : ℝ} (Esch : FordESchedule s k j eta)
    (hk : 1 ≤ k) (heta : 1 ≤ eta)
    {J : ℕ} (hJ : 1 ≤ J) (hJj : J < j) :
    Real.log (Esch.E (J - 1)) =
      (k : ℝ) * Real.log k +
        fordEStepExponent s k J * Real.log eta +
          Real.log (Esch.E J) / 2 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have heta0 : 0 < eta := zero_lt_one.trans_le heta
  have hE : 0 < Esch.E J := Esch.positive J hJj
  have hetaPow : eta ^ fordEStepExponent s k J ≠ 0 :=
    (Real.rpow_pos_of_pos heta0 _).ne'
  rw [Esch.recurrence J hJ hJj]
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ hkR.ne')
      hetaPow) (Real.sqrt_ne_zero'.2 hE),
    Real.log_mul (pow_ne_zero _ hkR.ne') hetaPow,
    Real.log_pow, Real.log_rpow heta0, Real.log_sqrt hE.le]

/-- The finite recurrence is bounded by Ford's infinite geometric envelope.
This is the rigorous form of the displayed infinite-product estimate in the
proof of Lemma 3.4. -/
theorem FordESchedule.log_le_majorant
    {s k j : ℕ} {eta : ℝ} (Esch : FordESchedule s k j eta)
    (hk : 1 ≤ k) (heta : 1 ≤ eta) (hj : 2 ≤ j)
    {J : ℕ} (hJ : J ≤ j - 1) :
    Real.log (Esch.E J) ≤ fordELogMajorant s k J eta := by
  have hlogk : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk)
  have hlogeta : 0 ≤ Real.log eta := Real.log_nonneg heta
  refine Nat.decreasingInduction (motive := fun J _ =>
    Real.log (Esch.E J) ≤ fordELogMajorant s k J eta) ?_ ?_ hJ
  · intro J hJlt ih
    have hJ1 : 1 ≤ J + 1 := by omega
    have hJj : J + 1 < j := by omega
    rw [show J = (J + 1) - 1 by omega,
      Esch.log_recurrence hk heta hJ1 hJj,
      fordELogMajorant_step (s := s) (k := k) (eta := eta) hJ1]
    linarith
  · change Real.log (Esch.E (j - 1)) ≤ fordELogMajorant s k (j - 1) eta
    rw [Esch.terminal, Real.log_one]
    unfold fordELogMajorant
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkdiff : 0 ≤ (k : ℝ) ^ 2 - k := by nlinarith
    have hJnonneg : 0 ≤ ((j - 1 : ℕ) : ℝ) ^ 2 + 3 * (j - 1 : ℕ) := by
      positivity
    have hcoef : 0 ≤ 2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 +
        (((j - 1 : ℕ) : ℝ) ^ 2 + 3 * (j - 1 : ℕ)) / 2 + 2 := by
      positivity
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hlogk)
      (mul_nonneg hcoef hlogeta)

theorem fordELogMajorant_zero
    (s k : ℕ) (eta : ℝ) :
    fordELogMajorant s k 0 eta =
      2 * (k : ℝ) * Real.log k +
        (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2) * Real.log eta := by
  unfold fordELogMajorant
  norm_num

/-- The exact `E₀` estimate asserted after equation (3.10). -/
theorem FordESchedule.zero_le_source_bound
    {s k j : ℕ} {eta : ℝ} (Esch : FordESchedule s k j eta)
    (hk : 1 ≤ k) (heta : 1 ≤ eta) (hj : 2 ≤ j) :
    Esch.E 0 ≤
      (k : ℝ) ^ (2 * k) *
        eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2) := by
  have hE0 : 0 < Esch.E 0 := Esch.positive 0 (by omega)
  have hlog : Real.log (Esch.E 0) ≤
      2 * (k : ℝ) * Real.log k +
        (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2) * Real.log eta := by
    calc
      Real.log (Esch.E 0) ≤ fordELogMajorant s k 0 eta :=
      Esch.log_le_majorant hk heta hj (by omega)
      _ = 2 * (k : ℝ) * Real.log k +
        (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2) * Real.log eta :=
      fordELogMajorant_zero s k eta
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have heta0 : 0 < eta := zero_lt_one.trans_le heta
  have hRhsPos : 0 < (k : ℝ) ^ (2 * k) *
      eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2) := by
    positivity
  have hlogRhs : Real.log ((k : ℝ) ^ (2 * k) *
        eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2)) =
      2 * (k : ℝ) * Real.log k +
        (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2) * Real.log eta := by
    rw [Real.log_mul (pow_ne_zero _ hkR.ne')
      (Real.rpow_pos_of_pos heta0 _).ne', Real.log_pow,
      Real.log_rpow heta0]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    Esch.E 0 ≤ Real.exp (2 * (k : ℝ) * Real.log k +
        (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2) * Real.log eta) :=
      (Real.log_le_iff_le_exp hE0).mp hlog
    _ = Real.exp (Real.log ((k : ℝ) ^ (2 * k) *
        eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2))) := by
      rw [hlogRhs]
    _ = (k : ℝ) ^ (2 * k) *
        eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2) :=
      Real.exp_log hRhsPos

/-- The source `E₀` estimate for the canonical recurrence, with no schedule
hypothesis remaining. -/
theorem fordCanonicalE_zero_le_source_bound
    {s k j : ℕ} {eta : ℝ}
    (hk : 1 ≤ k) (heta : 1 ≤ eta) (hj : 2 ≤ j) :
    fordEBackwardAux s k j eta (j - 1) ≤
      (k : ℝ) ^ (2 * k) *
        eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2) := by
  simpa [fordCanonicalESchedule_apply] using
    (fordCanonicalESchedule s k j eta hk heta).zero_le_source_bound hk heta hj

#print axioms fordELogMajorant_step
#print axioms fordEBackwardAux_pos
#print axioms fordCanonicalESchedule_apply
#print axioms FordESchedule.log_recurrence
#print axioms FordESchedule.log_le_majorant
#print axioms fordELogMajorant_zero
#print axioms FordESchedule.zero_le_source_bound
#print axioms fordCanonicalE_zero_le_source_bound

end

end GafniTao
