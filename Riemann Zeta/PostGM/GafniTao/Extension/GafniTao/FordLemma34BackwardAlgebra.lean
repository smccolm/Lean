import GafniTao.FordLemma34ScaleBounds

/-!
# Ford Lemma 3.4: algebra in the backward induction

These are the exact numerical and real-power simplifications between the
applications of Lemmas 3.2 and 3.3 and equation (3.10).
-/

namespace GafniTao

noncomputable section

/-- The integral prime exponent from Lemma 3.2 is no larger than the
half-integral exponent used in Ford's displayed real-power calculation.
Equality holds; the weak form avoids introducing a parity convention into
the consumer and is exactly the direction needed when the prime bound is at
least one. -/
theorem fordLemma34PrimeExponent_cast_le_source
    {s d r : ℕ} (hds : d ≤ s) (hdr : d < r) :
    (fordLemma34PrimeExponent s d r : ℝ) ≤
      2 * (s : ℝ) +
        ((r : ℝ) ^ 2 - r + (d : ℝ) ^ 2 - d) / 2 := by
  have hdsub : d ≤ 2 * s := hds.trans (Nat.le_mul_of_pos_left s (by omega))
  have hdr1 : d + 1 ≤ r := by omega
  have hcast1 : ((2 * s - d : ℕ) : ℝ) = 2 * (s : ℝ) - d := by
    rw [Nat.cast_sub hdsub]
    norm_num
  have hsub1 : r - d - 1 = r - (d + 1) := by omega
  have hcastRD : ((r - d : ℕ) : ℝ) = (r : ℝ) - d := by
    rw [Nat.cast_sub hdr.le]
  have hcastRD1 : ((r - d - 1 : ℕ) : ℝ) = (r : ℝ) - d - 1 := by
    rw [hsub1, Nat.cast_sub hdr1]
    push_cast
    ring
  have hdiv :
      (((r - d - 1) * (r - d) / 2 : ℕ) : ℝ) ≤
        (((r - d - 1) * (r - d) : ℕ) : ℝ) / 2 :=
    Nat.cast_div_le
  unfold fordLemma34PrimeExponent
  push_cast only [Nat.cast_add, Nat.cast_mul]
  rw [hcast1]
  calc
    2 * (s : ℝ) - d +
        (↑((r - d - 1) * (r - d) / 2) + (r : ℝ) * d) ≤
      2 * (s : ℝ) - d +
        (↑((r - d - 1) * (r - d)) / 2 + (r : ℝ) * d) := by
          gcongr
    _ = 2 * (s : ℝ) +
        ((r : ℝ) ^ 2 - r + (d : ℝ) ^ 2 - d) / 2 := by
      push_cast only [Nat.cast_mul]
      rw [hcastRD, hcastRD1]
      ring

/-- Ford's factorial estimate in the exact coefficient form occurring after
taking the square root of the Lemma-3.2 bound. -/
theorem ford_lemma_3_4_sqrt_coefficient
    {k : ℕ} (hk : 8 ≤ k) :
    (2 : ℝ) ^ k * (4 * √((k : ℝ) ^ 3 * k.factorial)) ≤
      (k : ℝ) ^ k := by
  have h := four_mul_sqrt_cube_factorial_le_two_pow_inv_mul_self_pow hk
  have htwo : 0 < (2 : ℝ) ^ k := by positivity
  rw [le_div_iff₀ htwo] at h
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- Both alternatives in the normalized maximum are absorbed by Ford's
`E_{J-1}` recurrence. -/
theorem ford_lemma_3_4_max_absorption
    {s k J : ℕ} {omega eta E : ℝ}
    (hk : 26 ≤ k) (hks : k ≤ s)
    (homega : 1 / (3 * Real.log k) ≤ omega)
    (heta : eta = 1 + omega) (hE : 1 ≤ E) :
    max ((2 : ℝ) ^ k * (k : ℝ) ^ k)
        ((2 : ℝ) ^ k *
          (4 * √((k : ℝ) ^ 3 * k.factorial)) *
            √E * eta ^ fordEStepExponent s k J) ≤
      (k : ℝ) ^ k * eta ^ fordEStepExponent s k J * √E := by
  have hetaBase := two_pow_le_ford_eta_absorption hk hks homega heta
  have heta1 : 1 ≤ eta := by
    have homega0 : 0 ≤ omega := by
      have hlog : 0 < Real.log (k : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < k by omega))
      have : 0 < 1 / (3 * Real.log (k : ℝ)) := by positivity
      linarith
    rw [heta]
    linarith
  have hJpart : 0 ≤ ((J : ℝ) ^ 2 - J) / 4 := by
    have hbase : 0 ≤ (J : ℝ) ^ 2 - J := by
      rcases J with _ | J
      · norm_num
      · push_cast
        nlinarith [show (0 : ℝ) ≤ J * (J + 1) by positivity]
    positivity
  have hstep :
      (s : ℝ) + ((k : ℝ) ^ 2 - k) / 4 ≤
        fordEStepExponent s k J := by
    unfold fordEStepExponent
    linarith
  have hetaPow : (2 : ℝ) ^ k ≤ eta ^ fordEStepExponent s k J :=
    hetaBase.trans (Real.rpow_le_rpow_of_exponent_le heta1 hstep)
  have hsqrtE : 1 ≤ √E := by
    simpa using Real.sqrt_le_sqrt hE
  apply max_le
  · calc
      (2 : ℝ) ^ k * (k : ℝ) ^ k ≤
          eta ^ fordEStepExponent s k J * (k : ℝ) ^ k := by gcongr
      _ ≤ eta ^ fordEStepExponent s k J * (k : ℝ) ^ k * √E := by
        exact le_mul_of_one_le_right (by positivity) hsqrtE
      _ = (k : ℝ) ^ k * eta ^ fordEStepExponent s k J * √E := by ring
  · have hcoef := ford_lemma_3_4_sqrt_coefficient (show 8 ≤ k by omega)
    calc
      (2 : ℝ) ^ k * (4 * √((k : ℝ) ^ 3 * k.factorial)) *
          √E * eta ^ fordEStepExponent s k J ≤
        (k : ℝ) ^ k * √E * eta ^ fordEStepExponent s k J := by
          gcongr
      _ = (k : ℝ) ^ k * eta ^ fordEStepExponent s k J * √E := by ring

/-- The real-power identity immediately following Ford's definition of the
backward `phi` schedule. -/
theorem ford_lemma_3_4_scale_cancellation
    {s k r J : ℕ} {P delta phiJ phiNext : ℝ}
    (hP : 0 < P) (hk : 0 < k) (hr : 0 < r)
    (hphi : phiJ = fordPhiStep k r J delta phiNext) :
    P ^ ((k : ℝ) / 2 - (k : ℝ) * r * phiJ) *
        (P ^ phiNext) ^
          ((s : ℝ) - fordLambda34 s k delta / 2 +
            ((r : ℝ) ^ 2 - r + (J : ℝ) ^ 2 - J) / 4) = 1 := by
  rw [← Real.rpow_mul hP.le, ← Real.rpow_add hP]
  have hcancel := ford_lemma_3_4_exponent_cancellation hk hr hphi
  have hinner := ford_lemma_3_4_inner_exponent_eq s k r J delta
  rw [hinner]
  have hexp :
      (k : ℝ) / 2 - (k : ℝ) * r * phiJ +
          (((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r +
            (J : ℝ) ^ 2 - J - 2 * delta) / 4) * phiNext = 0 := by
    linarith
  have hexp' :
      (k : ℝ) / 2 - (k : ℝ) * r * phiJ +
          phiNext * (((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r +
            (J : ℝ) ^ 2 - J - 2 * delta) / 4) = 0 := by
    nlinarith
  rw [hexp', Real.rpow_zero]

#print axioms fordLemma34PrimeExponent_cast_le_source
#print axioms ford_lemma_3_4_sqrt_coefficient
#print axioms ford_lemma_3_4_max_absorption
#print axioms ford_lemma_3_4_scale_cancellation

end

end GafniTao
