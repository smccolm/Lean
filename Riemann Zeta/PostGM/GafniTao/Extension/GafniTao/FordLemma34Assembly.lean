import GafniTao.FordLemma34E

/-!
# Ford Lemma 3.4: terminal constant and power assembly

These lemmas check the two final bookkeeping steps after equation (3.10):
absorption of the factorial and `E₀` constants, and conversion of the `M₁`
power into the updated Vinogradov exponent `Delta'`.
-/

namespace GafniTao

noncomputable section

/-- The entire numerical coefficient in the last display of Ford Lemma 3.4
is bounded by the published `k^(3k) eta^(4s+k²)`. -/
theorem ford_lemma_3_4_terminal_constant
    {k s : ℕ} {eta E0 : ℝ}
    (hk : 26 ≤ k) (heta : 1 ≤ eta)
    (hE0 : E0 ≤ (k : ℝ) ^ (2 * k) *
      eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2)) :
    (4 : ℝ) * k ^ 3 * k.factorial *
        eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2) * E0 ≤
      (k : ℝ) ^ (3 * k) * eta ^ (4 * (s : ℝ) + (k : ℝ) ^ 2) := by
  have hk11 : 11 ≤ k := by omega
  have hkR : (0 : ℝ) < k := by positivity
  have heta0 : 0 < eta := zero_lt_one.trans_le heta
  have hfac := four_mul_cube_mul_factorial_cast_le_self_pow hk11
  have hleftNonneg : 0 ≤ (4 : ℝ) * k ^ 3 * k.factorial *
      eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2) := by positivity
  calc
    (4 : ℝ) * k ^ 3 * k.factorial *
        eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2) * E0 ≤
      ((4 : ℝ) * k ^ 3 * k.factorial) *
        eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2) *
          ((k : ℝ) ^ (2 * k) *
            eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2)) := by
      exact mul_le_mul_of_nonneg_left hE0 hleftNonneg
    _ ≤ (k : ℝ) ^ k *
        eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2) *
          ((k : ℝ) ^ (2 * k) *
            eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2)) := by
      gcongr
    _ = (k : ℝ) ^ (3 * k) *
        eta ^ (4 * (s : ℝ) + (k : ℝ) ^ 2 - k + 2) := by
      rw [show (k : ℝ) ^ k *
          eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2) *
            ((k : ℝ) ^ (2 * k) *
              eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2)) =
          ((k : ℝ) ^ k * (k : ℝ) ^ (2 * k)) *
            (eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2) *
              eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 + 2)) by ring,
        ← pow_add, ← Real.rpow_add heta0]
      congr 1 <;> ring_nf
    _ ≤ (k : ℝ) ^ (3 * k) * eta ^ (4 * (s : ℝ) + (k : ℝ) ^ 2) := by
      have hexp : 4 * (s : ℝ) + (k : ℝ) ^ 2 - k + 2 ≤
          4 * (s : ℝ) + (k : ℝ) ^ 2 := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
        linarith
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le heta hexp) (by positivity)

/-- Substituting `M₁=P^phi₁` turns the terminal `P`- and `M₁`-powers into
exactly the exponent containing `Delta'`. -/
theorem ford_lemma_3_4_terminal_power
    {k s r : ℕ} {P delta phiOne : ℝ} (hP : 0 < P) :
    P ^ (fordLambda34 s k delta + k) *
        (P ^ phiOne) ^
          (((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r) / 2 - delta) =
      P ^ (2 * ((s : ℝ) + k) - ((k : ℝ) * (k + 1)) / 2 +
        fordDeltaPrime34 k r delta phiOne) := by
  rw [← Real.rpow_mul hP.le, ← Real.rpow_add hP,
    ford_lemma_3_4_final_exponent_eq]

/-- Canonical specialization of the final constant estimate to Ford's
backwards `E_J` recurrence. -/
theorem ford_lemma_3_4_canonical_terminal_constant
    {k s j : ℕ} {eta : ℝ}
    (hk : 26 ≤ k) (heta : 1 ≤ eta) (hj : 2 ≤ j) :
    (4 : ℝ) * k ^ 3 * k.factorial *
        eta ^ (2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2) *
          fordEBackwardAux s k j eta (j - 1) ≤
      (k : ℝ) ^ (3 * k) * eta ^ (4 * (s : ℝ) + (k : ℝ) ^ 2) := by
  apply ford_lemma_3_4_terminal_constant hk heta
  exact fordCanonicalE_zero_le_source_bound (by omega) heta hj

#print axioms ford_lemma_3_4_terminal_constant
#print axioms ford_lemma_3_4_terminal_power
#print axioms ford_lemma_3_4_canonical_terminal_constant

end

end GafniTao
