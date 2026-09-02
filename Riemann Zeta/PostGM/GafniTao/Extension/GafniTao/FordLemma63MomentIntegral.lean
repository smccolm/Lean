import GafniTao.FordLemma63IntegratedMoment

/-!
# Ford Lemma 6.3: evaluation of the integrated majorant
-/

open Finset Set MeasureTheory
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordLemma63PolynomialSum_unitCube_moment
    (s k Q : ℕ) :
    (∫ β : Fin k → ℝ in fordUnitCube k,
      ‖fordLemma63PolynomialSum k Q β‖ ^ (2 * s)) =
        (fordVinogradovMomentNat s k Q : ℝ) := by
  simpa only [fordUnitCube] using
    fordLemma63PolynomialSum_unitCube_mean_eq s k Q

theorem fordLemma63_integral_prefix_sum_eq
    (s k M : ℕ) :
    (∫ β : Fin k → ℝ in fordUnitCube k,
      ∑ q ∈ Finset.range (M - 1),
        ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ (2 * s)) =
      ∑ q ∈ Finset.range (M - 1),
        (fordVinogradovMomentNat s k (q + 1) : ℝ) := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    exact fordLemma63PolynomialSum_unitCube_moment s k (q + 1)
  · intro q hq
    exact integrableOn_fordLemma63PolynomialSum_norm_pow k (q + 1) (2 * s)

theorem fordLemma63_integral_sharp_rhs_eq
    (s k M : ℕ) :
    (∫ β : Fin k → ℝ in fordUnitCube k,
      (2 : ℝ) ^ (2 * s - 1) *
        (‖fordLemma63PolynomialSum k M β‖ ^ (2 * s) +
          (2 : ℝ) ^ (2 * s) * (1 / (M : ℝ)) *
            ∑ q ∈ Finset.range (M - 1),
              ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ (2 * s))) =
      (2 : ℝ) ^ (2 * s - 1) *
        ((fordVinogradovMomentNat s k M : ℝ) +
          (2 : ℝ) ^ (2 * s) * (1 / (M : ℝ)) *
            ∑ q ∈ Finset.range (M - 1),
              (fordVinogradovMomentNat s k (q + 1) : ℝ)) := by
  rw [integral_const_mul]
  rw [integral_add]
  · rw [fordLemma63PolynomialSum_unitCube_moment]
    rw [integral_const_mul]
    rw [fordLemma63_integral_prefix_sum_eq]
  · exact integrableOn_fordLemma63PolynomialSum_norm_pow k M (2 * s)
  · exact (integrable_finsetSum (Finset.range (M - 1)) (fun q hq =>
        integrableOn_fordLemma63PolynomialSum_norm_pow k (q + 1) (2 * s))).const_mul _

/-- The integrated `S₀` estimate in Ford's proof of Lemma 6.3. -/
theorem fordLemma63_integral_SZero_two_s_le
    {s k M : ℕ} (hs : 1 ≤ s) (hM : 1 ≤ M) :
    (∫ β : Fin k → ℝ in fordUnitCube k,
      fordLemma63SZero k M β ^ (2 * s)) ≤
        (2 : ℝ) ^ (4 * s) * (fordVinogradovMomentNat s k M : ℝ) := by
  let J : ℝ := fordVinogradovMomentNat s k M
  let B : ℝ := (2 : ℝ) ^ (2 * s)
  let c : ℝ := (2 : ℝ) ^ (2 * s - 1)
  have hrs : 1 ≤ 2 * s := by omega
  have hmono := fordLemma63_integral_SZero_power_le_sharp
    (k := k) (M := M) (r := 2 * s) hM hrs
  rw [fordLemma63_integral_sharp_rhs_eq] at hmono
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum :
      (∑ q ∈ Finset.range (M - 1),
        (fordVinogradovMomentNat s k (q + 1) : ℝ)) ≤ (M : ℝ) * J := by
    calc
      _ ≤ ∑ _q ∈ Finset.range (M - 1), J := by
        apply Finset.sum_le_sum
        intro q hq
        dsimp [J]
        exact_mod_cast (fordVinogradovMomentNat_mono s k
          (show q + 1 ≤ M by simp only [Finset.mem_range] at hq; omega))
      _ = ((M - 1 : ℕ) : ℝ) * J := by
        rw [Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul]
      _ ≤ (M : ℝ) * J := by
        gcongr
        exact_mod_cast Nat.sub_le M 1
  have havg :
      (1 / (M : ℝ)) *
          (∑ q ∈ Finset.range (M - 1),
            (fordVinogradovMomentNat s k (q + 1) : ℝ)) ≤ J := by
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hMpos]
    simpa only [mul_comm] using hsum
  have hB : 1 ≤ B := by
    dsimp [B]
    exact one_le_pow₀ (by norm_num)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hconst : c * (1 + B) ≤ (2 : ℝ) ^ (4 * s) := by
    calc
      c * (1 + B) ≤ c * (2 * B) := by
        gcongr
        linarith
      _ = (2 : ℝ) ^ (4 * s) := by
        dsimp [c, B]
        have hinner : (2 : ℝ) * 2 ^ (2 * s) = 2 ^ (2 * s + 1) := by
          rw [pow_succ]
          ring
        rw [hinner, ← pow_add]
        congr 1
        omega
  calc
    (∫ β : Fin k → ℝ in fordUnitCube k,
      fordLemma63SZero k M β ^ (2 * s)) ≤
        c * (J + B * (1 / (M : ℝ)) *
          ∑ q ∈ Finset.range (M - 1),
            (fordVinogradovMomentNat s k (q + 1) : ℝ)) := by
      simpa only [c, J, B, mul_assoc] using hmono
    _ ≤ c * (J + B * J) := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply add_le_add_right
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left havg (zero_le_one.trans hB))
    _ = (c * (1 + B)) * J := by ring
    _ ≤ (2 : ℝ) ^ (4 * s) * J :=
      mul_le_mul_of_nonneg_right hconst hJ
    _ = _ := rfl

#print axioms fordLemma63PolynomialSum_unitCube_moment
#print axioms fordLemma63_integral_prefix_sum_eq
#print axioms fordLemma63_integral_sharp_rhs_eq
#print axioms fordLemma63_integral_SZero_two_s_le

end

end GafniTao
