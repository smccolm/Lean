import GafniTao.FordLemma36Equation321
import GafniTao.FordExpCertificate

/-!
# Ford Lemma 3.6: the lower iterate used in equation (3.20)

Lean index `i` represents Ford's source exponent `Delta_(i+1)`.  This file
keeps that offset explicit and proves the numerical lower bound
`delta_(n-1) >= 0.0096476` on the complete range used in (3.20).
-/

namespace GafniTao

noncomputable section

theorem fordDSequence36_ge_geometric
    {k i : ℕ} (hk : 1000 ≤ k)
    (habove : ∀ m, m < i → (k : ℝ) < fordDeltaSequence36 k m) :
    fordDSequence36 k 0 * (1 - 2 / (k : ℝ)) ^ i ≤
      fordDSequence36 k i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have habovePrev : ∀ m, m < i →
          (k : ℝ) < fordDeltaSequence36 k m := by
        intro m hm
        exact habove m (by omega)
      have hstep := fordDSequence36_lower_step hk
        (n := i) (fun m hm => habove m (by omega))
      have hq : 0 ≤ 1 - 2 / (k : ℝ) := by
        have hkR : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
        exact sub_nonneg.mpr ((div_le_one (by positivity : (0 : ℝ) < k)).2 hkR)
      calc
        fordDSequence36 k 0 * (1 - 2 / (k : ℝ)) ^ (i + 1) =
            (fordDSequence36 k 0 * (1 - 2 / (k : ℝ)) ^ i) *
              (1 - 2 / (k : ℝ)) := by rw [pow_succ]; ring_nf
        _ ≤ fordDSequence36 k i * (1 - 2 / (k : ℝ)) :=
          mul_le_mul_of_nonneg_right (ih habovePrev) hq
        _ ≤ fordDSequence36 k (i + 1) := hstep

theorem fordDSequence36_ge_half_geometric
    {k i : ℕ} (hk : 1000 ≤ k)
    (habove : ∀ m, m < i → (k : ℝ) < fordDeltaSequence36 k m) :
    (1 / 2 : ℝ) * (1 - 2 / (k : ℝ)) ^ (i + 1) ≤
      fordDSequence36 k i := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hq : 0 ≤ 1 - 2 / (k : ℝ) := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    exact sub_nonneg.mpr ((div_le_one hk0).2 hkR)
  have hinitial : (1 / 2 : ℝ) * (1 - 2 / (k : ℝ)) ≤
      fordDSequence36 k 0 := by
    rw [fordDSequence36_zero]
    field_simp
    linarith
  calc
    (1 / 2 : ℝ) * (1 - 2 / (k : ℝ)) ^ (i + 1) =
        ((1 / 2 : ℝ) * (1 - 2 / (k : ℝ))) *
          (1 - 2 / (k : ℝ)) ^ i := by rw [pow_succ]; ring_nf
    _ ≤ fordDSequence36 k 0 * (1 - 2 / (k : ℝ)) ^ i :=
      mul_le_mul_of_nonneg_right hinitial (pow_nonneg hq i)
    _ ≤ fordDSequence36 k i := fordDSequence36_ge_geometric hk habove

theorem ford_one_sub_two_div_pow_ge_exp
    {k j : ℕ} (hk : 1000 ≤ k) :
    Real.exp (-(2 * (j : ℝ) / ((k : ℝ) - 2))) ≤
      (1 - 2 / (k : ℝ)) ^ j := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hk2 : (2 : ℝ) < k := by exact_mod_cast (show 2 < k by omega)
  have hq : 0 < 1 - 2 / (k : ℝ) := by
    exact sub_pos.mpr ((div_lt_one hk0).2 hk2)
  have hlog0 := Real.one_sub_inv_le_log_of_pos hq
  have hlog : -(2 / ((k : ℝ) - 2)) ≤
      Real.log (1 - 2 / (k : ℝ)) := by
    have hden : (k : ℝ) - 2 ≠ 0 := ne_of_gt (sub_pos.mpr hk2)
    convert hlog0 using 1
    field_simp [hk0.ne', hden]
    ring_nf
  have hscaled := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (j : ℝ) by positivity)
  have hexp := Real.exp_le_exp.mpr hscaled
  calc
    Real.exp (-(2 * (j : ℝ) / ((k : ℝ) - 2))) =
        Real.exp ((j : ℝ) * (-(2 / ((k : ℝ) - 2)))) := by ring_nf
    _ ≤ Real.exp ((j : ℝ) * Real.log (1 - 2 / (k : ℝ))) := hexp
    _ = (1 - 2 / (k : ℝ)) ^ j := by
      rw [Real.exp_nat_mul, Real.exp_log hq]

theorem ford_exp_1970_div_499_upper :
    Real.exp (1970 / 499 : ℝ) ≤ 1250000 / 24119 := by
  have hbase := real_exp_le_fordExpTaylorUpper
    (n := 20) (x := (1970 / (499 * 4) : ℝ)) (by norm_num) (by norm_num [abs_of_nonneg])
  have hpow := pow_le_pow_left₀ (Real.exp_pos (1970 / (499 * 4) : ℝ)).le
    hbase 4
  calc
    Real.exp (1970 / 499 : ℝ) =
        Real.exp ((4 : ℝ) * (1970 / (499 * 4) : ℝ)) := by norm_num
    _ = Real.exp (1970 / (499 * 4) : ℝ) ^ 4 :=
      Real.exp_nat_mul (1970 / (499 * 4) : ℝ) 4
    _ ≤ fordExpTaylorUpper 20 (1970 / (499 * 4) : ℝ) ^ 4 := hpow
    _ ≤ 1250000 / 24119 := by norm_num [fordExpTaylorUpper]

theorem ford_half_exp_neg_1970_div_499_lower :
    (24119 / 2500000 : ℝ) ≤
      (1 / 2 : ℝ) * Real.exp (-(1970 / 499 : ℝ)) := by
  have hpos : 0 < Real.exp (1970 / 499 : ℝ) := Real.exp_pos _
  have hupper := ford_exp_1970_div_499_upper
  have hinv : (24119 / 1250000 : ℝ) ≤
      (Real.exp (1970 / 499 : ℝ))⁻¹ := by
    have h := one_div_le_one_div_of_le hpos hupper
    norm_num at h ⊢
    exact h
  rw [← Real.exp_neg] at hinv
  nlinarith

theorem ford_exponent_range_197
    {k n : ℕ} (hk : 1000 ≤ k)
    (hn : 100 * (n - 1) ≤ 197 * k) :
    2 * (((n - 1 : ℕ) : ℝ)) / ((k : ℝ) - 2) ≤ 1970 / 499 := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (0 : ℝ) < (k : ℝ) - 2 := by linarith
  have hnR : 100 * (((n - 1 : ℕ) : ℝ)) ≤ 197 * (k : ℝ) := by
    exact_mod_cast hn
  rw [div_le_iff₀ hk2]
  have hratio : 499 * (k : ℝ) ≤ 500 * ((k : ℝ) - 2) := by
    linarith
  nlinarith

/-- The literal decimal lower bound on Ford's normalized predecessor
`delta_(n-1)`, with the source one-based index exposed in the hypotheses. -/
theorem fordDSequence36_source_predecessor_lower
    {k n : ℕ} (hk : 1000 ≤ k) (hnLower : 2 ≤ n)
    (hnUpper : 100 * (n - 1) ≤ 197 * k)
    (habove : ∀ m, m < n - 2 → (k : ℝ) < fordDeltaSequence36 k m) :
    (24119 / 2500000 : ℝ) ≤ fordDSequence36 k (n - 2) := by
  have hgeom := fordDSequence36_ge_half_geometric hk
    (i := n - 2) habove
  have hindex : n - 2 + 1 = n - 1 := by omega
  rw [hindex] at hgeom
  have hpow := ford_one_sub_two_div_pow_ge_exp (k := k) (j := n - 1) hk
  have hrange := ford_exponent_range_197 hk hnUpper
  have hexp : Real.exp (-(1970 / 499 : ℝ)) ≤
      Real.exp (-(2 * (((n - 1 : ℕ) : ℝ)) / ((k : ℝ) - 2))) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hrange)
  calc
    (24119 / 2500000 : ℝ) ≤
        (1 / 2 : ℝ) * Real.exp (-(1970 / 499 : ℝ)) :=
      ford_half_exp_neg_1970_div_499_lower
    _ ≤ (1 / 2 : ℝ) *
        Real.exp (-(2 * (((n - 1 : ℕ) : ℝ)) / ((k : ℝ) - 2))) := by
      gcongr
    _ ≤ (1 / 2 : ℝ) * (1 - 2 / (k : ℝ)) ^ (n - 1) := by
      gcongr
    _ ≤ fordDSequence36 k (n - 2) := hgeom

#print axioms fordDSequence36_ge_geometric
#print axioms fordDSequence36_ge_half_geometric
#print axioms ford_one_sub_two_div_pow_ge_exp
#print axioms ford_exp_1970_div_499_upper
#print axioms ford_half_exp_neg_1970_div_499_lower
#print axioms ford_exponent_range_197
#print axioms fordDSequence36_source_predecessor_lower

end

end GafniTao
