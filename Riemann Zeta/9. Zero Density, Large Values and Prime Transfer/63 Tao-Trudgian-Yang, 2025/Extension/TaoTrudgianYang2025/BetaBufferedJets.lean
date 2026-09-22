import TaoTrudgianYang2025.BetaBufferedCutoff

/-!
# Endpoint-independent derivative budgets for buffered cutoffs

The jth derivative costs eta^(-j), uniformly in both endpoints.
The statement includes overlapping transition bands and reversed intervals.
-/

noncomputable section

open Set
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

theorem iteratedDeriv_modelPhaseBufferedCutoff
    (l r η u : ℝ) (n : ℕ) :
    iteratedDeriv n (modelPhaseBufferedCutoff l r η) u =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        ((η⁻¹)^j * iteratedDeriv j Real.smoothTransition ((u-l)/η-1)) *
        ((-η⁻¹)^(n-j) * iteratedDeriv (n-j) Real.smoothTransition ((r-u)/η-1)) := by
  have heq : modelPhaseBufferedCutoff l r η =
      fun x => Real.smoothTransition (η⁻¹*x+(-l/η-1)) *
        Real.smoothTransition ((-η⁻¹)*x+(r/η-1)) := by
    funext x
    unfold modelPhaseBufferedCutoff
    congr 2 <;> ring
  rw [heq,iteratedDeriv_fun_mul (by fun_prop) (by fun_prop)]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDeriv_smoothTransition_affine,iteratedDeriv_smoothTransition_affine]
  rw [show η⁻¹*u+(-l/η-1) = (u-l)/η-1 by ring,
    show (-η⁻¹)*u+(r/η-1) = (r-u)/η-1 by ring]

theorem abs_iteratedDeriv_modelPhaseBufferedCutoff_le
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η)
    (n : ℕ)
    (hb : ∀ x : ℝ, ∀ j ≤ n, |iteratedDeriv j Real.smoothTransition x| ≤ M)
    (l r u : ℝ) :
    |iteratedDeriv n (modelPhaseBufferedCutoff l r η) u| ≤
      (2 : ℝ)^n*M^2*(η⁻¹)^n := by
  rw [iteratedDeriv_modelPhaseBufferedCutoff]
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1),
        |(n.choose j : ℝ) *
          ((η⁻¹)^j*iteratedDeriv j Real.smoothTransition ((u-l)/η-1)) *
          ((-η⁻¹)^(n-j)*iteratedDeriv (n-j) Real.smoothTransition ((r-u)/η-1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*(M^2*(η⁻¹)^n) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_pow,abs_pow,abs_neg,
        abs_of_nonneg (inv_nonneg.mpr hη.le),abs_of_nonneg (Nat.cast_nonneg _)]
      have hleft := mul_le_mul_of_nonneg_left (hb ((u-l)/η-1) j hjn)
        (pow_nonneg (inv_nonneg.mpr hη.le) j)
      have hright := mul_le_mul_of_nonneg_left (hb ((r-u)/η-1) (n-j) (Nat.sub_le _ _))
        (pow_nonneg (inv_nonneg.mpr hη.le) (n-j))
      calc
        _ ≤ (n.choose j : ℝ)*((η⁻¹)^j*M)*((η⁻¹)^(n-j)*M) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hleft (Nat.cast_nonneg _)) hright
            (mul_nonneg (pow_nonneg (inv_nonneg.mpr hη.le) _) (abs_nonneg _))
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg (inv_nonneg.mpr hη.le) _) hM))
        _ = (n.choose j : ℝ)*(M^2*(η⁻¹)^n) := by
          have hp : (η⁻¹)^j*(η⁻¹)^(n-j) = (η⁻¹)^n := by
            rw [← pow_add,Nat.add_sub_of_le hjn]
          calc
            _ = (n.choose j : ℝ)*(M^2*((η⁻¹)^j*(η⁻¹)^(n-j))) := by ring
            _ = _ := by rw [hp]
    _ = (2 : ℝ)^n*M^2*(η⁻¹)^n := by
      rw [← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]
      ring

theorem modelPhaseBufferedCutoff_uniform_jets (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η u : ℝ), 0 < η → η ≤ 1 →
      ∀ j ≤ Q, |iteratedDeriv j (modelPhaseBufferedCutoff l r η) u| ≤ C*(η⁻¹)^Q := by
  obtain ⟨M,hM,hb⟩ := smoothTransition_finite_jet_bound Q
  refine ⟨(2 : ℝ)^Q*M^2,?_,?_⟩
  · have hpow : 1 ≤ (2 : ℝ)^Q := one_le_pow₀ (by norm_num)
    nlinarith [sq_nonneg (M-1)]
  · intro l r η u hη hη₁ j hj
    have hA : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη₁
    have h := abs_iteratedDeriv_modelPhaseBufferedCutoff_le (zero_le_one.trans hM) hη j
      (fun x k hk => hb x k (hk.trans hj)) l r u
    apply h.trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)
        (sq_nonneg M))
      (pow_le_pow_right₀ hA hj) (pow_nonneg (inv_nonneg.mpr hη.le) _)
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (sq_nonneg M))

theorem modelPhaseBufferedCutoff_uniform_ordered_jets (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η u : ℝ), 0 < η →
      ∀ j ≤ Q, |iteratedDeriv j (modelPhaseBufferedCutoff l r η) u| ≤ C*(η⁻¹)^j := by
  obtain ⟨M,hM,hb⟩ := smoothTransition_finite_jet_bound Q
  refine ⟨(2 : ℝ)^Q*M^2,?_,?_⟩
  · have hpow : 1 ≤ (2 : ℝ)^Q := one_le_pow₀ (by norm_num)
    nlinarith [sq_nonneg (M-1)]
  · intro l r η u hη j hj
    have h := abs_iteratedDeriv_modelPhaseBufferedCutoff_le (zero_le_one.trans hM) hη j
      (fun x k hk => hb x k (hk.trans hj)) l r u
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)
        (sq_nonneg M)) (pow_nonneg (inv_nonneg.mpr hη.le) _))

end TaoTrudgianYang2025
