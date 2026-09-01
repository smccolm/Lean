import GafniTao.FordExplicitData.PositivePower11

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

theorem fordPositiveTaylorPower11_eq_pow :
    fordPositiveTaylorPower11 = fordPositiveTaylorPower1 ^ 11 := by
  rw [fordPositiveTaylorPower11_step, fordPositiveTaylorPower10_step,
    fordPositiveTaylorPower9_step, fordPositiveTaylorPower8_step,
    fordPositiveTaylorPower7_step, fordPositiveTaylorPower6_step,
    fordPositiveTaylorPower5_step, fordPositiveTaylorPower4_step,
    fordPositiveTaylorPower3_step, fordPositiveTaylorPower2_step]
  ring

def fordBiRatHom : ℚ →+* FordBiPolynomial :=
  (Polynomial.C : Polynomial ℚ →+* Polynomial (Polynomial ℚ)).comp
    (Polynomial.C : ℚ →+* Polynomial ℚ)

def fordPositiveLift (p : Polynomial ℚ) : FordBiPolynomial :=
  Polynomial.eval₂ fordBiRatHom fordPositivePhasePolynomial p

def fordPositiveUpperCompact : FordBiPolynomial :=
  fordPositiveLift fordPositiveTaylorPower11

theorem fordPositiveLift_mul (p q : Polynomial ℚ) :
    fordPositiveLift (p * q) = fordPositiveLift p * fordPositiveLift q := by
  exact map_mul
    (Polynomial.eval₂RingHom fordBiRatHom fordPositivePhasePolynomial) p q

theorem fordPositiveLift_pow (p : Polynomial ℚ) (n : ℕ) :
    fordPositiveLift (p ^ n) = fordPositiveLift p ^ n := by
  exact map_pow
    (Polynomial.eval₂RingHom fordBiRatHom fordPositivePhasePolynomial) p n

def fordPositiveTaylorSourceBase : Polynomial ℚ :=
  (∑ k ∈ Finset.range 6,
    (Polynomial.C (-1 / (11 : ℚ)) * Polynomial.X) ^ k *
      Polynomial.C (1 / (k.factorial : ℚ))) +
    (Polynomial.C (1 / (11 : ℚ)) * Polynomial.X) ^ 6 *
      Polynomial.C ((Nat.succ 6 : ℚ) / ((Nat.factorial 6 : ℚ) * 6))

theorem fordPositiveTaylorPower1_eq_sourceBase :
    fordPositiveTaylorPower1 = fordPositiveTaylorSourceBase := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (f := fun i : Fin 7 => (i : ℚ))
  · intro i j hij
    change (i.val : ℚ) = j.val at hij
    apply Fin.ext
    exact_mod_cast hij
  · intro i
    fin_cases i <;> norm_num [fordPositiveTaylorPower1,
      fordPositiveTaylorSourceBase, Finset.sum_range_succ]
  · simp only [Fintype.card_fin]
    have hleft : fordPositiveTaylorPower1.natDegree ≤ 6 := by
      unfold fordPositiveTaylorPower1
      compute_degree
    have hright : fordPositiveTaylorSourceBase.natDegree ≤ 6 := by
      unfold fordPositiveTaylorSourceBase
      apply le_trans (Polynomial.natDegree_add_le _ _)
      apply max_le
      · apply Polynomial.natDegree_sum_le_of_forall_le
        intro k hk
        have hk6 : k ≤ 6 := (Finset.mem_range.mp hk).le
        calc
          ((Polynomial.C (-1 / (11 : ℚ)) * Polynomial.X) ^ k *
              Polynomial.C (1 / (k.factorial : ℚ))).natDegree
              ≤ ((Polynomial.C (-1 / (11 : ℚ)) * Polynomial.X) ^ k).natDegree +
                  (Polynomial.C (1 / (k.factorial : ℚ))).natDegree :=
                Polynomial.natDegree_mul_le
          _ ≤ k * (Polynomial.C (-1 / (11 : ℚ)) * Polynomial.X).natDegree + 0 := by
                gcongr
                · exact Polynomial.natDegree_pow_le
                · exact Mathlib.Tactic.ComputeDegree.natDegree_C_le _
          _ ≤ k := by
                have hb : (Polynomial.C (-1 / (11 : ℚ)) * Polynomial.X).natDegree = 1 := by
                  compute_degree; norm_num
                rw [hb]
                simp
          _ ≤ 6 := hk6
      · compute_degree
    omega

theorem fordPositiveLift_base :
    fordPositiveLift fordPositiveTaylorPower1 =
      (∑ k ∈ Finset.range 6,
        (fordBiRat (-1 / (11 : ℚ)) * fordPositivePhasePolynomial) ^ k *
          fordBiRat (1 / (k.factorial : ℚ))) +
        (fordBiRat (1 / (11 : ℚ)) * fordPositivePhasePolynomial) ^ 6 *
          fordBiRat ((Nat.succ 6 : ℚ) / ((Nat.factorial 6 : ℚ) * 6)) := by
  rw [fordPositiveTaylorPower1_eq_sourceBase]
  unfold fordPositiveLift fordPositiveTaylorSourceBase
  rw [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  rfl

theorem fordPositiveUpperPolynomial_eq_compact :
    fordPositiveUpperPolynomial = fordPositiveUpperCompact := by
  unfold fordPositiveUpperPolynomial fordScaledTaylorPolynomial
  unfold fordPositiveUpperCompact
  rw [fordPositiveTaylorPower11_eq_pow, fordPositiveLift_pow,
    fordPositiveLift_base]
  norm_num

end

end GafniTao
