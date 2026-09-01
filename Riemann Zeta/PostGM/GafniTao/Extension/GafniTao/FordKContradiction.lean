import GafniTao.FordKRepeatedBound

/-!
# Ford Lemma 3.2: maximality contradiction

This file closes Ford's singular-class alternative.  The analytic input is
the literal repeated-coordinate torus integral; the arithmetic output is the
source conclusion that the maximizing `K` is at most twice its distinct
class when `P > 4 k^4`.
-/

namespace GafniTao

noncomputable section

theorem ford_self_holder_bound
    {k : ℕ} (hk : 1 ≤ k) {K J C : ℝ}
    (hK : 0 < K) (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (h : K ≤ C * (K ^ (1 - 1 / (2 * k : ℝ)) *
      J ^ (1 / (2 * k : ℝ)))) :
    K ≤ C ^ (2 * k : ℝ) * J := by
  let r : ℝ := 1 / (2 * k : ℝ)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hr : 0 < r := by dsimp [r]; positivity
  have h1r : 0 ≤ 1 - r := by
    dsimp [r]
    rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < 2 * k)]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hden : 0 < K ^ (1 - r) := Real.rpow_pos_of_pos hK _
  have hdiv : K / K ^ (1 - r) ≤ C * J ^ r := by
    exact (div_le_iff₀ hden).2
      (by simpa [r, mul_comm, mul_left_comm, mul_assoc] using h)
  have hKr : K ^ r ≤ C * J ^ r := by
    calc
      K ^ r = K ^ (1 - (1 - r)) := by congr 1; ring
      _ = K ^ (1 : ℝ) / K ^ (1 - r) := Real.rpow_sub hK _ _
      _ = K / K ^ (1 - r) := by rw [Real.rpow_one]
      _ ≤ C * J ^ r := hdiv
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hK) r) hKr
    (by positivity : (0 : ℝ) ≤ 2 * k)
  calc
    K = (K ^ r) ^ (2 * k : ℝ) := by
      rw [← Real.rpow_mul (le_of_lt hK)]
      rw [show r * (2 * k : ℝ) = 1 by
        dsimp [r]
        field_simp, Real.rpow_one]
    _ ≤ (C * J ^ r) ^ (2 * k : ℝ) := hpow
    _ = C ^ (2 * k : ℝ) * (J ^ r) ^ (2 * k : ℝ) := by
      rw [Real.mul_rpow hC (Real.rpow_nonneg hJ r)]
    _ = C ^ (2 * k : ℝ) * J := by
      rw [← Real.rpow_mul hJ]
      rw [show r * (2 * k : ℝ) = 1 by
        dsimp [r]
        field_simp, Real.rpow_one]

theorem fordK_le_two_distinct_of_maximal
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hk : 1 ≤ k) (hP : 4 * k ^ 4 < P) (hQ : 0 < Q) (hq : 0 < q)
    (hmax : FordKMaximal s P Q q Ψ) :
    fordKCount Ψ s P Q q ≤
      2 * Nat.card (FordKDistinctSolution Ψ s P Q q) := by
  let K : ℕ := fordKCount Ψ s P Q q
  let D : ℕ := Nat.card (FordKDistinctSolution Ψ s P Q q)
  let R : ℕ := Nat.card (FordKRepeatedSolution Ψ s P Q q)
  let J : ℕ := fordVinogradovMomentNat s k Q
  have hsplit : K = D + R := by
    exact fordK_count_eq_distinct_add_repeated Ψ
  by_contra hnot
  have hDR : D ≤ R := by omega
  have hKR : K ≤ 2 * R := by omega
  have hJpos : 0 < J := by
    have hdiag := ford_floor_pow_le_vinogradovMoment s k (P := (Q : ℝ))
    have hdiag' : Q ^ s ≤ J := by
      simpa [J, fordVinogradovMoment] using hdiag
    have : 0 < Q ^ s := pow_pos hQ s
    exact lt_of_lt_of_le this hdiag'
  have hKpos : 0 < K := by
    have hdiag := fordK_diagonal_lower Ψ s P Q q
    have hPpos : 0 < P := lt_trans (by positivity) hP
    have : 0 < P ^ k * J := mul_pos (pow_pos hPpos k) hJpos
    exact lt_of_lt_of_le this hdiag
  have hrep := fordK_repeated_card_le_k_sq_integral
    (s := s) (P := P) (Q := Q) (q := q) Ψ
  have hholder := fordK_repeated_integral_holder_real Ψ s P Q q hk hq
  have hdouble : fordKCount (fordDoubleIntegerPolynomialSystem Ψ) s P Q q ≤ K :=
    fordKMaximal_double hmax
  have hdoubleR :
      (fordKCount (fordDoubleIntegerPolynomialSystem Ψ) s P Q q : ℝ) ≤ K := by
    exact_mod_cast hdouble
  have hp : 0 ≤ 1 - 1 / (k : ℝ) := by
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    rw [sub_nonneg, div_le_one hkR]
    exact_mod_cast hk
  have hr : 0 ≤ 1 / (2 * k : ℝ) := by positivity
  have hholder' : fordKRepeatedIntegral Ψ s P Q q ≤
      (K : ℝ) ^ (1 - 1 / (k : ℝ)) * (J : ℝ) ^ (1 / (2 * k : ℝ)) *
        (K : ℝ) ^ (1 / (2 * k : ℝ)) := by
    apply hholder.trans
    gcongr
  have hexp : (1 - 1 / (k : ℝ)) + 1 / (2 * k : ℝ) =
      1 - 1 / (2 * k : ℝ) := by
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    field_simp
    ring
  have hholder'' : fordKRepeatedIntegral Ψ s P Q q ≤
      (K : ℝ) ^ (1 - 1 / (2 * k : ℝ)) *
        (J : ℝ) ^ (1 / (2 * k : ℝ)) := by
    calc
      fordKRepeatedIntegral Ψ s P Q q ≤
          (K : ℝ) ^ (1 - 1 / (k : ℝ)) *
            (J : ℝ) ^ (1 / (2 * k : ℝ)) *
            (K : ℝ) ^ (1 / (2 * k : ℝ)) := hholder'
      _ = ((K : ℝ) ^ (1 - 1 / (k : ℝ)) *
            (K : ℝ) ^ (1 / (2 * k : ℝ))) *
            (J : ℝ) ^ (1 / (2 * k : ℝ)) := by ring
      _ = (K : ℝ) ^ (1 - 1 / (2 * k : ℝ)) *
            (J : ℝ) ^ (1 / (2 * k : ℝ)) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < K), hexp]
  have hKI : (K : ℝ) ≤ (2 * (k : ℝ) ^ 2) *
      fordKRepeatedIntegral Ψ s P Q q := by
    calc
      (K : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hKR
      _ ≤ 2 * ((k : ℝ) ^ 2 * fordKRepeatedIntegral Ψ s P Q q) := by
        gcongr
      _ = (2 * (k : ℝ) ^ 2) * fordKRepeatedIntegral Ψ s P Q q := by ring
  have hself : (K : ℝ) ≤ (2 * (k : ℝ) ^ 2) *
      ((K : ℝ) ^ (1 - 1 / (2 * k : ℝ)) *
        (J : ℝ) ^ (1 / (2 * k : ℝ))) :=
    hKI.trans (mul_le_mul_of_nonneg_left hholder'' (by positivity))
  have hKupper := ford_self_holder_bound hk
    (K := (K : ℝ)) (J := (J : ℝ)) (C := 2 * (k : ℝ) ^ 2)
    (by exact_mod_cast hKpos) (by positivity) (by positivity) hself
  have hdiag := fordK_diagonal_lower Ψ s P Q q
  have hdiagR : (P : ℝ) ^ k * J ≤ K := by exact_mod_cast hdiag
  have hPJ : (P : ℝ) ^ k ≤ (2 * (k : ℝ) ^ 2) ^ (2 * k : ℝ) := by
    have hJr : (0 : ℝ) < J := by exact_mod_cast hJpos
    nlinarith
  have hpowC : (2 * (k : ℝ) ^ 2) ^ (2 * k : ℝ) =
      ((4 * k ^ 4 : ℕ) : ℝ) ^ k := by
    rw [show (2 * k : ℝ) = ((2 * k : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, pow_mul]
    push_cast
    ring
  rw [hpowC] at hPJ
  have hbase : (P : ℝ) ≤ (4 * k ^ 4 : ℕ) := by
    by_contra hbaseNot
    have hbaseLt : ((4 * k ^ 4 : ℕ) : ℝ) < P := lt_of_not_ge hbaseNot
    have := pow_lt_pow_left₀ hbaseLt
      (by positivity : (0 : ℝ) ≤ (4 * k ^ 4 : ℕ)) (by omega : k ≠ 0)
    exact (not_lt_of_ge hPJ) this
  exact (not_lt_of_ge (by exact_mod_cast hbase)) hP

#print axioms ford_self_holder_bound
#print axioms fordK_le_two_distinct_of_maximal

end

end GafniTao
