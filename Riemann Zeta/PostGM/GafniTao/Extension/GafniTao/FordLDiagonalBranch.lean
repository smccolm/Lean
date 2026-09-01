import GafniTao.FordLDiagonalHolder

/-!
# Ford Lemma 3.3: closure of the diagonal branch

The exact partition, coordinate deletion, and Hölder estimate are assembled
here.  If `U₀ ≥ U₁`, the literal `L_s` count is bounded by Ford's first
alternative `(2P)^k k^k J_{s,k}(Q)`.
-/

namespace GafniTao

noncomputable section

theorem fordL_reduced_holder_real
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T) (s Q q : ℕ)
    (hk : 1 ≤ k) (hpq : 0 < p * q) :
    (fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q : ℝ) ≤
      (fordLCount Ψ s P Q p q r : ℝ) ^ (1 - 1 / (k : ℝ)) *
        (fordVinogradovMomentNat s k Q : ℝ) ^ (1 / (k : ℝ)) := by
  have h := fordL_reduced_holder (P := P) (p := p) (r := r)
    Ψ s Q q hk hpq
  have hfinite :
      (fordLCount Ψ s P Q p q r : ENNReal) ^ (1 - 1 / (k : ℝ)) *
        (fordVinogradovMomentNat s k Q : ENNReal) ^ (1 / (k : ℝ)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
        rw [sub_nonneg, div_le_one hkR]
        exact_mod_cast hk
      · exact ENNReal.coe_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
      exact ENNReal.coe_ne_top
  have ht := ENNReal.toReal_mono hfinite h
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow] at ht
  simpa using ht

theorem ford_self_holder_bound_k
    {k : ℕ} (hk : 1 ≤ k) {K J C : ℝ}
    (hK : 0 < K) (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (h : K ≤ C * (K ^ (1 - 1 / (k : ℝ)) *
      J ^ (1 / (k : ℝ)))) :
    K ≤ C ^ (k : ℝ) * J := by
  let a : ℝ := 1 / (k : ℝ)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have ha : 0 < a := by dsimp [a]; positivity
  have h1a : 0 ≤ 1 - a := by
    dsimp [a]
    rw [sub_nonneg, div_le_one hkR]
    exact_mod_cast hk
  have hden : 0 < K ^ (1 - a) := Real.rpow_pos_of_pos hK _
  have hdiv : K / K ^ (1 - a) ≤ C * J ^ a := by
    exact (div_le_iff₀ hden).2
      (by simpa [a, mul_comm, mul_left_comm, mul_assoc] using h)
  have hKa : K ^ a ≤ C * J ^ a := by
    calc
      K ^ a = K ^ (1 - (1 - a)) := by congr 1; ring
      _ = K ^ (1 : ℝ) / K ^ (1 - a) := Real.rpow_sub hK _ _
      _ = K / K ^ (1 - a) := by rw [Real.rpow_one]
      _ ≤ C * J ^ a := hdiv
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hK) a) hKa
    (by positivity : (0 : ℝ) ≤ k)
  calc
    K = (K ^ a) ^ (k : ℝ) := by
      rw [← Real.rpow_mul (le_of_lt hK)]
      rw [show a * (k : ℝ) = 1 by
        dsimp [a]
        field_simp, Real.rpow_one]
    _ ≤ (C * J ^ a) ^ (k : ℝ) := hpow
    _ = C ^ (k : ℝ) * (J ^ a) ^ (k : ℝ) := by
      rw [Real.mul_rpow hC (Real.rpow_nonneg hJ a)]
    _ = C ^ (k : ℝ) * J := by
      rw [← Real.rpow_mul hJ]
      rw [show a * (k : ℝ) = 1 by
        dsimp [a]
        field_simp, Real.rpow_one]

theorem fordL_diagonal_branch_bound
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T) (s Q q : ℕ)
    (hk : 1 ≤ k) (hpq : 0 < p * q)
    (hbranch : fordLOffDiagonalCount Ψ s P Q p q r ≤
      fordLDiagonalCount Ψ s P Q p q r) :
    fordLCount Ψ s P Q p q r ≤
      (2 * P) ^ k * k ^ k * fordVinogradovMomentNat s k Q := by
  let L : ℕ := fordLCount Ψ s P Q p q r
  let D : ℕ := fordLDiagonalCount Ψ s P Q p q r
  let R : ℕ := fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q
  let J : ℕ := fordVinogradovMomentNat s k Q
  have hLD : L ≤ 2 * D := by
    have hsplit := fordLCount_eq_diagonal_add_offDiagonal Ψ s P Q p q r
    dsimp [L, D]
    omega
  have hDR : D ≤ k * P * R :=
    fordL_diagonal_le_k_mul_P_mul_reduced Ψ s P Q p q r
  have hLR : L ≤ 2 * k * P * R := by
    calc
      L ≤ 2 * D := hLD
      _ ≤ 2 * (k * P * R) := Nat.mul_le_mul_left 2 hDR
      _ = 2 * k * P * R := by ring
  by_cases hL0 : L = 0
  · simp [L, hL0]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  have hholder : (R : ℝ) ≤
      (L : ℝ) ^ (1 - 1 / (k : ℝ)) * (J : ℝ) ^ (1 / (k : ℝ)) := by
    simpa [L, R, J] using fordL_reduced_holder_real
      (P := P) (p := p) (r := r) Ψ s Q q hk hpq
  have hself : (L : ℝ) ≤ (2 * (k : ℝ) * P) *
      ((L : ℝ) ^ (1 - 1 / (k : ℝ)) *
        (J : ℝ) ^ (1 / (k : ℝ))) := by
    calc
      (L : ℝ) ≤ (2 * k * P * R : ℕ) := by exact_mod_cast hLR
      _ = (2 * (k : ℝ) * P) * R := by norm_num
      _ ≤ (2 * (k : ℝ) * P) *
          ((L : ℝ) ^ (1 - 1 / (k : ℝ)) *
            (J : ℝ) ^ (1 / (k : ℝ))) := by
        gcongr
  have hclosed := ford_self_holder_bound_k hk hLpos
    (show (0 : ℝ) ≤ J by positivity)
    (show (0 : ℝ) ≤ 2 * (k : ℝ) * P by positivity) hself
  have hclosed' : (L : ℝ) ≤
      (((2 * P) ^ k * k ^ k * J : ℕ) : ℝ) := by
    calc
      (L : ℝ) ≤ (2 * (k : ℝ) * P) ^ (k : ℝ) * J := hclosed
      _ = (2 * (k : ℝ) * P) ^ k * J := by rw [Real.rpow_natCast]
      _ = (((2 * P) ^ k * k ^ k * J : ℕ) : ℝ) := by
        push_cast
        ring
  exact_mod_cast hclosed'

#print axioms fordL_reduced_holder_real
#print axioms ford_self_holder_bound_k
#print axioms fordL_diagonal_branch_bound

end

end GafniTao
