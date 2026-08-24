import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.ArithmeticCoefficients

open Complex Finset
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-- Coefficients obtained by taking the `k`-th power of an arbitrary finite
Dirichlet polynomial on `(N,2N]`. -/
noncomputable def finitePowCoeff
    (N k : ℕ) (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ p ∈ (Fintype.piFinset (fun (_ : Fin k) => Ioc N (2 * N))).filter
      (fun p => (∏ x : Fin k, p x) = m),
    ∏ x : Fin k, a (p x)

/-- Structural form of the powered finite Dirichlet polynomial. -/
noncomputable def finitePowPoly
    (N k : ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  (∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-s)) ^ k

theorem finite_polynomial_power_identity (N k : ℕ) (a : ℕ → ℂ) (s : ℂ) :
    finitePowPoly N k a s =
      ∑ m ∈ Icc (N ^ k) ((2 * N) ^ k),
        finitePowCoeff N k a m * (m : ℂ) ^ (-s) := by
  classical
  let tuples := Fintype.piFinset (fun (_ : Fin k) => Ioc N (2 * N))
  have hsupport : ∀ p ∈ tuples,
      (∏ x : Fin k, p x) ∈ Icc (N ^ k) ((2 * N) ^ k) := by
    intro p hp
    exact powCoeff_product_mem_support N k p hp
  rw [finitePowPoly, Finset.sum_pow']
  change (∑ p ∈ tuples, ∏ x : Fin k, (a (p x) * (p x : ℂ) ^ (-s))) = _
  calc
    (∑ p ∈ tuples, ∏ x : Fin k, (a (p x) * (p x : ℂ) ^ (-s))) =
        ∑ p ∈ tuples, (∏ x : Fin k, a (p x)) *
          ((∏ x : Fin k, p x : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.prod_mul_distrib, prod_natCast_cpow_eq]
    _ = ∑ m ∈ Icc (N ^ k) ((2 * N) ^ k),
        ∑ p ∈ tuples with (∏ x : Fin k, p x) = m,
          (∏ x : Fin k, a (p x)) *
            ((∏ x : Fin k, p x : ℕ) : ℂ) ^ (-s) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hsupport _
    _ = ∑ m ∈ Icc (N ^ k) ((2 * N) ^ k),
        finitePowCoeff N k a m * (m : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [finitePowCoeff, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

theorem finitePowCoeff_lower_endpoint_eq_zero
    (N k : ℕ) (a : ℕ → ℂ) (hN : 0 < N) (hk : 0 < k) :
    finitePowCoeff N k a (N ^ k) = 0 := by
  classical
  rw [finitePowCoeff]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨hpSupport, hpProduct⟩
  rw [Fintype.mem_piFinset] at hpSupport
  have hCoordinate : ∀ x : Fin k, N + 1 ≤ p x := by
    intro x
    have hx := (Finset.mem_Ioc.mp (hpSupport x)).1
    omega
  have hProductLower : (N + 1) ^ k ≤ ∏ x : Fin k, p x := by
    calc
      (N + 1) ^ k = ∏ _x : Fin k, (N + 1) := by simp
      _ ≤ ∏ x : Fin k, p x := by
        apply Finset.prod_le_prod
        · intro _ _
          omega
        · intro x _
          exact hCoordinate x
  have hStrict : N ^ k < (N + 1) ^ k :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self N) hk.ne'
  omega

theorem finite_polynomial_power_identity_Ioc
    (N k : ℕ) (a : ℕ → ℂ) (s : ℂ) (hN : 0 < N) (hk : 0 < k) :
    finitePowPoly N k a s =
      ∑ m ∈ Ioc (N ^ k) ((2 * N) ^ k),
        finitePowCoeff N k a m * (m : ℂ) ^ (-s) := by
  rw [finite_polynomial_power_identity]
  rw [Finset.Icc_eq_cons_Ioc]
  · simp [finitePowCoeff_lower_endpoint_eq_zero N k a hN hk]
  · exact Nat.pow_le_pow_left (by omega : N ≤ 2 * N) k

/-- Bounded base coefficients give epsilon-power bounds for every fixed
power.  The constant is uniform in the block length and the target index. -/
theorem finitePowCoeff_bound
    (N k : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Ioc N (2 * N), ‖a n‖ ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ m : ℕ, 0 < m →
        ‖finitePowCoeff N k a m‖ ≤ C * (m : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨C, hC, hFactor⟩ := factorizationCountBound_native k ε hε
  refine ⟨C, hC, ?_⟩
  intro m hm
  let source := (Fintype.piFinset (fun (_ : Fin k) => Ioc N (2 * N))).filter
    (fun p => (∏ x : Fin k, p x) = m)
  let target := (Fintype.piFinset (fun (_ : Fin k) => Ioc 1 m)).filter
    (fun p => (∏ x : Fin k, p x) = m)
  have hsource : source ⊆ target := by
    simpa [source, target] using pow_coeff_subset N k m hm
  have hterm : ∀ p ∈ source, ‖∏ x : Fin k, a (p x)‖ ≤ 1 := by
    intro p hp
    rw [norm_prod]
    apply Finset.prod_le_one
    · intro x _
      exact norm_nonneg _
    · intro x _
      have hpSource := (Finset.mem_filter.mp hp).1
      rw [Fintype.mem_piFinset] at hpSource
      exact ha (p x) (hpSource x)
  calc
    ‖finitePowCoeff N k a m‖
        ≤ ∑ p ∈ source, ‖∏ x : Fin k, a (p x)‖ := by
          simpa only [finitePowCoeff, source] using
            norm_sum_le source (fun p => ∏ x : Fin k, a (p x))
    _ ≤ ∑ _p ∈ source, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (source.card : ℝ) := by simp
    _ ≤ (target.card : ℝ) := by exact_mod_cast Finset.card_le_card hsource
    _ ≤ C * (m : ℝ) ^ ε := by simpa [target] using hFactor m hm

/-- Quantifier-correct uniform form of `finitePowCoeff_bound`.  For a fixed
power and epsilon, the factorization constant is chosen before the block
length and coefficients, exactly as required by an eventual density bound. -/
theorem finitePowCoeff_bound_uniform
    (k : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℕ → ℂ),
      (∀ n ∈ Ioc N (2 * N), ‖a n‖ ≤ 1) →
      ∀ m : ℕ, 0 < m →
        ‖finitePowCoeff N k a m‖ ≤ C * (m : ℝ) ^ eps := by
  obtain ⟨C, hC, hFactor⟩ := factorizationCountBound_native k eps heps
  refine ⟨C, hC, ?_⟩
  intro N a ha m hm
  let source := (Fintype.piFinset (fun (_ : Fin k) => Ioc N (2 * N))).filter
    (fun p => (∏ x : Fin k, p x) = m)
  let target := (Fintype.piFinset (fun (_ : Fin k) => Ioc 1 m)).filter
    (fun p => (∏ x : Fin k, p x) = m)
  have hsource : source ⊆ target := by
    simpa [source, target] using pow_coeff_subset N k m hm
  have hterm : ∀ p ∈ source, ‖∏ x : Fin k, a (p x)‖ ≤ 1 := by
    intro p hp
    rw [norm_prod]
    apply Finset.prod_le_one
    · intro x _
      exact norm_nonneg _
    · intro x _
      have hpSource := (Finset.mem_filter.mp hp).1
      rw [Fintype.mem_piFinset] at hpSource
      exact ha (p x) (hpSource x)
  calc
    ‖finitePowCoeff N k a m‖
        ≤ ∑ p ∈ source, ‖∏ x : Fin k, a (p x)‖ := by
          simpa only [finitePowCoeff, source] using
            norm_sum_le source (fun p => ∏ x : Fin k, a (p x))
    _ ≤ ∑ _p ∈ source, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (source.card : ℝ) := by simp
    _ ≤ (target.card : ℝ) := by exact_mod_cast Finset.card_le_card hsource
    _ ≤ C * (m : ℝ) ^ eps := by simpa [target] using hFactor m hm

/-- Fixed-line coefficients of an arbitrary powered block, scaled at the
left endpoint. -/
noncomputable def finitePoweredLineCoeffs
    (N k : ℕ) (a : ℕ → ℂ) (σ : ℝ) (m : ℕ) : ℂ :=
  (((N ^ k : ℕ) : ℝ) : ℂ) ^ (σ : ℂ) *
    (finitePowCoeff N k a m * (m : ℂ) ^ (-(σ : ℂ)))

theorem wideDirichletPoly_finitePoweredLineCoeffs
    (N k : ℕ) (a : ℕ → ℂ) (σ t : ℝ) (hN : 0 < N) (hk : 0 < k) :
    wideDirichletPoly (N ^ k) k (finitePoweredLineCoeffs N k a σ) t =
      (((N ^ k : ℕ) : ℝ) : ℂ) ^ (σ : ℂ) *
        finitePowPoly N k a (σ + I * t) := by
  rw [finite_polynomial_power_identity_Ioc N k a (σ + I * t) hN hk]
  unfold wideDirichletPoly finitePoweredLineCoeffs
  have hUpper : 2 ^ k * N ^ k = (2 * N) ^ k := by rw [mul_pow]
  rw [hUpper, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hm).1
  have hmNe : (m : ℂ) ≠ 0 := by exact_mod_cast hmPos.ne'
  rw [mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hmNe]
  congr 2
  ring_nf

theorem norm_finitePoweredLineCoeffs_le
    (N k m : ℕ) (a : ℕ → ℂ) (σ : ℝ)
    (hN : 0 < N) (hσ : 0 ≤ σ)
    (hm : m ∈ Ioc (N ^ k) (2 ^ k * N ^ k)) :
    ‖finitePoweredLineCoeffs N k a σ m‖ ≤ ‖finitePowCoeff N k a m‖ := by
  have hQNat : 0 < N ^ k := pow_pos hN k
  have hmNat : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hm).1
  have hQ : (0 : ℝ) < (N ^ k : ℕ) := by exact_mod_cast hQNat
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hmNat
  have hQm : ((N ^ k : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hm).1.le
  have hPow : (((N ^ k : ℕ) : ℝ)) ^ σ ≤ (m : ℝ) ^ σ :=
    Real.rpow_le_rpow hQ.le hQm hσ
  have hmPowPos : 0 < (m : ℝ) ^ σ := Real.rpow_pos_of_pos hmReal _
  have hScale : (((N ^ k : ℕ) : ℝ)) ^ σ * (m : ℝ) ^ (-σ) ≤ 1 := by
    rw [Real.rpow_neg hmReal.le, ← div_eq_mul_inv]
    exact (div_le_one hmPowPos).2 hPow
  have hQNorm : ‖((((N ^ k : ℕ) : ℝ) : ℂ) ^ (σ : ℂ))‖ =
      (((N ^ k : ℕ) : ℝ)) ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ]
    rfl
  have hmNorm : ‖((m : ℂ) ^ (-(σ : ℂ)))‖ = (m : ℝ) ^ (-σ) := by
    change ‖(((m : ℝ) : ℂ) ^ (-(σ : ℂ)))‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hmReal]
    rfl
  rw [finitePoweredLineCoeffs, norm_mul, norm_mul, hQNorm, hmNorm]
  calc
    (((N ^ k : ℕ) : ℝ)) ^ σ *
        (‖finitePowCoeff N k a m‖ * (m : ℝ) ^ (-σ)) =
        ((((N ^ k : ℕ) : ℝ)) ^ σ * (m : ℝ) ^ (-σ)) *
          ‖finitePowCoeff N k a m‖ := by ring
    _ ≤ 1 * ‖finitePowCoeff N k a m‖ := by gcongr
    _ = ‖finitePowCoeff N k a m‖ := one_mul _

/-- Unit normalization of the powered coefficients on their full wide
support. -/
noncomputable def normalizedFinitePoweredCoeffs
    (N k : ℕ) (a : ℕ → ℂ) (σ C η : ℝ) (m : ℕ) : ℂ :=
  finitePoweredLineCoeffs N k a σ m /
    ((C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η : ℝ) : ℂ)

theorem norm_normalizedFinitePoweredCoeffs_le_one
    (N k m : ℕ) (a : ℕ → ℂ) (σ C η : ℝ)
    (hN : 0 < N) (hσ : 0 ≤ σ) (hC : 0 < C) (hη : 0 < η)
    (hm : m ∈ Ioc (N ^ k) (2 ^ k * N ^ k))
    (hCoeff : ‖finitePowCoeff N k a m‖ ≤ C * (m : ℝ) ^ η) :
    ‖normalizedFinitePoweredCoeffs N k a σ C η m‖ ≤ 1 := by
  have hmUpper : m ≤ 2 ^ k * N ^ k := (Finset.mem_Ioc.mp hm).2
  have hUpperPos : 0 < 2 ^ k * N ^ k :=
    mul_pos (pow_pos (by omega) k) (pow_pos hN k)
  have hRpow : (m : ℝ) ^ η ≤ ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmUpper) hη.le
  have hDenomPos : 0 < C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η := by
    exact mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast hUpperPos) _)
  have hDenomNorm :
      ‖((C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η : ℝ) : ℂ)‖ =
        C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η := by
    simpa only [Complex.norm_real] using abs_of_pos hDenomPos
  rw [normalizedFinitePoweredCoeffs, norm_div, hDenomNorm,
    div_le_one hDenomPos]
  exact (norm_finitePoweredLineCoeffs_le N k m a σ hN hσ hm).trans
    (hCoeff.trans (mul_le_mul_of_nonneg_left hRpow hC.le))

theorem wideDirichletPoly_normalizedFinitePoweredCoeffs
    (N k : ℕ) (a : ℕ → ℂ) (σ C η t : ℝ)
    (hN : 0 < N) (hk : 0 < k) :
    wideDirichletPoly (N ^ k) k
        (normalizedFinitePoweredCoeffs N k a σ C η) t =
      ((((N ^ k : ℕ) : ℝ) : ℂ) ^ (σ : ℂ) *
          finitePowPoly N k a (σ + I * t)) /
        ((C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η : ℝ) : ℂ) := by
  rw [← wideDirichletPoly_finitePoweredLineCoeffs N k a σ t hN hk]
  unfold wideDirichletPoly
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  rw [normalizedFinitePoweredCoeffs, div_mul_eq_mul_div]

/-- A lower bound for the base block survives taking a fixed power and the
normalizations required by MHH. -/
theorem normalized_finite_powered_wide_lower
    (N k : ℕ) (a : ℕ → ℂ) (σ C η t L : ℝ)
    (hN : 0 < N) (hk : 0 < k) (hL : 0 ≤ L)
    (hDenom : 0 < C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)
    (hBase : L ≤ ‖∑ n ∈ Ioc N (2 * N),
      a n * (n : ℂ) ^ (-(σ + I * t))‖) :
    ((N ^ k : ℕ) : ℝ) ^ σ * L ^ k /
        (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ≤
      ‖wideDirichletPoly (N ^ k) k
        (normalizedFinitePoweredCoeffs N k a σ C η) t‖ := by
  have hQNat : 0 < N ^ k := pow_pos hN k
  have hQ : (0 : ℝ) < (N ^ k : ℕ) := by exact_mod_cast hQNat
  have hQNorm : ‖((((N ^ k : ℕ) : ℝ) : ℂ) ^ (σ : ℂ))‖ =
      ((N ^ k : ℕ) : ℝ) ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ]
    rfl
  have hDenomNorm :
      ‖((C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η : ℝ) : ℂ)‖ =
        C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η := by
    simpa only [Complex.norm_real] using abs_of_pos hDenom
  have hPower : L ^ k ≤ ‖finitePowPoly N k a (σ + I * t)‖ := by
    rw [finitePowPoly, norm_pow]
    exact pow_le_pow_left₀ hL hBase k
  rw [wideDirichletPoly_normalizedFinitePoweredCoeffs N k a σ C η t hN hk,
    norm_div, norm_mul, hQNorm, hDenomNorm]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hPower (Real.rpow_nonneg hQ.le σ)) hDenom.le

/-- A common ordinary dyadic powered block carries the large value for a
common subset of ordinates. -/
theorem extract_normalized_finite_powered_block
    (N k : ℕ) (a : ℕ → ℂ) (σ C η L : ℝ) (W : Finset ℝ)
    (hN : 0 < N) (hk : 0 < k) (hL : 0 ≤ L)
    (hDenom : 0 < C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)
    (hBase : ∀ t ∈ W, L ≤ ‖∑ n ∈ Ioc N (2 * N),
      a n * (n : ℂ) ^ (-(σ + I * t))‖) :
    ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
      (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
      ∀ t ∈ W',
        (((N ^ k : ℕ) : ℝ) ^ σ * L ^ k /
            (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k ≤
          ‖dirichletPoly (2 ^ r * N ^ k)
            (normalizedFinitePoweredCoeffs N k a σ C η) t‖ := by
  apply exists_dyadic_block_and_subset (N ^ k) k
    (normalizedFinitePoweredCoeffs N k a σ C η) W
    (((N ^ k : ℕ) : ℝ) ^ σ * L ^ k /
      (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) hk
  intro t ht
  exact normalized_finite_powered_wide_lower N k a σ C η t L
    hN hk hL hDenom (hBase t ht)

end RiemannZeta.GuthMaynard
