import RiemannZeta.GuthMaynard.FiniteDensityTransfer
import RiemannZeta.GuthMaynard.ClassicalPowering

open Complex Finset Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-- The fixed-line sharp detector block is exactly the corresponding finite
Dirichlet series evaluated at `σ+it`. -/
theorem dirichletPoly_sharpMollifiedLineCoeff_eq
    (A X N : ℕ) (σ t : ℝ) :
    dirichletPoly N (sharpMollifiedLineCoeff A X σ) t =
      ∑ n ∈ Ioc N (2 * N),
        sharpMollifiedCoeff A X n * (n : ℂ) ^ (-(σ + I * t)) := by
  unfold dirichletPoly dyadicInterval sharpMollifiedLineCoeff
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hn).1
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
  rw [mul_assoc, ← Complex.cpow_add _ _ hnNe]
  congr 2
  ring_nf

/-- A unit-bounded fixed-coefficient block may be raised, normalized,
pigeonholed to one dyadic block, and passed to the finite MHH estimate.  This
is the coefficient-generic core of the powered Type-II argument. -/
theorem powered_unit_block_large_values_bound
    (N k : ℕ) (a : ℕ → ℂ) (σ H L : ℝ) (W : Finset ℝ)
    (hN : 0 < N) (hk : 0 < k) (hσ : 0 ≤ σ) (hH : 1 ≤ H)
    (hL : 0 < L) (ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval H W)
    (hLarge : ∀ t ∈ W,
      L ≤ ‖∑ n ∈ Finset.Ioc N (2 * N),
        a n * (n : ℂ) ^ (-(σ + I * t))‖) :
    ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, 0 < C ∧
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let Q := 2 ^ r * N ^ k
          let V := ((((N ^ k : ℕ) : ℝ) ^ σ * L ^ k /
              (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k)
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', V ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k a σ C η) t‖) ∧
          ∃ K : ℝ, 0 < K ∧
            (W'.card : ℝ) ≤
              K * (1 + (((harmonic Q : ℚ) : ℝ))) *
                ((Q : ℝ) ^ 2 / V ^ 2 +
                  H * min ((Q : ℝ) / V ^ 2)
                    ((Q : ℝ) ^ 4 / V ^ 6)) := by
  intro η hη
  obtain ⟨C, hC, hCoeff⟩ := finitePowCoeff_bound N k a ha η hη
  have hDenom : 0 < C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η := by
    have hUpper : 0 < 2 ^ k * N ^ k :=
      mul_pos (pow_pos (by omega) k) (pow_pos hN k)
    exact mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast hUpper) _)
  obtain ⟨r, hr, W', hWsub, hCard, hLarge'⟩ :=
    extract_normalized_finite_powered_block N k a σ C η L W
      hN hk hL.le hDenom hLarge
  let Q := 2 ^ r * N ^ k
  let V := ((((N ^ k : ℕ) : ℝ) ^ σ * L ^ k /
      (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k)
  have hQ : 0 < Q := mul_pos (pow_pos (by omega) r) (pow_pos hN k)
  have hV : 0 < V := by
    dsimp [V]
    positivity
  have hWideMem : ∀ m ∈ dyadicInterval Q,
      m ∈ Finset.Ioc (N ^ k) (2 ^ k * N ^ k) := by
    intro m hm
    change m ∈ Finset.Ioc Q (2 * Q) at hm
    rw [Finset.mem_Ioc] at hm ⊢
    constructor
    · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left (N ^ k)
        (pow_pos (by omega) r)) hm.1
    · have hrlt : r < k := Finset.mem_range.mp hr
      have hrOne : r + 1 ≤ k := by omega
      have hpow : 2 ^ (r + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hrOne
      have hQtwice : 2 * Q = 2 ^ (r + 1) * N ^ k := by
        dsimp [Q]
        rw [pow_succ]
        ring
      rw [hQtwice] at hm
      exact hm.2.trans (Nat.mul_le_mul_right (N ^ k) hpow)
  have hNorm : ∀ m ∈ dyadicInterval Q,
      ‖normalizedFinitePoweredCoeffs N k a σ C η m‖ ≤ 1 := by
    intro m hm
    have hmWide := hWideMem m hm
    exact norm_normalizedFinitePoweredCoeffs_le_one N k m a σ C η
      hN hσ hC hη hmWide (hCoeff m (by
        have hmData := Finset.mem_Ioc.mp hmWide
        omega))
  have hSep' : IsSeparated 1 W' := fun x hx y hy hxy =>
    hSep x (hWsub hx) y (hWsub hy) hxy
  have hBase' : InBaseInterval H W' := fun x hx => hBase x (hWsub hx)
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  have hMHH' := hMHH Q H V W'
    (normalizedFinitePoweredCoeffs N k a σ C η)
    hQ hH hV hNorm hSep' hBase' (by
      intro t ht
      simpa only [Q, V] using hLarge' t ht)
  refine ⟨C, hC, r, hr, W', hWsub, ?_⟩
  dsimp only
  refine ⟨hCard, hSep', hBase', ?_, K, hK, ?_⟩
  · simpa only [Q, V] using hLarge'
  · simpa only [Q, V] using hMHH'

/-- Uniform-constant form of the powered unit-block theorem.  For fixed
`k` and `eta`, both the factorization constant and the MHH constant are
selected before the varying block, ordinate family and height. -/
theorem powered_unit_block_large_values_bound_uniform
    (k : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) (a : ℕ → ℂ) (sigma H L : ℝ) (W : Finset ℝ),
        0 < N → 0 < k → 0 ≤ sigma → 1 ≤ H → 0 < L →
        (∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval H W →
        (∀ t ∈ W,
          L ≤ ‖∑ n ∈ Finset.Ioc N (2 * N),
            a n * (n : ℂ) ^ (-(sigma + I * t))‖) →
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let Q := 2 ^ r * N ^ k
          let V := ((((N ^ k : ℕ) : ℝ) ^ sigma * L ^ k /
              (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ eta)) / k)
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', V ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k a sigma C eta) t‖) ∧
          (W'.card : ℝ) ≤
            K * (1 + (((harmonic Q : ℚ) : ℝ))) *
              ((Q : ℝ) ^ 2 / V ^ 2 +
                H * min ((Q : ℝ) / V ^ 2)
                  ((Q : ℝ) ^ 4 / V ^ 6)) := by
  obtain ⟨C, hC, hCoeff⟩ := finitePowCoeff_bound_uniform k eta heta
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  refine ⟨C, hC, K, hK, ?_⟩
  intro N a sigma H L W hN hk hsigma hH hL ha hSep hBase hLarge
  have hDenom : 0 < C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ eta := by
    have hUpper : 0 < 2 ^ k * N ^ k :=
      mul_pos (pow_pos (by omega) k) (pow_pos hN k)
    exact mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast hUpper) _)
  obtain ⟨r, hr, W', hWsub, hCard, hLarge'⟩ :=
    extract_normalized_finite_powered_block N k a sigma C eta L W
      hN hk hL.le hDenom hLarge
  let Q := 2 ^ r * N ^ k
  let V := ((((N ^ k : ℕ) : ℝ) ^ sigma * L ^ k /
      (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ eta)) / k)
  have hQ : 0 < Q := mul_pos (pow_pos (by omega) r) (pow_pos hN k)
  have hV : 0 < V := by
    dsimp [V]
    positivity
  have hWideMem : ∀ m ∈ dyadicInterval Q,
      m ∈ Finset.Ioc (N ^ k) (2 ^ k * N ^ k) := by
    intro m hm
    change m ∈ Finset.Ioc Q (2 * Q) at hm
    rw [Finset.mem_Ioc] at hm ⊢
    constructor
    · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left (N ^ k)
        (pow_pos (by omega) r)) hm.1
    · have hrlt : r < k := Finset.mem_range.mp hr
      have hrOne : r + 1 ≤ k := by omega
      have hpow : 2 ^ (r + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hrOne
      have hQtwice : 2 * Q = 2 ^ (r + 1) * N ^ k := by
        dsimp [Q]
        rw [pow_succ]
        ring
      rw [hQtwice] at hm
      exact hm.2.trans (Nat.mul_le_mul_right (N ^ k) hpow)
  have hNorm : ∀ m ∈ dyadicInterval Q,
      ‖normalizedFinitePoweredCoeffs N k a sigma C eta m‖ ≤ 1 := by
    intro m hm
    have hmWide := hWideMem m hm
    exact norm_normalizedFinitePoweredCoeffs_le_one N k m a sigma C eta
      hN hsigma hC heta hmWide (hCoeff N a ha m (by
        have hmData := Finset.mem_Ioc.mp hmWide
        omega))
  have hSep' : IsSeparated 1 W' := fun x hx y hy hxy =>
    hSep x (hWsub hx) y (hWsub hy) hxy
  have hBase' : InBaseInterval H W' := fun x hx => hBase x (hWsub hx)
  have hMHH' := hMHH Q H V W'
    (normalizedFinitePoweredCoeffs N k a sigma C eta)
    hQ hH hV hNorm hSep' hBase' (by
      intro t ht
      simpa only [Q, V] using hLarge' t ht)
  refine ⟨r, hr, W', hWsub, ?_⟩
  dsimp only
  exact ⟨hCard, hSep', hBase', by simpa only [Q, V] using hLarge',
    by simpa only [Q, V] using hMHH'⟩

/-- One factorization constant works simultaneously for every positive power
`k ≤ B`.  This finite-uniform form is required when the power is selected
from a `T`-dependent logarithmic scale inside an epsilon-power proof. -/
theorem powered_unit_block_large_values_bound_bounded_uniform
    (B : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (k N : ℕ) (a : ℕ → ℂ) (sigma H L : ℝ) (W : Finset ℝ),
        0 < k → k ≤ B → 0 < N → 0 ≤ sigma → 1 ≤ H → 0 < L →
        (∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval H W →
        (∀ t ∈ W,
          L ≤ ‖∑ n ∈ Finset.Ioc N (2 * N),
            a n * (n : ℂ) ^ (-(sigma + I * t))‖) →
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let Q := 2 ^ r * N ^ k
          let V := ((((N ^ k : ℕ) : ℝ) ^ sigma * L ^ k /
              (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ eta)) / k)
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', V ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k a sigma C eta) t‖) ∧
          (W'.card : ℝ) ≤
            K * (1 + (((harmonic Q : ℚ) : ℝ))) *
              ((Q : ℝ) ^ 2 / V ^ 2 +
                H * min ((Q : ℝ) / V ^ 2)
                  ((Q : ℝ) ^ 4 / V ^ 6)) := by
  have hEach : ∀ k : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ) (a : ℕ → ℂ),
        (∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) →
        ∀ m : ℕ, 0 < m →
          ‖finitePowCoeff N k a m‖ ≤ c * (m : ℝ) ^ eta :=
    fun k => finitePowCoeff_bound_uniform k eta heta
  choose c hc hCoeff using hEach
  let C : ℝ := 1 + ∑ k ∈ Finset.range (B + 1), c k
  have hC : 0 < C := by
    dsimp only [C]
    have hsum : 0 ≤ ∑ k ∈ Finset.range (B + 1), c k := by
      exact Finset.sum_nonneg fun k _ => (hc k).le
    linarith
  have hCOne : 1 ≤ C := by
    dsimp only [C]
    have hsum : 0 ≤ ∑ k ∈ Finset.range (B + 1), c k :=
      Finset.sum_nonneg fun k _ => (hc k).le
    linarith
  have hcC : ∀ {k : ℕ}, k ≤ B → c k ≤ C := by
    intro k hkB
    have hkMem : k ∈ Finset.range (B + 1) := Finset.mem_range.mpr (by omega)
    have hsingle : c k ≤ ∑ j ∈ Finset.range (B + 1), c j :=
      Finset.single_le_sum (fun j _ => (hc j).le) hkMem
    dsimp only [C]
    linarith
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  refine ⟨C, hCOne, K, hK, ?_⟩
  intro k N a sigma H L W hk hkB hN hsigma hH hL ha hSep hBase hLarge
  have hCoeffC : ∀ m : ℕ, 0 < m →
      ‖finitePowCoeff N k a m‖ ≤ C * (m : ℝ) ^ eta := by
    intro m hm
    exact (hCoeff k N a ha m hm).trans
      (mul_le_mul_of_nonneg_right (hcC hkB) (Real.rpow_nonneg (by positivity) _))
  have hDenom : 0 < C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ eta := by
    have hUpper : 0 < 2 ^ k * N ^ k :=
      mul_pos (pow_pos (by omega) k) (pow_pos hN k)
    exact mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast hUpper) _)
  obtain ⟨r, hr, W', hWsub, hCard, hLarge'⟩ :=
    extract_normalized_finite_powered_block N k a sigma C eta L W
      hN hk hL.le hDenom hLarge
  let Q := 2 ^ r * N ^ k
  let V := ((((N ^ k : ℕ) : ℝ) ^ sigma * L ^ k /
      (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ eta)) / k)
  have hQ : 0 < Q := mul_pos (pow_pos (by omega) r) (pow_pos hN k)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hWideMem : ∀ m ∈ dyadicInterval Q,
      m ∈ Finset.Ioc (N ^ k) (2 ^ k * N ^ k) := by
    intro m hm
    change m ∈ Finset.Ioc Q (2 * Q) at hm
    rw [Finset.mem_Ioc] at hm ⊢
    constructor
    · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left (N ^ k)
        (pow_pos (by omega) r)) hm.1
    · have hrlt : r < k := Finset.mem_range.mp hr
      have hrOne : r + 1 ≤ k := by omega
      have hpow : 2 ^ (r + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hrOne
      have hQtwice : 2 * Q = 2 ^ (r + 1) * N ^ k := by
        dsimp only [Q]
        rw [pow_succ]
        ring
      rw [hQtwice] at hm
      exact hm.2.trans (Nat.mul_le_mul_right (N ^ k) hpow)
  have hNorm : ∀ m ∈ dyadicInterval Q,
      ‖normalizedFinitePoweredCoeffs N k a sigma C eta m‖ ≤ 1 := by
    intro m hm
    have hmWide := hWideMem m hm
    exact norm_normalizedFinitePoweredCoeffs_le_one N k m a sigma C eta
      hN hsigma hC heta hmWide (hCoeffC m (by
        have hmData := Finset.mem_Ioc.mp hmWide
        omega))
  have hSep' : IsSeparated 1 W' := fun x hx y hy hxy =>
    hSep x (hWsub hx) y (hWsub hy) hxy
  have hBase' : InBaseInterval H W' := fun x hx => hBase x (hWsub hx)
  have hMHH' := hMHH Q H V W'
    (normalizedFinitePoweredCoeffs N k a sigma C eta)
    hQ hH hV hNorm hSep' hBase' (by
      intro t ht
      simpa only [Q, V] using hLarge' t ht)
  refine ⟨r, hr, W', hWsub, ?_⟩
  dsimp only
  exact ⟨hCard, hSep', hBase', by simpa only [Q, V] using hLarge',
    by simpa only [Q, V] using hMHH'⟩

/-- The powered MHH application for the actual sharp zeta--Möbius detector
block, with arbitrary mollifier cutoff `X`.  The base detector coefficients
are first divided by their proved divisor-bound normalization; hence this
theorem applies in particular to the cutoff `⌊T^(δ₂/2)⌋₊` returned by the
finite Type-I/Type-II dichotomy. -/
theorem powered_actual_sharpMollified_block_large_values_bound
    (A X N k : ℕ) (σ H L η₀ C₀ : ℝ) (W : Finset ℝ)
    (hN : 0 < N) (hk : 0 < k) (hσ : 0 ≤ σ) (hH : 1 ≤ H)
    (hL : 0 < L) (hη₀ : 0 ≤ η₀) (hC₀ : 0 < C₀)
    (hCoeff : ∀ n : ℕ, 0 < n →
      ‖sharpMollifiedCoeff A X n‖ ≤ C₀ * (n : ℝ) ^ η₀)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval H W)
    (hLarge : ∀ t ∈ W,
      L ≤ ‖dirichletPoly N (sharpMollifiedLineCoeff A X σ) t‖) :
    ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, 0 < C ∧
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let D := C₀ * (2 * N : ℝ) ^ η₀ * (N : ℝ) ^ (-σ)
          let Q := 2 ^ r * N ^ k
          let V := (((L / D) ^ k /
              (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k)
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', V ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k
                (normalizedSharpMollifiedLineCoeff A X N σ η₀ C₀)
                0 C η) t‖) ∧
          ∃ K : ℝ, 0 < K ∧
            (W'.card : ℝ) ≤
              K * (1 + (((harmonic Q : ℚ) : ℝ))) *
                ((Q : ℝ) ^ 2 / V ^ 2 +
                  H * min ((Q : ℝ) / V ^ 2)
                    ((Q : ℝ) ^ 4 / V ^ 6)) := by
  intro η hη
  let D : ℝ := C₀ * (2 * N : ℝ) ^ η₀ * (N : ℝ) ^ (-σ)
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : 0 < D := by
    dsimp [D]
    positivity
  let a : ℕ → ℂ := normalizedSharpMollifiedLineCoeff A X N σ η₀ C₀
  have ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1 := by
    intro n hn
    exact norm_normalizedSharpMollifiedLineCoeff_le_one
      A X N n σ η₀ C₀ hN hσ hη₀ hC₀ hCoeff hn
  have hSeries : ∀ t ∈ W,
      L / D ≤ ‖∑ n ∈ Finset.Ioc N (2 * N),
        a n * (n : ℂ) ^ (-(0 + I * t))‖ := by
    intro t ht
    have hEq :
        ∑ n ∈ Finset.Ioc N (2 * N),
            a n * (n : ℂ) ^ (-(0 + I * t)) =
          dirichletPoly N (normalizedSharpMollifiedLineCoeff
            A X N σ η₀ C₀) t := by
      unfold dirichletPoly dyadicInterval
      apply Finset.sum_congr rfl
      intro n _
      simp only [a, zero_add]
      congr 2
      ring
    rw [hEq, dirichletPoly_normalizedSharpMollifiedLineCoeff,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    exact div_le_div_of_nonneg_right (hLarge t ht) hD.le
  have hPowered := powered_unit_block_large_values_bound
    N k a 0 H (L / D) W hN hk (by norm_num) hH (div_pos hL hD)
    ha hSep hBase hSeries η hη
  simpa only [a, D, Real.rpow_zero, one_mul] using hPowered

/-- Unconditional coefficient package for the actual-`X` powered Type-II
application.  The only hypotheses are the finite witness data and ordinary
range conditions; the sharp detector coefficient estimate is discharged by
`sharpMollifiedCoeff_bound`. -/
theorem actual_typeII_powered_mhh_native
    (A X N k : ℕ) (σ H L : ℝ) (W : Finset ℝ)
    (hN : 0 < N) (hk : 0 < k) (hσ : 0 ≤ σ) (hH : 1 ≤ H)
    (hL : 0 < L) (hSep : IsSeparated 1 W)
    (hBase : InBaseInterval H W)
    (hLarge : ∀ t ∈ W,
      L ≤ ‖dirichletPoly N (sharpMollifiedLineCoeff A X σ) t‖) :
    ∀ η₀ : ℝ, 0 < η₀ →
      ∃ C₀ : ℝ, 0 < C₀ ∧
        ∀ η : ℝ, 0 < η →
          ∃ C : ℝ, 0 < C ∧
            ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
              let D := C₀ * (2 * N : ℝ) ^ η₀ * (N : ℝ) ^ (-σ)
              let Q := 2 ^ r * N ^ k
              let V := (((L / D) ^ k /
                  (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k)
              (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
              IsSeparated 1 W' ∧ InBaseInterval H W' ∧
              (∀ t ∈ W', V ≤
                ‖dirichletPoly Q
                  (normalizedFinitePoweredCoeffs N k
                    (normalizedSharpMollifiedLineCoeff A X N σ η₀ C₀)
                    0 C η) t‖) ∧
              ∃ K : ℝ, 0 < K ∧
                (W'.card : ℝ) ≤
                  K * (1 + (((harmonic Q : ℚ) : ℝ))) *
                    ((Q : ℝ) ^ 2 / V ^ 2 +
                      H * min ((Q : ℝ) / V ^ 2)
                        ((Q : ℝ) ^ 4 / V ^ 6)) := by
  intro η₀ hη₀
  obtain ⟨C₀, hC₀, hCoeff⟩ := sharpMollifiedCoeff_bound η₀ hη₀
  refine ⟨C₀, hC₀, ?_⟩
  exact powered_actual_sharpMollified_block_large_values_bound
    A X N k σ H L η₀ C₀ W hN hk hσ hH hL hη₀.le hC₀
      (fun n hn => hCoeff A X n hn) hSep hBase hLarge

/-- Uniform-constant form of the actual sharp-detector Type-II estimate.
For fixed powering and epsilon parameters all analytic constants are chosen
before the cutoff, dyadic scale, line, height, threshold, or witness family.
This quantifier order is required by the final epsilon-power argument. -/
theorem actual_typeII_powered_mhh_uniform_native
    (k : ℕ) (η₀ η : ℝ) (hη₀ : 0 < η₀) (hη : 0 < η) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (A X N : ℕ) (σ H L : ℝ) (W : Finset ℝ),
        0 < N → 0 < k → 0 ≤ σ → 1 ≤ H → 0 < L →
        IsSeparated 1 W → InBaseInterval H W →
        (∀ t ∈ W,
          L ≤ ‖dirichletPoly N (sharpMollifiedLineCoeff A X σ) t‖) →
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let D := C₀ * (2 * N : ℝ) ^ η₀ * (N : ℝ) ^ (-σ)
          let Q := 2 ^ r * N ^ k
          let V := (((L / D) ^ k /
              (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k)
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', V ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k
                (normalizedSharpMollifiedLineCoeff A X N σ η₀ C₀)
                0 C η) t‖) ∧
          (W'.card : ℝ) ≤
            K * (1 + (((harmonic Q : ℚ) : ℝ))) *
              ((Q : ℝ) ^ 2 / V ^ 2 +
                H * min ((Q : ℝ) / V ^ 2)
                  ((Q : ℝ) ^ 4 / V ^ 6)) := by
  obtain ⟨C₀, hC₀, hCoeff⟩ := sharpMollifiedCoeff_bound η₀ hη₀
  obtain ⟨C, hC, K, hK, hPowered⟩ :=
    powered_unit_block_large_values_bound_uniform k η hη
  refine ⟨C₀, hC₀, C, hC, K, hK, ?_⟩
  intro A X N σ H L W hN hk hσ hH hL hSep hBase hLarge
  let D : ℝ := C₀ * (2 * N : ℝ) ^ η₀ * (N : ℝ) ^ (-σ)
  let a : ℕ → ℂ := normalizedSharpMollifiedLineCoeff A X N σ η₀ C₀
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1 := by
    intro n hn
    exact norm_normalizedSharpMollifiedLineCoeff_le_one
      A X N n σ η₀ C₀ hN hσ hη₀.le hC₀
        (fun m hm => hCoeff A X m hm) hn
  have hSeries : ∀ t ∈ W,
      L / D ≤ ‖∑ n ∈ Finset.Ioc N (2 * N),
        a n * (n : ℂ) ^ (-(0 + I * t))‖ := by
    intro t ht
    have hEq :
        ∑ n ∈ Finset.Ioc N (2 * N),
            a n * (n : ℂ) ^ (-(0 + I * t)) =
          dirichletPoly N
            (normalizedSharpMollifiedLineCoeff A X N σ η₀ C₀) t := by
      unfold dirichletPoly dyadicInterval
      apply Finset.sum_congr rfl
      intro n _
      simp only [a, zero_add]
      congr 2
      ring
    rw [hEq, dirichletPoly_normalizedSharpMollifiedLineCoeff,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    exact div_le_div_of_nonneg_right (hLarge t ht) hD.le
  obtain ⟨r, hr, W', hW', hCard, hSep', hBase', hLarge', hBound⟩ :=
    hPowered N a 0 H (L / D) W hN hk (by norm_num) hH
      (div_pos hL hD) ha hSep hBase hSeries
  refine ⟨r, hr, W', hW', ?_⟩
  simpa only [D, a, Real.rpow_zero, one_mul] using
    And.intro hCard (And.intro hSep' (And.intro hBase'
      (And.intro hLarge' hBound)))

/-- Bounded-power uniform form for the actual sharp zeta--Möbius detector.
All constants precede the `T`-dependent power selected by the endpoint scale
reduction. -/
theorem actual_typeII_powered_mhh_bounded_uniform_native
    (B : ℕ) (η₀ η : ℝ) (hη₀ : 0 < η₀) (hη : 0 < η) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (k A X N : ℕ) (σ H L : ℝ) (W : Finset ℝ),
        0 < k → k ≤ B → 0 < N → 0 ≤ σ → 1 ≤ H → 0 < L →
        IsSeparated 1 W → InBaseInterval H W →
        (∀ t ∈ W,
          L ≤ ‖dirichletPoly N (sharpMollifiedLineCoeff A X σ) t‖) →
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let D := C₀ * (2 * N : ℝ) ^ η₀ * (N : ℝ) ^ (-σ)
          let Q := 2 ^ r * N ^ k
          let V := (((L / D) ^ k /
              (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k)
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', V ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k
                (normalizedSharpMollifiedLineCoeff A X N σ η₀ C₀)
                0 C η) t‖) ∧
          (W'.card : ℝ) ≤
            K * (1 + (((harmonic Q : ℚ) : ℝ))) *
              ((Q : ℝ) ^ 2 / V ^ 2 +
                H * min ((Q : ℝ) / V ^ 2)
                  ((Q : ℝ) ^ 4 / V ^ 6)) := by
  obtain ⟨Craw, hCraw, hCoeffRaw⟩ := sharpMollifiedCoeff_bound η₀ hη₀
  let C₀ : ℝ := max 1 Craw
  have hC₀One : 1 ≤ C₀ := le_max_left _ _
  have hCrawC₀ : Craw ≤ C₀ := le_max_right _ _
  have hC₀ : 0 < C₀ := zero_lt_one.trans_le hC₀One
  have hCoeff : ∀ (A X n : ℕ), 0 < n →
      ‖sharpMollifiedCoeff A X n‖ ≤ C₀ * (n : ℝ) ^ η₀ := by
    intro A X n hn
    exact (hCoeffRaw A X n hn).trans
      (mul_le_mul_of_nonneg_right hCrawC₀ (Real.rpow_nonneg (by positivity) _))
  obtain ⟨C, hC, K, hK, hPowered⟩ :=
    powered_unit_block_large_values_bound_bounded_uniform B η hη
  refine ⟨C₀, hC₀One, C, hC, K, hK, ?_⟩
  intro k A X N σ H L W hk hkB hN hσ hH hL hSep hBase hLarge
  let D : ℝ := C₀ * (2 * N : ℝ) ^ η₀ * (N : ℝ) ^ (-σ)
  let a : ℕ → ℂ := normalizedSharpMollifiedLineCoeff A X N σ η₀ C₀
  have hD : 0 < D := by dsimp only [D]; positivity
  have ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1 := by
    intro n hn
    exact norm_normalizedSharpMollifiedLineCoeff_le_one
      A X N n σ η₀ C₀ hN hσ hη₀.le hC₀
        (fun m hm => hCoeff A X m hm) hn
  have hSeries : ∀ t ∈ W,
      L / D ≤ ‖∑ n ∈ Finset.Ioc N (2 * N),
        a n * (n : ℂ) ^ (-(0 + I * t))‖ := by
    intro t ht
    have hEq :
        ∑ n ∈ Finset.Ioc N (2 * N),
            a n * (n : ℂ) ^ (-(0 + I * t)) =
          dirichletPoly N a t := by
      unfold dirichletPoly dyadicInterval
      apply Finset.sum_congr rfl
      intro n _
      simp only [zero_add]
      congr 2
      ring
    rw [hEq]
    change L / D ≤
      ‖dirichletPoly N
        (normalizedSharpMollifiedLineCoeff A X N σ η₀ C₀) t‖
    rw [dirichletPoly_normalizedSharpMollifiedLineCoeff,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    exact div_le_div_of_nonneg_right (hLarge t ht) hD.le
  obtain ⟨r, hr, W', hW', hCard, hSep', hBase', hLarge', hBound⟩ :=
    hPowered k N a 0 H (L / D) W hk hkB hN (by norm_num) hH
      (div_pos hL hD) ha hSep hBase hSeries
  refine ⟨r, hr, W', hW', ?_⟩
  simpa only [D, a, Real.rpow_zero, one_mul] using
    And.intro hCard (And.intro hSep' (And.intro hBase'
      (And.intro hLarge' hBound)))

/-- One already extracted zeta block may be raised to any fixed positive
power, normalized, pigeonholed to one ordinary dyadic block, and fed into the
full finite MHH estimate. -/
theorem powered_sharp_block_large_values_bound
    (A N k : ℕ) (σ H L : ℝ) (W : Finset ℝ)
    (hN : 0 < N) (hk : 0 < k) (hσ : 0 ≤ σ) (hH : 1 ≤ H)
    (hL : 0 < L) (hSep : IsSeparated 1 W) (hBase : InBaseInterval H W)
    (hLarge : ∀ t ∈ W,
      L ≤ ‖dirichletPoly N (sharpMollifiedLineCoeff A 1 σ) t‖) :
    ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, 0 < C ∧
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let Q := 2 ^ r * N ^ k
          let V := ((((N ^ k : ℕ) : ℝ) ^ σ * L ^ k /
              (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k)
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', V ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k
                (sharpMollifiedCoeff A 1) σ C η) t‖) ∧
          ∃ K : ℝ, 0 < K ∧
            (W'.card : ℝ) ≤
              K * (1 + (((harmonic Q : ℚ) : ℝ))) *
                ((Q : ℝ) ^ 2 / V ^ 2 +
                  H * min ((Q : ℝ) / V ^ 2)
                    ((Q : ℝ) ^ 4 / V ^ 6)) := by
  intro η hη
  let a : ℕ → ℂ := sharpMollifiedCoeff A 1
  have ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1 := by
    intro n _
    exact norm_sharpMollifiedCoeff_one_le_one A n
  obtain ⟨C, hC, hCoeff⟩ := finitePowCoeff_bound N k a ha η hη
  have hDenom : 0 < C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η := by
    have hUpper : 0 < 2 ^ k * N ^ k :=
      mul_pos (pow_pos (by omega) k) (pow_pos hN k)
    exact mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast hUpper) _)
  have hSeries : ∀ t ∈ W, L ≤ ‖∑ n ∈ Finset.Ioc N (2 * N),
      a n * (n : ℂ) ^ (-(σ + I * t))‖ := by
    intro t ht
    simpa only [a, dirichletPoly_sharpMollifiedLineCoeff_eq] using hLarge t ht
  obtain ⟨r, hr, W', hWsub, hCard, hLarge'⟩ :=
    extract_normalized_finite_powered_block N k a σ C η L W
      hN hk hL.le hDenom hSeries
  let Q := 2 ^ r * N ^ k
  let V := ((((N ^ k : ℕ) : ℝ) ^ σ * L ^ k /
      (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k)
  have hQ : 0 < Q := mul_pos (pow_pos (by omega) r) (pow_pos hN k)
  have hV : 0 < V := by
    dsimp [V]
    positivity
  have hWideMem : ∀ m ∈ dyadicInterval Q,
      m ∈ Finset.Ioc (N ^ k) (2 ^ k * N ^ k) := by
    intro m hm
    change m ∈ Finset.Ioc Q (2 * Q) at hm
    rw [Finset.mem_Ioc] at hm ⊢
    constructor
    · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left (N ^ k)
        (pow_pos (by omega) r)) hm.1
    · have hrlt : r < k := Finset.mem_range.mp hr
      have hrOne : r + 1 ≤ k := by omega
      have hpow : 2 ^ (r + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hrOne
      have hQtwice : 2 * Q = 2 ^ (r + 1) * N ^ k := by
        dsimp [Q]
        rw [pow_succ]
        ring
      have hmUpper := hm.2
      rw [hQtwice] at hmUpper
      exact hmUpper.trans (Nat.mul_le_mul_right (N ^ k) hpow)
  have hNorm : ∀ m ∈ dyadicInterval Q,
      ‖normalizedFinitePoweredCoeffs N k a σ C η m‖ ≤ 1 := by
    intro m hm
    have hmWide := hWideMem m hm
    exact norm_normalizedFinitePoweredCoeffs_le_one N k m a σ C η
      hN hσ hC hη hmWide (hCoeff m (by
        have hmData := Finset.mem_Ioc.mp hmWide
        omega))
  have hSep' : IsSeparated 1 W' := fun x hx y hy hxy =>
    hSep x (hWsub hx) y (hWsub hy) hxy
  have hBase' : InBaseInterval H W' := fun x hx => hBase x (hWsub hx)
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  have hMHH' := hMHH Q H V W'
    (normalizedFinitePoweredCoeffs N k a σ C η)
    hQ hH hV hNorm hSep' hBase' (by
      intro t ht
      simpa only [Q, V, a] using hLarge' t ht)
  refine ⟨C, hC, r, hr, W', hWsub, ?_⟩
  dsimp only
  refine ⟨hCard, hSep', hBase', ?_, K, hK, ?_⟩
  · simpa only [Q, V, a] using hLarge'
  · simpa only [Q, V, a] using hMHH'

end RiemannZeta.GuthMaynard
