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
