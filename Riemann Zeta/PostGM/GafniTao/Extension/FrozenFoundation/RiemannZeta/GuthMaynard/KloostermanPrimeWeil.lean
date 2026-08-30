import RiemannZeta.GuthMaynard.KloostermanEquationEight
import RiemannZeta.GuthMaynard.KloostermanPrime
import RiemannZeta.GuthMaynard.PowerSumSpectral

/-!
# Prime Kloosterman Weil bound from the Harcos curve

This module completes the spectral step in Harcos's proof: the exact curve
count and its uniform high-extension estimate bound the power sums of the two
local roots, and the finite power-sum spectral lemma forces both roots onto
the circle of radius `sqrt p`.
-/

namespace RiemannZeta.GuthMaynard

open scoped BigOperators

open Finset

noncomputable section

theorem natSqrt_even_primePower (p n : ℕ) :
    Nat.sqrt (p ^ (2 * n)) = p ^ n := by
  rw [show p ^ (2 * n) = (p ^ n) ^ 2 by
    rw [← pow_mul]
    congr 1
    omega]
  exact Nat.sqrt_eq' _

theorem eventually_kloostermanCurve_large
    (p : ℕ) [Fact p.Prime] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      100 * (2 * p + 1) * (Nat.sqrt (p ^ (2 * n)) + 1) <
        p ^ (2 * n) := by
  have hp1 : 1 < p := (show p.Prime from Fact.out).one_lt
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt (200 * (2 * p + 1)) hp1
  refine ⟨n₀, fun n hn => ?_⟩
  rw [natSqrt_even_primePower]
  have hpowmono : p ^ n₀ ≤ p ^ n := Nat.pow_le_pow_right
    (show 0 < p from (show p.Prime from Fact.out).pos) hn
  have hconst : 200 * (2 * p + 1) < p ^ n := hn₀.trans_le hpowmono
  have hpownz : 0 < p ^ n := pow_pos (show 0 < p from
    (show p.Prime from Fact.out).pos) n
  have hone : 1 ≤ p ^ n := hpownz
  calc
    100 * (2 * p + 1) * (p ^ n + 1)
        ≤ 200 * (2 * p + 1) * p ^ n := by nlinarith
    _ < p ^ n * p ^ n := Nat.mul_lt_mul_of_pos_right hconst hpownz
    _ = p ^ (2 * n) := by rw [← pow_add]; congr 1; omega

/-- The `KloostermanRootIndex` definition used by the source-facing construction in `KloostermanPrimeWeil`. -/
abbrev KloostermanRootIndex (p : ℕ) :=
  {m : ZMod p // m ≠ 0} × Bool

/-- The `normalizedKloostermanSquaredRoot` definition used by the source-facing construction in `KloostermanPrimeWeil`. -/
noncomputable def normalizedKloostermanSquaredRoot
    (p : ℕ) [NeZero p] (c : ZMod p)
    (x : KloostermanRootIndex p) : ℂ :=
  let root := if x.2 then
    kloostermanAlpha p x.1.1 (x.1.1 * c)
  else
    kloostermanBeta p x.1.1 (x.1.1 * c)
  root ^ 2 / (p : ℂ)

theorem sum_normalizedKloostermanSquaredRoot_pow
    (p n : ℕ) [NeZero p] (c : ZMod p) :
    ∑ x : KloostermanRootIndex p,
        normalizedKloostermanSquaredRoot p c x ^ n =
      (∑ m : {m : ZMod p // m ≠ 0},
        (kloostermanAlpha p m.1 (m.1 * c) ^ (2 * n) +
          kloostermanBeta p m.1 (m.1 * c) ^ (2 * n))) /
        (p : ℂ) ^ n := by
  rw [Fintype.sum_prod_type]
  simp only [normalizedKloostermanSquaredRoot, Fintype.sum_bool, if_pos,
    Bool.false_eq_true, if_false, div_pow, ← pow_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  rw [add_div]

theorem norm_natCast_sub_natCast_eq_intAbs (a b : ℕ) :
    ‖(a : ℂ) - (b : ℂ)‖ =
      ((|(a : ℤ) - (b : ℤ)| : ℤ) : ℝ) := by
  change ‖((a : ℤ) : ℂ) - ((b : ℤ) : ℂ)‖ = _
  rw [← Int.cast_sub, Complex.norm_intCast, ← Int.cast_abs]

theorem normalizedKloostermanSquaredRoot_powerSum_eventually
    (p : ℕ) [NeZero p] [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ‖∑ x : KloostermanRootIndex p,
          normalizedKloostermanSquaredRoot p c x ^ n‖ ≤
        (160 * (2 * p + 1) + 2 : ℝ) := by
  obtain ⟨n₁, hn₁⟩ := eventually_kloostermanCurve_large p
  refine ⟨max n₁ 1, fun n hn => ?_⟩
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := (le_max_right n₁ 1).trans hn
  have hlarge := hn₁ n hn1
  have hcurve := kloostermanCurve_defect_high_extension
    p (2 * n) hpodd c hc (by omega) hlarge
  rw [← card_quadraticArtinCurve_eq_hyperelliptic p (2 * n) c] at hcurve
  have heq := harcosEquationThree_normalized p (2 * n) hpodd c hc (by omega)
  let q := p ^ (2 * n)
  let card := Nat.card (QuadraticArtinCurvePoints p
    (algebraMap (ZMod p) (GaloisField p (2 * n)) c))
  let S : ℂ := ∑ m : {m : ZMod p // m ≠ 0},
    (kloostermanAlpha p m.1 (m.1 * c) ^ (2 * n) +
      kloostermanBeta p m.1 (m.1 * c) ^ (2 * n))
  have hS : S = (q : ℂ) - (card : ℂ) - 1 := by
    dsimp [S, q, card]
    linear_combination -heq
  have hcurve' : |(card : ℤ) - (q : ℤ)| <
      (80 * (2 * p + 1) * (p ^ n + 1) + 1 : ℕ) := by
    simpa [card, q, natSqrt_even_primePower] using hcurve
  have hcurveR : ((|(card : ℤ) - (q : ℤ)| : ℤ) : ℝ) <
      (80 * (2 * p + 1) * (p ^ n + 1) + 1 : ℕ) := by
    exact_mod_cast hcurve'
  rw [Int.cast_abs, Int.cast_sub] at hcurveR
  push_cast at hcurveR
  have hSnorm : ‖S‖ ≤
      (160 * (2 * p + 1) + 2 : ℝ) * p ^ n := by
    rw [hS]
    apply le_of_lt
    calc
      ‖(q : ℂ) - (card : ℂ) - 1‖
          ≤ ‖(q : ℂ) - (card : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ((|(q : ℤ) - (card : ℤ)| : ℤ) : ℝ) + 1 := by
        rw [norm_natCast_sub_natCast_eq_intAbs]
        simp
      _ = ((|(card : ℤ) - (q : ℤ)| : ℤ) : ℝ) + 1 := by
        rw [abs_sub_comm]
      _ < (80 * (2 * p + 1) * (p ^ n + 1) + 1 : ℕ) + 1 := by
        push_cast
        nlinarith [hcurveR]
      _ ≤ (160 * (2 * p + 1) + 2 : ℝ) * p ^ n := by
        have hpown : (1 : ℝ) ≤ p ^ n := by
          exact_mod_cast (show 1 ≤ p ^ n from
            (pow_pos (show 0 < p from (show p.Prime from Fact.out).pos) n))
        push_cast
        nlinarith
  rw [sum_normalizedKloostermanSquaredRoot_pow]
  rw [norm_div, norm_pow, Complex.norm_natCast]
  have hpownpos : (0 : ℝ) < (p : ℝ) ^ n := by
    exact pow_pos (by exact_mod_cast (show 0 < p from
      (show p.Prime from Fact.out).pos)) n
  exact (div_le_iff₀ hpownpos).2 hSnorm

theorem normalizedKloostermanSquaredRoot_norm_le_one
    (p : ℕ) [NeZero p] [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) (x : KloostermanRootIndex p) :
    ‖normalizedKloostermanSquaredRoot p c x‖ ≤ 1 := by
  obtain ⟨n₀, hpower⟩ :=
    normalizedKloostermanSquaredRoot_powerSum_eventually p hpodd c hc
  apply norm_le_one_of_power_sums_eventually
    (normalizedKloostermanSquaredRoot p c)
    (160 * (2 * p + 1) + 2 : ℝ) (by
      have hp0 : (0 : ℝ) ≤ p := by positivity
      nlinarith) n₀ hpower x

theorem kloostermanAlpha_norm_sq_le_prime
    (p : ℕ) [NeZero p] [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) (m : {m : ZMod p // m ≠ 0}) :
    ‖kloostermanAlpha p m.1 (m.1 * c)‖ ^ 2 ≤ p := by
  have h := normalizedKloostermanSquaredRoot_norm_le_one
    p hpodd c hc (m, true)
  change ‖kloostermanAlpha p m.1 (m.1 * c) ^ 2 / (p : ℂ)‖ ≤ 1 at h
  rw [norm_div, norm_pow, Complex.norm_natCast] at h
  exact (div_le_one (by exact_mod_cast (show 0 < p from
    (show p.Prime from Fact.out).pos))).mp h

theorem kloostermanBeta_norm_sq_le_prime
    (p : ℕ) [NeZero p] [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) (m : {m : ZMod p // m ≠ 0}) :
    ‖kloostermanBeta p m.1 (m.1 * c)‖ ^ 2 ≤ p := by
  have h := normalizedKloostermanSquaredRoot_norm_le_one
    p hpodd c hc (m, false)
  change ‖kloostermanBeta p m.1 (m.1 * c) ^ 2 / (p : ℂ)‖ ≤ 1 at h
  rw [norm_div, norm_pow, Complex.norm_natCast] at h
  exact (div_le_one (by exact_mod_cast (show 0 < p from
    (show p.Prime from Fact.out).pos))).mp h

theorem kloostermanAlpha_norm_eq_sqrt_prime
    (p : ℕ) [NeZero p] [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) (m : {m : ZMod p // m ≠ 0}) :
    ‖kloostermanAlpha p m.1 (m.1 * c)‖ = Real.sqrt p := by
  let A := kloostermanAlpha p m.1 (m.1 * c)
  let B := kloostermanBeta p m.1 (m.1 * c)
  have hAsq : ‖A‖ ^ 2 ≤ (p : ℝ) :=
    kloostermanAlpha_norm_sq_le_prime p hpodd c hc m
  have hBsq : ‖B‖ ^ 2 ≤ (p : ℝ) :=
    kloostermanBeta_norm_sq_le_prime p hpodd c hc m
  have hpR : (0 : ℝ) < p := by exact_mod_cast
    (show 0 < p from (show p.Prime from Fact.out).pos)
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt hpR.le
  have hA : ‖A‖ ≤ Real.sqrt p :=
    (sq_le_sq₀ (norm_nonneg A) (Real.sqrt_nonneg _)).mp (by
      rw [hsqrtSq]
      exact hAsq)
  have hB : ‖B‖ ≤ Real.sqrt p :=
    (sq_le_sq₀ (norm_nonneg B) (Real.sqrt_nonneg _)).mp (by
      rw [hsqrtSq]
      exact hBsq)
  have hAB : ‖A‖ * ‖B‖ = (p : ℝ) := by
    rw [← norm_mul]
    simpa [A, B] using congrArg norm
      (kloostermanAlpha_mul_beta p m.1 (m.1 * c))
  have hp_le : (p : ℝ) ≤ ‖A‖ * Real.sqrt p := by
    calc
      (p : ℝ) = ‖A‖ * ‖B‖ := hAB.symm
      _ ≤ ‖A‖ * Real.sqrt p :=
        mul_le_mul_of_nonneg_left hB (norm_nonneg A)
  have hsqrt_le : Real.sqrt p ≤ ‖A‖ := by
    have hmul : Real.sqrt p * Real.sqrt p ≤ ‖A‖ * Real.sqrt p := by
      rw [show Real.sqrt p * Real.sqrt p = (p : ℝ) by
        rw [← pow_two]
        exact hsqrtSq]
      exact hp_le
    exact le_of_mul_le_mul_right hmul (Real.sqrt_pos.2 hpR)
  exact le_antisymm hA hsqrt_le

theorem kloostermanBeta_norm_eq_sqrt_prime
    (p : ℕ) [NeZero p] [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) (m : {m : ZMod p // m ≠ 0}) :
    ‖kloostermanBeta p m.1 (m.1 * c)‖ = Real.sqrt p := by
  let A := kloostermanAlpha p m.1 (m.1 * c)
  let B := kloostermanBeta p m.1 (m.1 * c)
  have hA := kloostermanAlpha_norm_eq_sqrt_prime p hpodd c hc m
  have hAB : ‖A‖ * ‖B‖ = (p : ℝ) := by
    rw [← norm_mul]
    simpa [A, B] using congrArg norm
      (kloostermanAlpha_mul_beta p m.1 (m.1 * c))
  have hsqrtpos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 (by
    exact_mod_cast (show 0 < p from (show p.Prime from Fact.out).pos))
  rw [show ‖A‖ = Real.sqrt p by simpa [A] using hA] at hAB
  have hsqrtSq : Real.sqrt (p : ℝ) * Real.sqrt p = p := by
    rw [← pow_two]
    exact Real.sq_sqrt (by
      exact_mod_cast (show 0 ≤ p from Nat.zero_le p))
  apply (mul_left_cancel₀ hsqrtpos.ne')
  rw [hAB, hsqrtSq]

theorem kloostermanSumZMod_prime_normalized_weil
    (p : ℕ) [NeZero p] [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) :
    ‖kloostermanSumZMod p 1 c‖ ≤ 2 * Real.sqrt p := by
  let m : {m : ZMod p // m ≠ 0} := ⟨1, one_ne_zero⟩
  have hA := kloostermanAlpha_norm_eq_sqrt_prime p hpodd c hc m
  have hB := kloostermanBeta_norm_eq_sqrt_prime p hpodd c hc m
  have hadd := kloostermanAlpha_add_beta p (1 : ZMod p) c
  rw [show (1 : ZMod p) * c = c by simp] at hA hB
  calc
    ‖kloostermanSumZMod p 1 c‖ =
        ‖-(kloostermanAlpha p 1 c + kloostermanBeta p 1 c)‖ := by
          simp [hadd]
    _ = ‖kloostermanAlpha p 1 c + kloostermanBeta p 1 c‖ := norm_neg _
    _ ≤ ‖kloostermanAlpha p 1 c‖ + ‖kloostermanBeta p 1 c‖ := norm_add_le _ _
    _ = 2 * Real.sqrt p := by rw [hA, hB]; ring

theorem kloostermanSumZMod_two_bound (A B : ZMod 2) :
    ‖kloostermanSumZMod 2 A B‖ ≤ 2 * Real.sqrt 2 := by
  unfold kloostermanSumZMod
  calc
    ‖∑ d : (ZMod 2)ˣ,
        ZMod.stdAddChar
          (A * (d : ZMod 2) + B * (↑(d⁻¹) : ZMod 2))‖
        ≤ ∑ d : (ZMod 2)ˣ,
            ‖ZMod.stdAddChar
              (A * (d : ZMod 2) + B * (↑(d⁻¹) : ZMod 2))‖ := norm_sum_le _ _
    _ = 1 := by
      simp only [AddChar.norm_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
      norm_num [ZMod.card_units_eq_totient]
    _ ≤ 2 * Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg (2 : ℝ)]

/-- Prime-modulus nondegenerate Weil bound, including characteristic two. -/
theorem kloostermanSumZMod_prime_weil
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (A B : ZMod p) (hA : A ≠ 0) (hB : B ≠ 0) :
    ‖kloostermanSumZMod p A B‖ ≤ 2 * Real.sqrt p := by
  rcases (show p.Prime from Fact.out).eq_two_or_odd' with rfl | hpodd
  · exact kloostermanSumZMod_two_bound A B
  · rw [kloostermanSumZMod_prime_eq_normalized p A B hA]
    exact kloostermanSumZMod_prime_normalized_weil p hpodd (A * B)
      (mul_ne_zero hA hB)

end

end RiemannZeta.GuthMaynard
