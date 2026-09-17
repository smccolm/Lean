import Tao2026.SmoothNumberSaddleMovingShell

/-!
# Accumulated dyadic loss on the first outer shell

This module strengthens the one-block outer estimate by using the full coarse
CEP dyadic alphabet.  All retained primes remain in the negative-cosine phase
window on the first outer-frequency shell, while their reciprocal mass is of
order `1 / log u`.  Saddle-equation and cutoff estimates turn the resulting
cosine loss into a named scale comparable from below to `u / log u`; this
scale diverges in every critical regime and gives uniform decay of the
physical Perron integrand on the shell.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval Chebyshev

namespace Tao2026

noncomputable section

theorem three_quarters_log_le_log_of_mem_cepDyadicPrimeAlphabet
    {B y : ℕ} {u : ℝ} (hB : 4 ≤ B) (hy : 2 ≤ y)
    (hlogU : 8 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huY : u ≤ Real.sqrt y) {p : TaoBoundedPrime y}
    (hp : p ∈ cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u)) :
    (3 / 4 : ℝ) * Real.log (y : ℝ) ≤ Real.log (p : ℝ) := by
  have hcut := one_sub_two_div_log_mul_log_le_log_cepDyadicCofactorCutoff
    hB hy (by linarith) hBu huY
  have hlogUPos : 0 < Real.log u := by linarith
  have hcoeff : (3 / 4 : ℝ) ≤ 1 - 2 / Real.log u := by
    have hdiv : 2 / Real.log u ≤ (1 / 4 : ℝ) := by
      apply (div_le_iff₀ hlogUPos).mpr
      nlinarith
    linarith
  have hlogY : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hcutPos : (0 : ℝ) < cepDyadicCofactorCutoff y u := by
    have hw := nat_le_cepDyadicCofactorCutoff_of_criticalRange
      (show 1 ≤ y by omega) (by linarith) hBu huY
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < B) hw)
  have hpCut : (cepDyadicCofactorCutoff y u : ℝ) < (p : ℝ) := by
    exact_mod_cast cepDyadicCofactorCutoff_lt_of_mem hp
  calc
    (3 / 4 : ℝ) * Real.log (y : ℝ) ≤
        (1 - 2 / Real.log u) * Real.log (y : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff hlogY
    _ ≤ Real.log (cepDyadicCofactorCutoff y u : ℕ) := hcut
    _ ≤ Real.log (p : ℝ) := Real.log_le_log hcutPos hpCut.le

theorem one_le_cosineLossTerm_of_cepDyadicPrimeAlphabet
    {B y : ℕ} {u t : ℝ} (hB : 4 ≤ B) (hy : 2 ≤ y)
    (hlogU : 8 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huY : u ≤ Real.sqrt y)
    (htLower : Real.pi / Real.log (y : ℝ) ≤ t)
    (htUpper : t ≤ 3 * Real.pi / (2 * Real.log (y : ℝ)))
    {p : TaoBoundedPrime y}
    (hp : p ∈ cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u)) :
    1 ≤ 1 - Real.cos (t * Real.log (p : ℝ)) := by
  have hpData := Nat.mem_primesLE.mp p.2
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpData.2.pos
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogpLower := three_quarters_log_le_log_of_mem_cepDyadicPrimeAlphabet
    hB hy hlogU hBu huY hp
  have hlogpUpper : Real.log (p : ℝ) ≤ Real.log (y : ℝ) :=
    Real.log_le_log hpPos (by exact_mod_cast hpData.1)
  have htPos : 0 < t := lt_of_lt_of_le (by positivity [Real.pi_pos]) htLower
  have hphaseLower : Real.pi / 2 ≤ t * Real.log (p : ℝ) := by
    have hmul := mul_le_mul htLower hlogpLower
      (by positivity) (by positivity [Real.pi_pos])
    field_simp [hlogy.ne'] at hmul
    nlinarith [Real.pi_pos]
  have hphaseUpper : t * Real.log (p : ℝ) ≤ Real.pi + Real.pi / 2 := by
    calc
      t * Real.log (p : ℝ) ≤
          (3 * Real.pi / (2 * Real.log (y : ℝ))) *
            Real.log (y : ℝ) :=
        mul_le_mul htUpper hlogpUpper
          (Real.log_nonneg (by exact_mod_cast hpData.2.one_le))
          (by positivity [Real.pi_pos])
      _ = Real.pi + Real.pi / 2 := by field_simp [hlogy.ne']; ring
  linarith [Real.cos_nonpos_of_pi_div_two_le_of_le hphaseLower hphaseUpper]

theorem cofactor_rpow_div_log_le_sum_rpow_neg_cepDyadicPrimeAlphabet
    {B y : ℕ} {u sigma : ℝ} (hB : 4 ≤ B) (hy : 2 ≤ y)
    (hlogU : 8 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huY : u ≤ Real.sqrt y)
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta (n : ℝ) ∧
        Chebyshev.theta (n : ℝ) ≤ (5 / 4 : ℝ) * n)
    (hsigma1 : sigma ≤ 1) :
    (cepDyadicCofactorCutoff y u : ℝ) ^ (1 - sigma) /
        (16 * Real.log 2 * Real.log u) ≤
      ∑ p ∈ cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u),
        ((p : ℕ) : ℝ) ^ (-sigma) := by
  have hmass := one_div_log_le_sum_inv_cepDyadicPrimeAlphabet_of_criticalRange
    hB hy (by linarith) hBu huY hpnt
  have hpowNonneg : 0 ≤
      (cepDyadicCofactorCutoff y u : ℝ) ^ (1 - sigma) := by positivity
  calc
    (cepDyadicCofactorCutoff y u : ℝ) ^ (1 - sigma) /
        (16 * Real.log 2 * Real.log u) =
      (cepDyadicCofactorCutoff y u : ℝ) ^ (1 - sigma) *
        (1 / (16 * Real.log 2 * Real.log u)) := by ring
    _ ≤ (cepDyadicCofactorCutoff y u : ℝ) ^ (1 - sigma) *
        (∑ p ∈ cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u),
          (((p : ℕ) : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left hmass hpowNonneg
    _ = ∑ p ∈ cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u),
        (cepDyadicCofactorCutoff y u : ℝ) ^ (1 - sigma) *
          (((p : ℕ) : ℝ)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u),
        ((p : ℕ) : ℝ) ^ (-sigma) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := Nat.mem_primesLE.mp p.2
      have hpPos : (0 : ℝ) < (p : ℕ) := by exact_mod_cast hpData.2.pos
      have hcutPos : (0 : ℝ) < cepDyadicCofactorCutoff y u := by
        have hw := nat_le_cepDyadicCofactorCutoff_of_criticalRange
          (show 1 ≤ y by omega) (by linarith) hBu huY
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < B) hw)
      have hpCut : (cepDyadicCofactorCutoff y u : ℝ) ≤ ((p : ℕ) : ℝ) := by
        exact_mod_cast (cepDyadicCofactorCutoff_lt_of_mem hp).le
      have hrpow : (cepDyadicCofactorCutoff y u : ℝ) ^ (1 - sigma) ≤
          ((p : ℕ) : ℝ) ^ (1 - sigma) :=
        Real.rpow_le_rpow hcutPos.le hpCut (sub_nonneg.mpr hsigma1)
      calc
        (cepDyadicCofactorCutoff y u : ℝ) ^ (1 - sigma) *
            (((p : ℕ) : ℝ)⁻¹) ≤
          ((p : ℕ) : ℝ) ^ (1 - sigma) * (((p : ℕ) : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right hrpow (by positivity)
        _ = ((p : ℕ) : ℝ) ^ (-sigma) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hpPos]
          congr 1
          ring

theorem firstOuterMultiShell_cosineLoss_lower
    {B y : ℕ} {u sigma t : ℝ} (hB : 4 ≤ B) (hy : 2 ≤ y)
    (hlogU : 8 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huY : u ≤ Real.sqrt y)
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta (n : ℝ) ∧
        Chebyshev.theta (n : ℝ) ≤ (5 / 4 : ℝ) * n)
    (hsigma1 : sigma ≤ 1)
    (htLower : Real.pi / Real.log (y : ℝ) ≤ t)
    (htUpper : t ≤ 3 * Real.pi / (2 * Real.log (y : ℝ))) :
    (cepDyadicCofactorCutoff y u : ℝ) ^ (1 - sigma) /
        (16 * Real.log 2 * Real.log u) ≤
      smoothSaddleCosineLoss y sigma t := by
  let P := cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u)
  let S := (Finset.Icc 2 y).filter Nat.Prime
  let f : ℕ → ℝ := fun p =>
    (p : ℝ) ^ (-sigma) * (1 - Real.cos (t * Real.log (p : ℝ)))
  have hweight :=
    cofactor_rpow_div_log_le_sum_rpow_neg_cepDyadicPrimeAlphabet
      hB hy hlogU hBu huY hpnt hsigma1
  have hphase (p : TaoBoundedPrime y) (hp : p ∈ P) :
      1 ≤ 1 - Real.cos (t * Real.log ((p : ℕ) : ℝ)) := by
    exact one_le_cosineLossTerm_of_cepDyadicPrimeAlphabet
      hB hy hlogU hBu huY htLower htUpper hp
  have hsubset : P.image (fun p : TaoBoundedPrime y => (p : ℕ)) ⊆ S := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hqData := Nat.mem_primesLE.mp q.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqData.2.two_le, hqData.1⟩, hqData.2⟩
  calc
    (cepDyadicCofactorCutoff y u : ℝ) ^ (1 - sigma) /
        (16 * Real.log 2 * Real.log u) ≤
      ∑ p ∈ P, ((p : ℕ) : ℝ) ^ (-sigma) := by
        simpa only [P] using hweight
    _ ≤ ∑ p ∈ P, f (p : ℕ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact le_mul_of_one_le_right (by positivity) (hphase p hp)
    _ = ∑ p ∈ P.image (fun p : TaoBoundedPrime y => (p : ℕ)), f p := by
      rw [Finset.sum_image]
      intro p hp q hq hpq
      exact Subtype.ext hpq
    _ ≤ ∑ p ∈ S, f p := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p hp hnot => mul_nonneg (by positivity)
          (by linarith [Real.cos_le_one (t * Real.log (p : ℝ))]))
    _ = smoothSaddleCosineLoss y sigma t := rfl

theorem smoothSaddlePrimeTerm_le_five_mul_rpow_mul_log_div
    {y p : ℕ} (hp : p.Prime) (hpy : p ≤ y)
    {sigma : ℝ} (hsigmaHalf : (1 / 2 : ℝ) ≤ sigma)
    (hsigmaOne : sigma ≤ 1) :
    smoothSaddlePrimeTerm p sigma ≤
      5 * (y : ℝ) ^ (1 - sigma) * (Real.log (p : ℝ) / (p : ℝ)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpPos : (0 : ℝ) < p := by positivity
  have hyPos : (0 : ℝ) < y := by
    exact_mod_cast (lt_of_lt_of_le hp.pos hpy)
  have hsigmaPos : 0 < sigma := by linarith
  have hsqrtTwo : (5 / 4 : ℝ) ≤ Real.sqrt 2 := by
    have hsqrt0 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hpowLower : (5 / 4 : ℝ) ≤ (p : ℝ) ^ sigma := by
    calc
      (5 / 4 : ℝ) ≤ Real.sqrt 2 := hsqrtTwo
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
      _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp2) (by norm_num)
      _ ≤ (p : ℝ) ^ sigma :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ p by omega))
          hsigmaHalf
  have hdenPos : 0 < (p : ℝ) ^ sigma - 1 :=
    smoothSaddle_denominator_pos hp2 hsigmaPos
  have hpowDen : (p : ℝ) ^ sigma ≤ 5 * ((p : ℝ) ^ sigma - 1) := by
    nlinarith
  have hlogNonneg : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hterm : smoothSaddlePrimeTerm p sigma ≤
      5 * (Real.log (p : ℝ) / (p : ℝ) ^ sigma) := by
    unfold smoothSaddlePrimeTerm
    calc
      Real.log (p : ℝ) / ((p : ℝ) ^ sigma - 1) ≤
          (5 * Real.log (p : ℝ)) / (p : ℝ) ^ sigma := by
        rw [div_le_div_iff₀ hdenPos (Real.rpow_pos_of_pos hpPos sigma)]
        nlinarith [mul_le_mul_of_nonneg_left hpowDen hlogNonneg]
      _ = 5 * (Real.log (p : ℝ) / (p : ℝ) ^ sigma) := by ring
  have hpPow : (p : ℝ) ^ (1 - sigma) ≤ (y : ℝ) ^ (1 - sigma) :=
    Real.rpow_le_rpow hpPos.le (by exact_mod_cast hpy)
      (sub_nonneg.mpr hsigmaOne)
  calc
    smoothSaddlePrimeTerm p sigma ≤
        5 * (Real.log (p : ℝ) / (p : ℝ) ^ sigma) := hterm
    _ = 5 * (p : ℝ) ^ (1 - sigma) *
        (Real.log (p : ℝ) / (p : ℝ)) := by
      have hinv : ((p : ℝ) ^ sigma)⁻¹ = (p : ℝ) ^ (-sigma) := by
        exact (Real.rpow_neg hpPos.le sigma).symm
      have hrpow : (p : ℝ) ^ (1 - sigma) * (p : ℝ) ^ (-1 : ℝ) =
          (p : ℝ) ^ (-sigma) := by
        rw [← Real.rpow_add hpPos]
        congr 1
        ring
      rw [div_eq_mul_inv, div_eq_mul_inv, hinv, ← Real.rpow_neg_one, ← hrpow]
      ring
    _ ≤ 5 * (y : ℝ) ^ (1 - sigma) *
        (Real.log (p : ℝ) / (p : ℝ)) := by
      gcongr
    _ = 5 * (y : ℝ) ^ (1 - sigma) *
        (Real.log (p : ℝ) / (p : ℝ)) := rfl

theorem smoothSaddlePhiOne_le_five_mul_rpow_mul_weightedPrimeLog
    {y : ℕ} (hy : 2 ≤ y) {sigma : ℝ}
    (hsigmaHalf : (1 / 2 : ℝ) ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    smoothSaddlePhiOne y sigma ≤
      5 * (y : ℝ) ^ (1 - sigma) *
        (Real.log 4 * (2 + Real.log (y : ℝ))) := by
  calc
    smoothSaddlePhiOne y sigma ≤
        ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
          5 * (y : ℝ) ^ (1 - sigma) *
            (Real.log (p : ℝ) / (p : ℝ)) := by
      unfold smoothSaddlePhiOne
      exact Finset.sum_le_sum fun p hp =>
        smoothSaddlePrimeTerm_le_five_mul_rpow_mul_log_div
          (Finset.mem_filter.mp hp).2
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
          hsigmaHalf hsigmaOne
    _ = 5 * (y : ℝ) ^ (1 - sigma) * weightedPrimeLogSum y := by
      rw [weightedPrimeLogSum, Finset.mul_sum]
    _ ≤ 5 * (y : ℝ) ^ (1 - sigma) *
        (Real.log 4 * (2 + Real.log (y : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (weightedPrimeLogSum_le y (by omega))
        (by positivity)

theorem rankinRatio_div_fifteen_log_four_le_saddle_rpow
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hlogY : 1 ≤ Real.log (y : ℝ))
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaOne : smoothSaddlePoint X y ≤ 1) :
    smoothRankinRatio X y / (15 * Real.log 4) ≤
      (y : ℝ) ^ (1 - smoothSaddlePoint X y) := by
  let sigma := smoothSaddlePoint X y
  let A := (y : ℝ) ^ (1 - sigma)
  let L := Real.log (y : ℝ)
  let K := Real.log 4
  have hphi := smoothSaddlePhiOne_le_five_mul_rpow_mul_weightedPrimeLog
    hy hsigmaHalf hsigmaOne
  rw [smoothSaddlePhiOne_smoothSaddlePoint hX hy] at hphi
  have hXL : Real.log (X : ℝ) = smoothRankinRatio X y * L := by
    simpa only [L] using (smoothRankinRatio_mul_log hy).symm
  have hK : 0 < K := by dsimp only [K]; positivity
  have hL : 0 < L := by dsimp only [L]; linarith
  have hfactor : K * (2 + L) ≤ 3 * K * L := by
    nlinarith [hK.le]
  have hphi' : smoothRankinRatio X y * L ≤ (15 * K * A) * L := by
    rw [← hXL]
    calc
      Real.log (X : ℝ) ≤ 5 * A * (K * (2 + L)) := by
        simpa only [sigma, A, L, K] using hphi
      _ ≤ 5 * A * (3 * K * L) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = (15 * K * A) * L := by ring
  have hu : smoothRankinRatio X y ≤ 15 * K * A :=
    le_of_mul_le_mul_right hphi' hL
  apply (div_le_iff₀ (mul_pos (by norm_num) hK)).mpr
  simpa [A, K, sigma, mul_comm, mul_left_comm, mul_assoc] using hu

theorem exp_neg_sixteen_mul_rpow_le_cofactor_rpow
    {B y : ℕ} {u sigma : ℝ} (hB : 4 ≤ B) (hy : 2 ≤ y)
    (hlogU : 8 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huY : u ≤ Real.sqrt y) (hsigmaOne : sigma ≤ 1)
    (hdisplacement : 1 - sigma ≤
      8 * Real.log u / Real.log (y : ℝ)) :
    Real.exp (-16) * (y : ℝ) ^ (1 - sigma) ≤
      (cepDyadicCofactorCutoff y u : ℝ) ^ (1 - sigma) := by
  let e := 1 - sigma
  let L := Real.log (y : ℝ)
  let U := Real.log u
  let w := cepDyadicCofactorCutoff y u
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hU : 0 < U := by dsimp only [U]; linarith
  have hwNat := nat_le_cepDyadicCofactorCutoff_of_criticalRange
    (show 1 ≤ y by omega) (by linarith) hBu huY
  have hw : 0 < (w : ℝ) := by
    dsimp only [w]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < B) hwNat)
  have hlogW : (1 - 2 / U) * L ≤ Real.log (w : ℝ) := by
    simpa only [U, L, w] using
      one_sub_two_div_log_mul_log_le_log_cepDyadicCofactorCutoff
        hB hy (by linarith) hBu huY
  have hdisp : e * L ≤ 8 * U := by
    apply (le_div_iff₀ hL).mp
    simpa only [e, L, U] using hdisplacement
  have hbudget : 2 * e * L ≤ 16 * U := by nlinarith
  have hpenalty : 2 * e * L / U ≤ 16 :=
    (div_le_iff₀ hU).mpr (by nlinarith)
  have hleft : -16 + e * L ≤ e * ((1 - 2 / U) * L) := by
    have hid : e * ((1 - 2 / U) * L) = e * L - 2 * e * L / U := by
      ring
    rw [hid]
    linarith
  have hright : e * ((1 - 2 / U) * L) ≤ e * Real.log (w : ℝ) :=
    mul_le_mul_of_nonneg_left hlogW he
  have hexponent : -16 + e * L ≤ e * Real.log (w : ℝ) :=
    hleft.trans hright
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (y : ℝ)),
    Real.rpow_def_of_pos hw]
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by
    simpa [e, L, w, mul_comm] using hexponent)

theorem firstOuterMultiShell_cosineLoss_lower_at_saddle
    {B X y : ℕ} {t : ℝ} (hB : 4 ≤ B) (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hlogY : 1 ≤ Real.log (y : ℝ))
    (hlogU : 8 ≤ Real.log (smoothRankinRatio X y))
    (hBu : (B : ℝ) ≤ smoothRankinRatio X y)
    (huY : smoothRankinRatio X y ≤ Real.sqrt y)
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta (n : ℝ) ∧
        Chebyshev.theta (n : ℝ) ≤ (5 / 4 : ℝ) * n)
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaOne : smoothSaddlePoint X y ≤ 1)
    (hdisplacement : 1 - smoothSaddlePoint X y ≤
      8 * Real.log (smoothRankinRatio X y) / Real.log (y : ℝ))
    (htLower : Real.pi / Real.log (y : ℝ) ≤ t)
    (htUpper : t ≤ 3 * Real.pi / (2 * Real.log (y : ℝ))) :
    (Real.exp (-16) *
        (smoothRankinRatio X y / (15 * Real.log 4))) /
        (16 * Real.log 2 * Real.log (smoothRankinRatio X y)) ≤
      smoothSaddleCosineLoss y (smoothSaddlePoint X y) t := by
  let u := smoothRankinRatio X y
  let sigma := smoothSaddlePoint X y
  let w := cepDyadicCofactorCutoff y u
  have hrankin := rankinRatio_div_fifteen_log_four_le_saddle_rpow
    hX hy hlogY hsigmaHalf hsigmaOne
  have hcofactor := exp_neg_sixteen_mul_rpow_le_cofactor_rpow
    hB hy hlogU hBu huY hsigmaOne hdisplacement
  have hmulti := firstOuterMultiShell_cosineLoss_lower
    hB hy hlogU hBu huY hpnt hsigmaOne htLower htUpper
  have hleft : Real.exp (-16) * (u / (15 * Real.log 4)) ≤
      (w : ℝ) ^ (1 - sigma) := by
    calc
      Real.exp (-16) * (u / (15 * Real.log 4)) ≤
          Real.exp (-16) * (y : ℝ) ^ (1 - sigma) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [u, sigma] using hrankin) (Real.exp_pos _).le
      _ ≤ (w : ℝ) ^ (1 - sigma) := by
        simpa only [u, sigma, w] using hcofactor
  have hden : 0 < 16 * Real.log 2 * Real.log u := by
    have : 0 < Real.log u := by dsimp only [u]; linarith
    positivity
  calc
    (Real.exp (-16) *
        (smoothRankinRatio X y / (15 * Real.log 4))) /
        (16 * Real.log 2 * Real.log (smoothRankinRatio X y)) =
      (Real.exp (-16) * (u / (15 * Real.log 4))) /
        (16 * Real.log 2 * Real.log u) := by rfl
    _ ≤ (w : ℝ) ^ (1 - sigma) /
        (16 * Real.log 2 * Real.log u) := by
      exact (div_le_div_iff₀ hden hden).mpr (by nlinarith)
    _ ≤ smoothSaddleCosineLoss y sigma t := by
      simpa only [u, sigma, w] using hmulti

noncomputable def smoothSaddleFirstOuterLossScale (X y : ℕ) : ℝ :=
  (Real.exp (-16) *
      (smoothRankinRatio X y / (15 * Real.log 4))) /
    (16 * Real.log 2 * Real.log (smoothRankinRatio X y))

theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleFirstOuterLossScale_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleFirstOuterLossScale (X n) (y n))
      atTop atTop := by
  let c : ℝ := Real.exp (-16) / (15 * Real.log 4 * Real.log 2)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hbase := hregime.tendsto_rankinRatio_div_sixteen_log_atTop hα
  have hscaled := hbase.const_mul_atTop hc
  apply hscaled.congr'
  filter_upwards [hregime.tendsto_rankinRatio_atTop hα |>.eventually
    (eventually_gt_atTop (1 : ℝ))] with n hu
  have hlogu : Real.log (smoothRankinRatio (X n) (y n)) ≠ 0 :=
    (Real.log_pos hu).ne'
  unfold smoothSaddleFirstOuterLossScale
  dsimp only [c]
  field_simp [hlogu, (Real.log_pos (by norm_num : (1 : ℝ) < 4)).ne',
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

theorem IsTaoCriticalSmoothRegime.eventually_smoothSaddleFirstOuterLossScale_le_cosineLoss
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      Real.pi / Real.log (y n : ℝ) ≤ t →
      t ≤ 3 * Real.pi / (2 * Real.log (y n : ℝ)) →
      smoothSaddleFirstOuterLossScale (X n) (y n) ≤
        smoothSaddleCosineLoss (y n) (smoothSaddlePoint (X n) (y n)) t := by
  obtain ⟨B, hB, hpnt⟩ := exists_chebyshevTheta_quarter_threshold
  have huTop := hregime.tendsto_rankinRatio_atTop hα
  have hloguTop := Real.tendsto_log_atTop.comp huTop
  have hsaddleHalf := (hregime.tendsto_smoothSaddlePoint_one hα).eventually
    (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (1 : ℝ)),
    hloguTop.eventually (eventually_ge_atTop (8 : ℝ)),
    huTop.eventually (eventually_ge_atTop (B : ℝ)),
    hregime.eventually_rankinRatio_le_y_rpow_half hα,
    hsaddleHalf,
    hregime.eventually_smoothSaddlePoint_lt_one hα,
    hregime.eventually_one_sub_saddle_lt_eight_log_ratio hα] with
      n hX hy hlogY hlogU hBu huY hsigmaHalf hsigmaOne hdisplacement
  intro t htLower htUpper
  have huSqrt : smoothRankinRatio (X n) (y n) ≤ Real.sqrt (y n) := by
    simpa only [Real.sqrt_eq_rpow] using huY
  unfold smoothSaddleFirstOuterLossScale
  exact firstOuterMultiShell_cosineLoss_lower_at_saddle
    hB hX hy hlogY hlogU hBu huSqrt hpnt hsigmaHalf.le hsigmaOne.le
    hdisplacement.le htLower htUpper

theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleFirstOuterEnvelope_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      Real.exp (-(smoothSaddleFirstOuterLossScale (X n) (y n) / 96)))
      atTop (𝓝 0) := by
  have hscale :=
    hregime.tendsto_smoothSaddleFirstOuterLossScale_atTop hα
  have hdiv := hscale.atTop_div_const (by norm_num : (0 : ℝ) < 96)
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hdiv)

theorem IsTaoCriticalSmoothRegime.eventually_norm_smoothSaddlePerronLineIntegrand_le_firstOuterEnvelope
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      Real.pi / Real.log (y n : ℝ) ≤ t →
      t ≤ 3 * Real.pi / (2 * Real.log (y n : ℝ)) →
      ‖smoothSaddlePerronLineIntegrand (X n) (y n) t‖ ≤
        Real.exp (-(smoothSaddleFirstOuterLossScale (X n) (y n) / 96)) := by
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hregime.eventually_smoothSaddleFirstOuterLossScale_le_cosineLoss hα] with
      n hX hy hsigma hloss
  intro t htLower htUpper
  calc
    ‖smoothSaddlePerronLineIntegrand (X n) (y n) t‖ ≤
        Real.exp (-(smoothSaddleCosineLoss (y n)
          (smoothSaddlePoint (X n) (y n)) t / 96)) :=
      norm_smoothSaddlePerronLineIntegrand_le_cosineLoss
        hX hy hsigma.le t
    _ ≤ Real.exp (-(smoothSaddleFirstOuterLossScale (X n) (y n) / 96)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hloss t htLower htUpper]

end

end Tao2026
